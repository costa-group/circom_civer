use constraint_list::ConstraintList;
use constraint_writers::debug_writer::DebugWriter;
use constraint_writers::ConstraintExporter;
use program_structure::constants::UsefulConstants;
use program_structure::error_definition::ReportCollection;
use std::time::Duration;
use std::collections::{HashMap, HashSet, LinkedList};
type Signal = usize;
type Constraint = circom_algebra::algebra::Constraint<usize>;
type Substitution = circom_algebra::algebra::Substitution<usize>;
type Range = std::ops::Range<usize>;
use std::time::Instant;
use circom_algebra::num_bigint::BigInt;
use solvers_interface::*;


use program_structure::ast::Expression;

pub type FastSubAccess = HashMap<usize, Substitution>;





#[derive(Default)]
pub struct VerificationTree {
    pub constraints: Vec<Constraint>,
    pub node_id: usize,
    pub template_name: String,
    pub pretty_template_name: String,
    /// Each specification travels with the name of the tag it comes from, so a
    /// result can be attributed to a tag. It is dropped when the problem for the
    /// solver is built: the translators only need the condition.
    pub specification_preconditions: Vec<(String, Expression)>,
    pub specification_intermediates: Vec<(String, Expression)>,
    pub specification_postconditions: Vec<(String, Expression)>,
    pub number_signals: usize,
    pub number_inputs: usize, 
    pub number_outputs: usize,
    pub initial_signal: usize,
    pub subcomponents: LinkedList<VerificationTree>,
    pub is_custom: bool,
}

impl VerificationTree {
    pub fn template_name(&self)-> &String{
        &self.template_name
    }

    pub fn pretty_template_name(&self)-> &String{
        &self.pretty_template_name
    }

    pub fn node_id(&self)-> usize{
        self.node_id
    }

    pub fn subcomponents(&self)-> &LinkedList<VerificationTree>{
        &self.subcomponents
    }

    pub fn constraints(&self)-> &Vec<Constraint>{
        &self.constraints
    }

    pub fn number_signals(&self)-> usize{
        self.number_signals
    }

    pub fn number_inputs(&self)-> usize{
        self.number_inputs
    }

    pub fn number_outputs(&self)-> usize{
        self.number_outputs
    }

    pub fn initial_signal(&self)-> usize{
        self.initial_signal
    }

    pub fn is_custom(&self)-> bool{
        self.is_custom
    }

    /// One labelled obligation per tagged signal that this template must prove:
    /// its outputs and its intermediates. Exactly the same set the combined
    /// query proves, only split and labelled so that a result can be attributed
    /// to a single obligation.
    ///
    /// The input tags of the subcomponents are deliberately NOT here: they are
    /// hypotheses, assumed as the left hand side of the implication built by
    /// generate_tags_implications, and discharged by the tag discipline of the
    /// type checker rather than by an SMT query.
    pub fn collect_tag_obligations(&self) -> Vec<TagObligation>{
        let mut obligations = Vec::new();
        for (i, (tag, c)) in self.specification_intermediates.iter().enumerate(){
            obligations.push(TagObligation{
                label: format!("intermediate #{} [{}]", i, tag),
                condition: c.clone(),
            });
        }
        for (i, (tag, c)) in self.specification_postconditions.iter().enumerate(){
            obligations.push(TagObligation{
                label: format!("output #{} [{}]", i, tag),
                condition: c.clone(),
            });
        }
        obligations
    }

    pub fn get_no_postconditions(&self) -> usize{
        self.specification_intermediates.len() + self.specification_postconditions.len() 
    }

    pub fn verify_tree(
        &self, 
        field: &BigInt, 
        config: VerificationConfig,
    ) -> (PossibleResult, PossibleResult, Vec<String>){
        
        let mut tags_implications: Vec<ExecutedImplication> = Vec::new();
        let mut implications_safety: Vec<SafetyImplication> = Vec::new();
        let mut signals: LinkedList<usize> = LinkedList::new(); 
        let mut logs =  Vec::new();
        let mut n_rounds = 0;

        let mut tag_result = PossibleResult::NOSTUDIED;
        let mut safety_result = PossibleResult::NOSTUDIED;

        logs.push(format!("Checking template {}\n", self.pretty_template_name));


        if self.is_custom{
            logs.push(format!("Not checking custom templates. Assuming that they are correct. \n"));
            return (PossibleResult::VERIFIED, PossibleResult::VERIFIED, logs);
        }
        
        for s in 0..self.number_signals{
            signals.push_back(s+self.initial_signal);
        }
        
        let mut to_check_next = Vec::new();
        for subtree in &self.subcomponents{
            let (
                mut new_signals, 
                new_tag_implication, 
                new_implications_safety
            ) = subtree.abstract_subtree();
            signals.append(&mut new_signals);
   
            if new_tag_implication.is_some(){
                tags_implications.push(new_tag_implication.unwrap());
            }
            implications_safety.push(new_implications_safety);

            to_check_next.push(subtree);
        } 


        let mut verification = VerificationProblem{
            template_name: self.pretty_template_name.clone(),
            signals: signals,
            initial_signal: self.initial_signal,
            number_outputs: self.number_outputs,
            number_inputs: self.number_inputs,
            specification_preconditions: conditions(&self.specification_preconditions),
            specification_intermediates: conditions(&self.specification_intermediates),
            specification_postconditions: conditions(&self.specification_postconditions),
            tag_obligations: if config.split_tags{
                self.collect_tag_obligations()
            } else{
                Vec::new()
            },
            constraints: self.constraints.clone(),  
            tags_implications: tags_implications,
            implications_safety: implications_safety,
            field: field.clone(),
            config
        };

        logs.push(format!("Number of signals (i,int,o): {}\n", self.number_signals));
        if config.check_tags{
            logs.push(format!("Number of tagged signals to check: {}\n", self.specification_postconditions.len() + self.specification_intermediates.len()));
            if config.split_tags{
                logs.push(format!("Number of tag obligations to prove one by one: {}\n", verification.tag_obligations.len()));
            }
        }
     
        logs.push(format!("Number of constraints in template: {}\n", self.constraints().len()));
        let inicio = Instant::now();


        let mut complete_result = verification.solve_problem();

        if complete_result.tags_result.is_some(){
            tag_result =  complete_result.tags_result.unwrap();
        }

        if complete_result.safety_result.is_some(){
            safety_result =  complete_result.safety_result.unwrap();
        }

        drop_proven_obligations(&mut verification, &complete_result.tag_obligation_results);

        if tag_result == PossibleResult::VERIFIED{
            verification.config.check_tags = false;
        }

        if safety_result == PossibleResult::VERIFIED{
            verification.config.check_safety = false;
        }
        
        let mut finished_verification = tag_result.finished_verification() && safety_result.finished_verification();
        logs.append(&mut complete_result.logs);


        while !finished_verification && !to_check_next.is_empty(){

            n_rounds += 1;

            let new_components = std::mem::take(&mut to_check_next);
            for subtree in new_components{
                let result_add_components = subtree.add_info_component(&mut verification);
                for aux in result_add_components{
                    to_check_next.push(aux);
                }
            }
            
            logs.push(format!("### Trying to verify adding constraints of the children\n"));

            let mut complete_result = verification.solve_problem();

            if complete_result.tags_result.is_some(){
                tag_result =  complete_result.tags_result.unwrap();
            }

            if complete_result.safety_result.is_some(){
                safety_result =  complete_result.safety_result.unwrap();
            }

            drop_proven_obligations(&mut verification, &complete_result.tag_obligation_results);

            if tag_result == PossibleResult::VERIFIED{
                verification.config.check_tags = false;
            }

            if safety_result == PossibleResult::VERIFIED{
                verification.config.check_safety = false;
            }
            
            finished_verification = tag_result.finished_verification() && safety_result.finished_verification();
            logs.append(&mut complete_result.logs);


        }

        let duration = inicio.elapsed();  
        pretty_print_result(&mut logs, duration, n_rounds, &safety_result, &tag_result);

        (safety_result, tag_result, logs)

    }


    fn add_info_component(&self, verification: &mut VerificationProblem)-> &LinkedList<VerificationTree>{
        for c in &self.constraints{
            verification.constraints.push(c.clone());
        }
        for s in (self.number_inputs + self.number_outputs)..self.number_signals{
            verification.signals.push_back(s+self.initial_signal);
        }
        for subtree_child in &self.subcomponents{
            let (new_signals, new_tag_implication, new_safety_implication) = subtree_child.abstract_subtree();
            for s in new_signals{
                verification.signals.push_back(s);
            }
            if new_tag_implication.is_some(){
                verification.tags_implications.push(new_tag_implication.unwrap());
            }
            verification.implications_safety.push(new_safety_implication);
        }
        &self.subcomponents

    }


    fn abstract_subtree(&self)-> (LinkedList<usize>, Option<ExecutedImplication>, SafetyImplication){
        (   self.generate_io_signals(),
            self.generate_tags_implications(), 
            self.generate_implications_safety()
        )
    }

    fn generate_io_signals(&self)-> LinkedList<usize>{
        let mut signals = LinkedList::new();
        for s in 0..(self.number_inputs+ self.number_outputs){
            signals.push_back(s+self.initial_signal);
        } 
        signals
    }
    
    fn generate_tags_implications(&self)-> Option<ExecutedImplication>{
        let mut left_conditions = Vec::new();
        let mut right_conditions = Vec::new();
        if !self.specification_postconditions.is_empty() {
            for (_tag, prec) in &self.specification_preconditions{
                left_conditions.push(prec.clone());
            }

            for (_tag, post) in &self.specification_postconditions{
                right_conditions.push(post.clone());
            }
            Some(ExecutedImplication{left: left_conditions, right: right_conditions})
        } else{
            None
        }

    }

    fn generate_implications_safety(&self)-> SafetyImplication{
        let mut list_inputs = Vec::new();
        let mut list_outputs = Vec::new();
        for s in 0..self.number_outputs{
            list_outputs.push(self.initial_signal + s);
        }
        for s in 0..self.number_inputs{
            list_inputs.push(self.initial_signal + self.number_outputs + s);
        }
        
        SafetyImplication{
            left: list_inputs, 
            right: list_outputs
        }
    }

    

}

    /// Drops the name of the tag: from here on only the condition is needed.
    fn conditions(specs: &Vec<(String, Expression)>) -> Vec<Expression>{
        specs.iter().map(|(_tag, c)| c.clone()).collect()
    }

    /// In split mode, a later round only has to retry the obligations that are
    /// not proven yet: everything already VERIFIED stays verified when more
    /// information (the constraints of the children) is added.
    fn drop_proven_obligations(
        verification: &mut VerificationProblem,
        results: &Vec<(String, PossibleResult)>,
    ){
        if results.is_empty(){
            return;
        }
        let proven: HashSet<&String> = results.iter()
            .filter(|(_, r)| *r == PossibleResult::VERIFIED)
            .map(|(label, _)| label)
            .collect();
        verification.tag_obligations.retain(|o| !proven.contains(&o.label));
    }

    fn pretty_print_result(logs: &mut Vec<String>, duration: Duration, n_rounds: usize, result_safety: &PossibleResult, result_tags: &PossibleResult){
        logs.push(format!("Verification time per template: {}\n", duration.as_secs_f64()));    
        logs.push(format!("     NUMBER OF ROUNDS: {}\n\n ", n_rounds));
        logs.push(format!("******** VERIFICATION RESULTS ********\n"));

        if result_safety != &PossibleResult::NOSTUDIED{
            logs.push(format!("-----> DETERMINISM: "));
            logs.push(result_safety.result_to_str());
        }

        if result_tags != &PossibleResult::NOSTUDIED{
            logs.push(format!("-----> TAG CORRECTNESS: "));
            logs.push(result_tags.result_to_str());
        }

        logs.push(format!("\n\n"));
    }