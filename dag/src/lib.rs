mod constraint_correctness_analysis;
mod json_porting;
mod map_to_constraint_list;
mod r1cs_porting;
mod sym_porting;
mod witness_producer;
mod tags_checking;

use tags_checking::TemplateVerification;
use circom_algebra::num_bigint::BigInt;
use constraint_list::ConstraintList;
use constraint_writers::debug_writer::DebugWriter;
use constraint_writers::ConstraintExporter;
use program_structure::constants::UsefulConstants;
use program_structure::error_definition::ReportCollection;
use std::collections::{HashMap, HashSet, LinkedList};
use std::time::Instant;
type Signal = usize;
type Constraint = circom_algebra::algebra::Constraint<usize>;
type Substitution = circom_algebra::algebra::Substitution<usize>;
type Range = std::ops::Range<usize>;
use program_structure::ast::Expression;

pub type FastSubAccess = HashMap<usize, Substitution>;
pub type SafetyImplication = (Vec<usize>, Vec<usize>);

#[derive(Clone)]
pub struct ExecutedImplication{
    pub left: Vec<Expression>,
    pub right: Vec<Expression>,
}


#[derive(PartialEq, Eq)] 
pub enum PossibleResult{
    VERIFIED, UNKNOWN, FAILED, NOSTUDIED, NOTHING
} impl PossibleResult {
    fn finished_verification(&self) -> bool{
        self == &PossibleResult::VERIFIED || self == &PossibleResult::NOSTUDIED || self == &PossibleResult::NOTHING || self == &PossibleResult::UNKNOWN
    }
    fn result_to_str(&self)-> String{
        match self{
            &PossibleResult::FAILED => {format!("FAILED -> FOUND COUNTEREXAMPLE\n")}
            &PossibleResult::UNKNOWN => {format!("UNKNOWN -> VERIFICATION TIMEOUT\n")}
            &PossibleResult::NOTHING => {format!("NOTHING TO VERIFY\n")}
            _ => {format!("VERIFIED\n")}
        }
    }
}


#[derive(Default)]
pub struct TreeConstraints {
    constraints: Vec<Constraint>,
    node_id: usize,
    template_name: String,
    pretty_template_name: String,
    preconditions: Vec<Expression>,
    preconditions_intermediates: Vec<Expression>,
    postconditions_intermediates: Vec<Expression>,
    postconditions_outputs: Vec<Expression>,
    facts: Vec<Expression>,
    tags_preconditions: Vec<Expression>,
    tags_postconditions_intermediates: Vec<Expression>,
    tags_postconditions_outputs: Vec<Expression>,
    number_signals: usize,
    number_inputs: usize, 
    number_outputs: usize,
    initial_signal: usize,
    subcomponents: LinkedList<TreeConstraints>,
}

impl TreeConstraints {
    pub fn template_name(&self)-> &String{
        &self.template_name
    }

    pub fn pretty_template_name(&self)-> &String{
        &self.pretty_template_name
    }

    pub fn subcomponents(&self)-> &LinkedList<TreeConstraints>{
        &self.subcomponents
    }

    pub fn constraints(&self)-> &Vec<Constraint>{
        &self.constraints
    }

    pub fn get_no_postconditions(&self) -> usize{
        self.postconditions_intermediates.len() + self.postconditions_outputs.len() 
    }

    pub fn get_no_tags_postconditions(&self) -> usize{
        self.tags_postconditions_intermediates.len() + self.tags_postconditions_outputs.len() 
    }

    fn add_info_component(&self, verification: &mut TemplateVerification)-> Option<&LinkedList<TreeConstraints>>{
        //if self.constraints.len() <= 150{
            for c in &self.constraints{
                verification.constraints.push(c.clone());
            }
            for s in (self.number_inputs + self.number_outputs)..self.number_signals{
                verification.signals.push_back(s+self.initial_signal);
            }
            for subtree_child in &self.subcomponents{
                let (new_signals, new_implication, new_tag_implication, new_safety_implication) = subtree_child.generate_info_subtree();
                for s in new_signals{
                    verification.signals.push_back(s);
                }
                if new_implication.is_some(){
                    verification.implications.push(new_implication.unwrap());
                }
                if new_tag_implication.is_some(){
                    verification.tags_implications.push(new_tag_implication.unwrap());
                }
                verification.implications_safety.push(new_safety_implication);
            }
            Some(&self.subcomponents)
        /* } else{
            println!("Subcomponent has not been considered since it has {} constraints", self.constraints.len());
            None
        }*/
    }

    pub fn check_tags(&self, field: &BigInt, verification_timeout: u64, check_tags: bool, check_postconditions: bool, check_safety: bool, 
        add_tags_info: bool, add_postconditions_info: bool,
    ) -> (PossibleResult, PossibleResult, PossibleResult, Vec<String>){
        let mut implications: Vec<ExecutedImplication> = Vec::new();
        let mut tags_implications: Vec<ExecutedImplication> = Vec::new();

        let mut implications_safety: Vec<SafetyImplication> = Vec::new();

        let mut signals: LinkedList<usize> = LinkedList::new(); 

        let mut logs =  Vec::new();
        
        println!("Checking template {}\n", self.pretty_template_name);
        
        for s in 0..self.number_signals{
            signals.push_back(s+self.initial_signal);
        }
        
        for subtree in &self.subcomponents{
            let (mut new_signals, new_implication, new_tag_implication, new_implications_safety) = subtree.generate_info_subtree();
            signals.append(&mut new_signals);
            if new_implication.is_some(){
                implications.push(new_implication.unwrap());
            }
            if new_tag_implication.is_some(){
                tags_implications.push(new_tag_implication.unwrap());
            }
            implications_safety.push(new_implications_safety)
        }

        let mut postconditions = self.postconditions_outputs.clone();
        for post in self.postconditions_intermediates.clone(){
            postconditions.push(post);
        }

        let mut verification = TemplateVerification::new(
            &self.template_name, 
            signals, 
            self.initial_signal,
            self.number_outputs,
            self.number_inputs,
            self.constraints.clone(), 
            self.preconditions.clone(), 
            self.preconditions_intermediates.clone(),
            self.postconditions_outputs.clone(),
            self.postconditions_intermediates.clone(),
            self.facts.clone(),
            self.tags_preconditions.clone(), 
            self.tags_postconditions_outputs.clone(),
            self.tags_postconditions_intermediates.clone(),
            implications,
            tags_implications,
            implications_safety,
            field,
            verification_timeout,
            check_tags,
            check_postconditions,
            check_safety,
            add_tags_info,
            add_postconditions_info,
        );
        logs.push(format!("Checking template {}\n", self.pretty_template_name));
        logs.push(format!("Number of signals (i,int,o): {}\n", self.number_signals));
        if check_tags{
            logs.push(format!("Number of tagged signals to check: {}\n", self.tags_postconditions_intermediates.len() + self.tags_postconditions_outputs.len()));
        }
        if check_postconditions{
            logs.push(format!("Number of postconditions to check: {}\n", self.postconditions_intermediates.len() + self.postconditions_outputs.len()));
        }        
        logs.push(format!("Number of constraints in template: {}\n", self.constraints().len()));
        let inicio = Instant::now();

        let (mut result_tags, mut result_postconditions, mut result_safety, mut logs_round) = verification.deduce();
        let mut finished_verification = result_tags.finished_verification() &&  result_postconditions.finished_verification() && result_safety.finished_verification();
        logs.append(&mut logs_round);
        if finished_verification{
            let duration = inicio.elapsed();    
            logs.push(format!("Verification time per template: {}\n", duration.as_secs_f64()));    
            logs.push(format!("     NUMBER OF ROUNDS: 0\n\n"));
            logs.push(format!("******** VERIFICATION RESULTS ********\n"));
            if check_tags{
                logs.push(format!("-----> TAGS CHECKING: "));
                logs.push(result_tags.result_to_str());
            }
            if check_postconditions{
                logs.push(format!("-----> POSTCONDITIONS CHECKING: "));
                logs.push(result_postconditions.result_to_str());
            }
            if check_safety{
                logs.push(format!("-----> WEAK SAFETY: "));
                logs.push(result_safety.result_to_str());
            }
            logs.push(format!("\n\n"));
            (result_tags, result_postconditions, result_safety, logs)
        } else if !self.subcomponents.is_empty(){
            let mut to_check_next = Vec::new();
            let mut n_rounds = 1;
            for subtree in &self.subcomponents{
                let result_add_components = subtree.add_info_component(&mut verification);
                if result_add_components.is_some(){
                    for aux in result_add_components.unwrap(){
                        to_check_next.push(aux);
                    }
                }
            }

            if result_tags == PossibleResult::VERIFIED{
                verification.check_tags = false;
            }
            if result_postconditions == PossibleResult::VERIFIED{
                verification.check_postconditions = false;
            }
            if result_safety == PossibleResult::VERIFIED{
                verification.check_safety = false;
            }

            logs.push(format!("### Trying to verify adding constraints of the children\n"));
            (result_tags, result_postconditions, result_safety, logs_round) = verification.deduce();
            finished_verification = result_tags.finished_verification() &&  result_postconditions.finished_verification() && result_safety.finished_verification();
            logs.append(&mut logs_round);
            while !finished_verification && !to_check_next.is_empty(){
                let new_components = std::mem::take(&mut to_check_next);
                n_rounds = n_rounds + 1;
                
                for subtree in &new_components{
                    let result_add_components = subtree.add_info_component(&mut verification);
                    if result_add_components.is_some(){
                        for aux in result_add_components.unwrap(){
                            to_check_next.push(aux);
                        }
                    }
                }

                if result_tags == PossibleResult::VERIFIED{
                    verification.check_tags = false;
                }
                if result_postconditions == PossibleResult::VERIFIED{
                    verification.check_postconditions = false;
                }
                if result_safety == PossibleResult::VERIFIED{
                    verification.check_safety = false;
                }

                logs.push(format!("### Trying to verify adding constraints of the children\n"));
                (result_tags, result_postconditions, result_safety, logs_round) = verification.deduce();
                finished_verification = result_tags.finished_verification() &&  result_postconditions.finished_verification() && result_safety.finished_verification();
                logs.append(&mut logs_round);
            }
            let duration = inicio.elapsed();    
            logs.push(format!("Verification time per template: {}\n", duration.as_secs_f64()));    
            logs.push(format!("     NUMBER OF ROUNDS: {}\n\n ", n_rounds));
            logs.push(format!("******** VERIFICATION RESULTS ********\n"));
            if check_tags{
                logs.push(format!("-----> TAGS CHECKING: "));
                logs.push(result_tags.result_to_str());
            }
            if check_postconditions{
                logs.push(format!("-----> POSTCONDITIONS CHECKING: "));
                logs.push(result_postconditions.result_to_str());
            }
            if check_safety{
                logs.push(format!("-----> WEAK SAFETY: "));
                logs.push(result_safety.result_to_str());
            }
            logs.push(format!("\n\n"));
            (result_tags, result_postconditions, result_safety, logs)
        } else{
            let duration = inicio.elapsed();  
            logs.push(format!("Verification time per template: {}\n", duration.as_secs_f64()));    
            logs.push(format!("     NUMBER OF ROUNDS: 0  \n\n"));
            logs.push(format!("******** VERIFICATION RESULTS ********\n"));
            if check_tags{
                logs.push(format!("-----> TAGS CHECKING: "));
                logs.push(result_tags.result_to_str());
            }
            if check_postconditions{
                logs.push(format!("-----> POSTCONDITIONS CHECKING: "));
                logs.push(result_postconditions.result_to_str());
            }
            if check_safety{
                logs.push(format!("-----> WEAK SAFETY: "));
                logs.push(result_safety.result_to_str());
            }
            logs.push(format!("\n\n"));
            (result_tags, result_postconditions, result_safety, logs)
        }
    }

    fn generate_info_subtree(&self)-> (LinkedList<usize>, Option<ExecutedImplication>, Option<ExecutedImplication>, SafetyImplication){
        (   self.generate_io_signals(),
            self.generate_implications(), 
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
        if self.preconditions_intermediates.is_empty() && !self.tags_postconditions_outputs.is_empty() {
            for prec in &self.preconditions{
                left_conditions.push(prec.clone());
            }
            for prec in &self.tags_preconditions{
                left_conditions.push(prec.clone());
            }
            for post in &self.tags_postconditions_outputs{
                right_conditions.push(post.clone());
            }
            Some(ExecutedImplication{left: left_conditions, right: right_conditions})
        } else{
            None
        }

    }
    fn generate_implications(&self)-> Option<ExecutedImplication>{
        let mut left_conditions = Vec::new();
        let mut right_conditions = Vec::new();
        if self.preconditions_intermediates.is_empty() && !self.postconditions_outputs.is_empty() {
            for prec in &self.preconditions{
                left_conditions.push(prec.clone());
            }
            for prec in &self.tags_preconditions{
                left_conditions.push(prec.clone());
            }
            for post in &self.postconditions_outputs{
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
        (list_inputs, list_outputs)
    }


}

pub struct Tree<'a> {
    dag: &'a DAG,
    pub field: BigInt,
    pub path: String,
    pub offset: usize,
    pub node_id: usize,
    pub signals: Vec<usize>,
    pub forbidden: HashSet<usize>,
    pub id_to_name: HashMap<usize, String>,
    pub constraints: Vec<Constraint>,
    pub preconditions: Vec<Expression>,
    pub preconditions_intermediates: Vec<Expression>,
    pub postconditions_outputs: Vec<Expression>,
    pub postconditions_intermediates: Vec<Expression>,
    pub facts: Vec<Expression>,
    pub tags_preconditions: Vec<Expression>,
    pub tags_postconditions_outputs: Vec<Expression>,
    pub tags_postconditions_intermediates: Vec<Expression>,
}

impl<'a> Tree<'a> {
    pub fn new(dag: &DAG) -> Tree {
        let constants = UsefulConstants::new(&dag.prime);
        let field = constants.get_p().clone();
        let root = dag.get_main().unwrap();
        let node_id = dag.main_id();
        let offset = dag.get_entry().unwrap().in_number;
        let path = dag.get_entry().unwrap().label.clone();
        let constraints = root.constraints.clone();
        let preconditions = root.preconditions.clone();
        let preconditions_intermediates = root.preconditions_intermediates.clone();
        let postconditions_intermediates = root.postconditions_intermediates.clone();
        let postconditions_outputs = root.postconditions_outputs.clone();
        let facts = root.facts.clone();
        let tags_preconditions = root.tags_preconditions.clone();
        let tags_postconditions_intermediates = root.tags_postconditions_intermediates.clone();
        let tags_postconditions_outputs = root.tags_postconditions_outputs.clone();
        let mut id_to_name = HashMap::new();
        let mut signals: Vec<_> = Vec::new();
        let forbidden: HashSet<_> =
            root.forbidden_if_main.iter().cloned().map(|s| s + offset).collect();
        for (name, id) in root.correspondence() {
            if root.is_local_signal(*id) {
                Vec::push(&mut signals, *id + offset);
                HashMap::insert(&mut id_to_name, *id, name.clone());
            }
        }
        signals.sort();
        Tree { field, dag, path, offset, node_id, signals, forbidden, id_to_name, constraints,
            preconditions, preconditions_intermediates, postconditions_intermediates, postconditions_outputs,
            facts,
            tags_preconditions, tags_postconditions_intermediates, tags_postconditions_outputs,
         }   
        }

    pub fn go_to_subtree(current: &'a Tree, edge: &Edge) -> Tree<'a> {
        let field = current.field.clone();
        let dag = current.dag;
        let node_id = edge.goes_to;
        let node = &current.dag.nodes[node_id];
        let path = format!("{}.{}", current.path, edge.label);
        let offset = current.offset + edge.in_number;
        let mut id_to_name = HashMap::new();
        let forbidden = HashSet::with_capacity(0);
        let mut signals: Vec<_> = Vec::new();
        for (name, id) in node.correspondence() {
            if node.is_local_signal(*id) {
                Vec::push(&mut signals, *id + offset);
                HashMap::insert(&mut id_to_name, *id + offset, name.clone());
            }
        }
        signals.sort();
        let constraints: Vec<_> = node
            .constraints
            .iter()
            .filter(|c| !c.is_empty())
            .map(|c| Constraint::apply_offset(c, offset))
            .collect();
        let preconditions: Vec<_> = node
            .preconditions
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();
        let preconditions_intermediates: Vec<_> = node
            .preconditions_intermediates
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();
        let postconditions_intermediates: Vec<_> = node
            .postconditions_intermediates
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();
        let postconditions_outputs: Vec<_> = node
            .postconditions_outputs
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();
        let facts: Vec<_> = node
            .facts
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();
        let tags_preconditions: Vec<_> = node
            .tags_preconditions
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();
        let tags_postconditions_intermediates: Vec<_> = node
            .tags_postconditions_intermediates
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();
        let tags_postconditions_outputs: Vec<_> = node
            .tags_postconditions_outputs
            .iter()
            .map(|c| c.apply_offset(offset))
            .collect();

        
            
        Tree { field, dag, path, offset, node_id, signals, forbidden, id_to_name, constraints,
            preconditions, preconditions_intermediates, postconditions_intermediates, postconditions_outputs,
            facts, 
            tags_preconditions, tags_postconditions_intermediates, tags_postconditions_outputs,
         }
    }

    pub fn get_edges(tree: &'a Tree) -> &'a Vec<Edge> {
        &tree.dag.adjacency[tree.node_id]
    }
}

#[derive(Default)]
pub struct Edge {
    label: String,
    goes_to: usize,
    in_number: usize,
    out_number: usize,
    in_component_number: usize,
    out_component_number: usize
}
impl Edge {
    fn new_entry(id: usize) -> Edge {
        Edge { label: "main".to_string(), goes_to: id, in_number: 0, out_number: 0, in_component_number: 0, out_component_number: 0  }
    }

    pub fn get_goes_to(&self) -> usize {
        self.goes_to
    }

    pub fn get_signal_range(&self) -> Range {
        (self.in_number + 1)..(self.out_number + 1)
    }

    pub fn get_in(&self) -> usize {
        self.in_number
    }

    pub fn get_out(&self) -> usize {
        self.out_number
    }

    pub fn get_in_component(&self) -> usize {
        self.in_component_number
    }

    pub fn get_out_component(&self) -> usize {
        self.out_component_number
    }

    pub fn reach(&self, with_offset: usize) -> usize {
        with_offset + self.in_number
    }

    pub fn get_label(&self) -> &str {
        &self.label
    }
}

#[derive(Default)]
pub struct Node {
    entry: Edge,
    template_name: String,
    pretty_template_name: String,
    parameters: Vec<BigInt>,
    number_of_signals: usize,
    number_of_components: usize,
    intermediates_length: usize,
    public_inputs_length: usize,
    inputs_length: usize,
    outputs_length: usize,
    signal_correspondence: HashMap<String, Signal>,
    ordered_signals: Vec<String>,
    locals: HashSet<usize>,
    reachables: HashSet<usize>, // locals and io of subcomponents
    forbidden_if_main: HashSet<usize>,
    io_signals: Vec<usize>,
    constraints: Vec<Constraint>,
    underscored_signals: Vec<usize>,
    is_parallel: bool,
    has_parallel_sub_cmp: bool,
    is_custom_gate: bool,
    number_of_subcomponents_indexes: usize,
    preconditions: Vec<Expression>,
    preconditions_intermediates: Vec<Expression>,
    postconditions_intermediates: Vec<Expression>,
    postconditions_outputs: Vec<Expression>,
    facts: Vec<Expression>,
    tags_preconditions: Vec<Expression>,
    tags_postconditions_intermediates: Vec<Expression>,
    tags_postconditions_outputs: Vec<Expression>,
}

impl Node {
    fn new(
        id: usize,
        template_name: String,
        pretty_template_name: String,
        parameters: Vec<BigInt>,
        ordered_signals: Vec<String>,
        is_parallel: bool,
        is_custom_gate: bool
    ) -> Node {
        Node {
            template_name, 
            pretty_template_name,
            entry: Edge::new_entry(id),
            parameters,
            number_of_components: 1,
            ordered_signals,
            is_parallel,
            has_parallel_sub_cmp: false,
            is_custom_gate,
            forbidden_if_main: vec![0].into_iter().collect(),
            ..Node::default()
        }
    }

    fn add_input(&mut self, name: String, is_public: bool) {
        let id = self.number_of_signals + 1;
        self.io_signals.push(id);
        self.public_inputs_length += if is_public { 1 } else { 0 };
        self.signal_correspondence.insert(name, id);
        self.locals.insert(id);
        self.reachables.insert(id);
        self.number_of_signals += 1;
        self.entry.out_number += 1;
        self.inputs_length += 1;
        if is_public {
            self.forbidden_if_main.insert(id);
        }
    }

    fn add_output(&mut self, name: String) {
        let id = self.number_of_signals + 1;
        self.io_signals.push(id);
        self.signal_correspondence.insert(name, id);
        self.forbidden_if_main.insert(id);
        self.locals.insert(id);
        self.reachables.insert(id);
        self.number_of_signals += 1;
        self.entry.out_number += 1;
        self.outputs_length += 1;
    }

    fn add_intermediate(&mut self, name: String) {
        let id = self.number_of_signals + 1;
        self.signal_correspondence.insert(name, id);
        self.locals.insert(id);
        self.reachables.insert(id);
        self.number_of_signals += 1;
        self.entry.out_number += 1;
        self.intermediates_length += 1;
    }

    fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint)
    }

    fn add_underscored_signal(&mut self, signal: usize) {
        self.underscored_signals.push(signal)
    }
    
    fn add_precondition(&mut self, prec: Expression) {
        self.preconditions.push(prec)
    }

    fn add_precondition_intermediate(&mut self, prec: Expression) {
        self.preconditions_intermediates.push(prec)
    }


    fn add_postcondition_intermediate(&mut self, post: Expression) {
        self.postconditions_intermediates.push(post)
    }

    fn add_postcondition_output(&mut self, post: Expression) {
        self.postconditions_outputs.push(post)
    }

    fn add_fact(&mut self, fact: Expression) {
        self.facts.push(fact)
    }

    fn add_tag_precondition(&mut self, prec: Expression) {
        self.tags_preconditions.push(prec)
    }

    fn add_tag_postcondition_intermediate(&mut self, post: Expression) {
        self.tags_postconditions_intermediates.push(post)
    }

    fn add_tag_postcondition_output(&mut self, post: Expression) {
        self.tags_postconditions_outputs.push(post)
    }

    fn set_number_of_subcomponents_indexes(&mut self, number_scmp: usize) {
        self.number_of_subcomponents_indexes = number_scmp
    }

    pub fn parameters(&self) -> &Vec<BigInt> {
        &self.parameters
    }

    fn is_local_signal(&self, s: usize) -> bool {
        self.locals.contains(&s)
    }

    fn is_reachable_signal(&self, s: usize) -> bool {
        self.reachables.contains(&s)
    }

    pub fn number_of_signals(&self) -> usize {
        self.number_of_signals
    }

    pub fn correspondence(&self) -> &HashMap<String, usize> {
        &self.signal_correspondence
    }

    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }

    pub fn io_signals(&self) -> &Vec<usize> {
        &self.io_signals
    }

    pub fn get_entry(&self) -> &Edge {
        &self.entry
    }

    pub fn number_of_public_inputs(&self) -> usize {
        self.public_inputs_length
    }

    pub fn number_of_private_inputs(&self) -> usize {
        self.inputs_length - self.public_inputs_length
    }

    pub fn number_of_inputs(&self) -> usize {
        self.inputs_length
    }

    pub fn number_of_outputs(&self) -> usize {
        self.outputs_length
    }

    pub fn number_of_intermediates(&self) -> usize {
        self.intermediates_length
    }

    pub fn has_parallel_sub_cmp(&self) -> bool {
        self.has_parallel_sub_cmp
    }

    pub fn is_custom_gate(&self) -> bool {
        self.is_custom_gate
    }

    pub fn number_of_subcomponents_indexes(&self) -> usize {
        self.number_of_subcomponents_indexes
    }
}

pub struct DAG {
    pub one_signal: usize,
    pub nodes: Vec<Node>,
    pub adjacency: Vec<Vec<Edge>>,
    pub prime: String,
}

impl ConstraintExporter for DAG {
    fn r1cs(&self, out: &str, custom_gates: bool) -> Result<(), ()> {
        DAG::generate_r1cs_output(self, out, custom_gates)
    }

    fn json_constraints(&self, writer: &DebugWriter) -> Result<(), ()> {
        DAG::generate_json_constraints(self, writer)
    }

    fn sym(&self, out: &str) -> Result<(), ()> {
        DAG::generate_sym_output(self, out)
    }
}

impl DAG {
    pub fn new(prime: &String) -> DAG {
        DAG{
            prime : prime.clone(),
            one_signal: 0,
            nodes: Vec::new(),
            adjacency: Vec::new(),
        }
    }

    pub fn add_edge(&mut self, to: usize, label: &str, is_parallel: bool) -> Option<&Edge> {
        if to < self.main_id() {
            // create arrow
            let from = self.main_id();
            let in_num = self.nodes[from].number_of_signals;
            let in_component_num = self.nodes[from].number_of_components;
            let out_num = in_num + self.nodes[to].number_of_signals;
            let out_component_num = in_component_num + self.nodes[to].number_of_components;
            self.nodes[from].number_of_signals += self.nodes[to].number_of_signals;
            self.nodes[from].entry.out_number += self.nodes[to].number_of_signals;
            self.nodes[from].number_of_components += self.nodes[to].number_of_components;
            self.nodes[from].entry.out_component_number += self.nodes[to].number_of_components;
            self.nodes[from].has_parallel_sub_cmp |= self.nodes[to].is_parallel || is_parallel;
            let with = Edge {
                label: label.to_string(),
                goes_to: to,
                in_number: in_num,
                out_number: out_num,
                in_component_number: in_component_num,
                out_component_number: out_component_num,
            };
            // add correspondence to current node
            let mut correspondence = std::mem::take(&mut self.nodes[from].signal_correspondence);
            let mut reachables = std::mem::take(&mut self.nodes[from].reachables);
            for (signal, id) in self.nodes[to].correspondence() {
                if self.nodes[to].is_local_signal(*id) {
                    let concrete_name = format!("{}.{}", label, signal);
                    let concrete_value = with.in_number + *id;
                    correspondence.insert(concrete_name, concrete_value);
                    if *id <= self.nodes[to].inputs_length + self.nodes[to].outputs_length{
                        // in case it is an input/output signal
                        reachables.insert(concrete_value);
                    }
                }
            }
            self.nodes[from].signal_correspondence = correspondence;
            self.nodes[from].reachables = reachables;
            self.nodes[from].has_parallel_sub_cmp |= self.nodes[to].is_parallel;
            self.adjacency[from].push(with);
            self.adjacency[from].last()
        } else {
            Option::None
        }
    }

    pub fn add_node(
        &mut self,
        template_name: String,
        pretty_template_name: String,
        parameters: Vec<BigInt>,
        ordered_signals: Vec<String>,
        is_parallel: bool,
        is_custom_gate: bool
    ) -> usize {
        let id = self.nodes.len();
        self.nodes.push(
            Node::new(id, template_name, pretty_template_name, parameters, ordered_signals, is_parallel, is_custom_gate)
        );
        self.adjacency.push(vec![]);
        id
    }

    pub fn add_input(&mut self, name: String, is_public: bool) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_input(name, is_public);
        }
    }

    pub fn add_output(&mut self, name: String) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_output(name);
        }
    }

    pub fn add_intermediate(&mut self, name: String) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_intermediate(name);
        }
    }

    pub fn add_constraint(&mut self, constraint: Constraint) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_constraint(constraint);
        }
    }

    pub fn add_underscored_signal(&mut self, signal: usize) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_underscored_signal(signal);
         }
    }
    pub fn add_precondition(&mut self, prec: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_precondition(prec);
        }
    }

    pub fn add_precondition_intermediate(&mut self, prec: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_precondition_intermediate(prec);
        }
    }

    pub fn add_postcondition_intermediate(&mut self, post: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_postcondition_intermediate(post);
        }
    }

    pub fn add_postcondition_output(&mut self, post: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_postcondition_output(post);
        }
    }

    pub fn add_fact(&mut self, fact: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_fact(fact);
        }
    }

    pub fn add_tag_precondition(&mut self, prec: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_tag_precondition(prec);
        }
    }

    pub fn add_tag_postcondition_intermediate(&mut self, post: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_tag_postcondition_intermediate(post);
        }
    }

    pub fn add_tag_postcondition_output(&mut self, post: Expression) {
        if let Option::Some(node) = self.get_mut_main() {
            node.add_tag_postcondition_output(post);
        }
    }

    pub fn set_number_of_subcomponents_indexes(&mut self, number_scmp: usize){
        if let Option::Some(node) = self.get_mut_main() {
            node.set_number_of_subcomponents_indexes(number_scmp);
        }
    }

    pub fn get_node(&self, id: usize) -> Option<&Node> {
        if id < self.nodes.len() {
            Some(&self.nodes[id])
        } else {
            None
        }
    }

    fn raw_find_id_connexion(&self, source: usize, target: usize) -> Option<usize> {
        let cc = &self.adjacency[source];
        let mut index = 0;
        while index < cc.len() && cc[index].goes_to != target {
            index += 1;
        }
        if index == cc.len() {
            Option::None
        } else {
            Option::Some(index)
        }
    }

    pub fn get_connexion(&self, from: usize, to: usize) -> Option<&Edge> {
        let index = self.raw_find_id_connexion(from, to);
        if let Option::Some(i) = index {
            Some(&self.adjacency[from][i])
        } else {
            None
        }
    }

    pub fn get_edges(&self, node: usize) -> Option<&Vec<Edge>> {
        if node < self.nodes.len() {
            Some(&self.adjacency[node])
        } else {
            None
        }
    }

    pub fn constraint_analysis(&mut self) -> Result<ReportCollection, ReportCollection> {
        let reports = constraint_correctness_analysis::analyse(&self.nodes);
        if reports.errors.is_empty() {
            Ok(reports.warnings)
        } else {
            Err(reports.errors)
        }
    }

    pub fn clean_constraints(&mut self) {
        constraint_correctness_analysis::clean_constraints(&mut self.nodes);
    }

    pub fn generate_r1cs_output(&self, output_file: &str, custom_gates: bool) -> Result<(), ()> {
        r1cs_porting::write(self, output_file, custom_gates)
    }

    pub fn generate_sym_output(&self, output_file: &str) -> Result<(), ()> {
        sym_porting::write(self, output_file)
    }

    pub fn generate_json_constraints(&self, debug: &DebugWriter) -> Result<(), ()> {
        json_porting::port_constraints(self, debug)
    }

    pub fn produce_witness(&self) -> Vec<usize> {
        witness_producer::produce_witness(self)
    }

    fn get_mut_main(&mut self) -> Option<&mut Node> {
        self.nodes.last_mut()
    }

    pub fn get_main(&self) -> Option<&Node> {
        self.nodes.last()
    }

    pub fn main_id(&self) -> usize {
        self.nodes.len() - 1
    }

    pub fn number_of_nodes(&self) -> usize {
        self.nodes.len()
    }

    pub fn get_entry(&self) -> Option<&Edge> {
        self.get_main().map(|v| v.get_entry())
    }

    pub fn public_inputs(&self) -> usize {
        if let Option::Some(main) = self.get_main() {
            main.number_of_public_inputs()
        } else {
            0
        }
    }

    pub fn private_inputs(&self) -> usize {
        if let Option::Some(main) = self.get_main() {
            main.number_of_private_inputs()
        } else {
            0
        }
    }

    pub fn public_outputs(&self) -> usize {
        if let Option::Some(main) = self.get_main() {
            main.number_of_outputs()
        } else {
            0
        }
    }

    pub fn map_to_list(self, flags: SimplificationFlags) -> ConstraintList {
        map_to_constraint_list::map(self, flags)
    }

    pub fn map_to_constraint_tree(&self) -> TreeConstraints {
        map_to_constraint_list::map_to_constraint_tree(&self)
    }
}

pub struct SimplificationFlags {
    pub no_rounds: usize,
    pub flag_s: bool,
    pub parallel_flag: bool,
    pub port_substitution: bool,
    pub flag_old_heuristics: bool,
    pub prime : String,
}
