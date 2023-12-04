use std::{collections::{HashMap, LinkedList}, cmp::max};
use num_bigint_dig::BigInt;
use program_structure::ast::{Expression, ExpressionInfixOpcode, ExpressionPrefixOpcode};
use crate::{PossibleResult, ExecutedImplication};
use circom_algebra::{modular_arithmetic, algebra::{
    Constraint, ExecutedInequation}};

        use z3::Config;
        use z3::Context;
        use z3::Solver;
        use z3::ast::Ast;
        use z3::*;

fn is_positive(a: &BigInt, field: &BigInt) -> bool{
    a <= &(field / BigInt::from(2))
}

//This function only works if 0 <= a <= field - 1
fn to_neg(a: &BigInt, field: &BigInt) -> BigInt{
    if a < &(field/BigInt::from(2)){
        a.clone()
    }
    else {
        a - field
    }
}

pub type Signal2Bounds = HashMap<usize, ExecutedInequation<usize>>;

pub struct TemplateVerification {
    pub template_name: String,
    pub signals: LinkedList<usize>,
    pub initial_signal: usize,
    pub number_outputs: usize,
    pub number_inputs: usize,
    pub preconditions: Vec<Expression>,
    pub preconditions_intermediates: Vec<Expression>,
    pub postconditions_intermediates : Vec<Expression>,
    pub postconditions : Vec<Expression>,
    pub facts: Vec<Expression>,
    pub tags_preconditions: Vec<Expression>,
    pub tags_postconditions_intermediates : Vec<Expression>,
    pub tags_postconditions : Vec<Expression>,
    pub constraints: Vec<Constraint<usize>>,
    pub implications: Vec<ExecutedImplication>,
    pub tags_implications: Vec<ExecutedImplication>,
    pub implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
    pub deductions: Signal2Bounds,
    pub substitutions: HashMap<usize, usize>,
    pub field: BigInt,
    pub verbose: bool,
    pub verification_timeout: u64,
    pub check_tags: bool,
    pub check_postconditions: bool,
    pub check_safety: bool,
    pub add_tags_info: bool,
    pub add_postconditions_info: bool,
}

impl TemplateVerification{

    pub fn new(
        template_name: &String,
        signals: LinkedList<usize>,
        initial_signal: usize,
        number_outputs: usize,
        number_inputs: usize,
        constraints: Vec<Constraint<usize>>,
        preconditions: Vec<Expression>,
        preconditions_intermediates: Vec<Expression>,
        postconditions: Vec<Expression>,
        postconditions_intermediates: Vec<Expression>,
        facts: Vec<Expression>,
        tags_preconditions: Vec<Expression>,
        tags_postconditions_intermediates : Vec<Expression>,
        tags_postconditions : Vec<Expression>,
        implications: Vec<ExecutedImplication>,
        tags_implications: Vec<ExecutedImplication>,
        implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
        field: &BigInt,
        verification_timeout: u64, 
        check_tags: bool, 
        check_postconditions: bool,
        check_safety: bool,
        add_tags_info: bool,
        add_postconditions_info: bool,
    ) -> TemplateVerification {
        let mut fixed_constraints = Vec::new();
        for c in constraints{
            let mut new_c = c.clone();
            Constraint::fix_constraint(&mut new_c, field);
            fixed_constraints.push(new_c);
        }
        let mut substitutions = HashMap::new();
        for s in &signals{
            substitutions.insert(*s, *s);
        }

        TemplateVerification {
            template_name: template_name.clone(),
            signals,
            initial_signal,
            number_inputs,
            number_outputs,
            preconditions,
            preconditions_intermediates,
            postconditions,
            postconditions_intermediates,
            facts,
            tags_preconditions,
            tags_postconditions,
            tags_postconditions_intermediates,
            implications,
            tags_implications,
            implications_safety,
            deductions: HashMap::new(),
            substitutions,
            constraints: fixed_constraints,
            field: field.clone(),
            verbose: false,      
            verification_timeout, 
            check_tags, 
            check_postconditions,
            check_safety,
            add_tags_info,
            add_postconditions_info,
        }
    }

    pub fn initialize_bounds_preconditions(&mut self){
        use std::collections::HashSet;

        self.deductions.insert(0, ExecutedInequation{signal: 0, min: BigInt::from(1), max: BigInt::from(1)});
        
        let mut init_signals = HashSet::new();


        for ineq in &self.preconditions{
            let possible_bounds = get_bounds_expression_bool(ineq, &self.field);
            for(signal, (min, max)) in possible_bounds{
                if init_signals.contains(&signal){
                        update_bounds_signal(&mut self.deductions, signal, min, max, &self.field);
                    } else{
                        self.deductions.insert(signal, ExecutedInequation{signal, min, max});        
                        init_signals.insert(signal);
                    }
            }
            
        }
        for ineq in &self.preconditions_intermediates{
            let possible_bounds = get_bounds_expression_bool(ineq, &self.field);
            for(signal, (min, max)) in possible_bounds{
                if init_signals.contains(&signal){
                        update_bounds_signal(&mut self.deductions, signal, min, max, &self.field);
                    } else{
                        self.deductions.insert(signal, ExecutedInequation{signal, min, max});        
                        init_signals.insert(signal);
                    }
            }

        }

        for ineq in &self.facts{
            let possible_bounds = get_bounds_expression_bool(ineq, &self.field);
            for(signal, (min, max)) in possible_bounds{
                if init_signals.contains(&signal){
                        update_bounds_signal(&mut self.deductions, signal, min, max, &self.field);
                    } else{
                        self.deductions.insert(signal, ExecutedInequation{signal, min, max});        
                        init_signals.insert(signal);
                    }
            }

        }

    }


    pub fn deduce(&mut self)-> (PossibleResult, PossibleResult, PossibleResult) {        //self.print_pretty_template_verification();
        self.deduce_round();

        let result_tags = if self.check_tags{
            if self.tags_postconditions_intermediates.is_empty() && self.tags_postconditions.is_empty(){
                println!("### NOTHING TO VERIFY: THE TEMPLATE DOES NOT CONTAIN TAGGED OUTPUTS");
                PossibleResult::NOTHING
            } else{
                self.try_prove_tags()
            }
        } else{
            PossibleResult::NOSTUDIED
        };
        let result_post = if self.check_postconditions{
            if self.postconditions_intermediates.is_empty() && self.postconditions.is_empty(){
                println!("### NOTHING TO VERIFY: THE TEMPLATE DOES NOT CONTAIN POSTCONDITIONS");
                PossibleResult::NOTHING
            } else{
                self.try_prove_postconditions()
            }
        } else{
            PossibleResult::NOSTUDIED
        };
        let result_safety = if self.check_safety{
            self.try_prove_safety()
        } else{
            PossibleResult::NOSTUDIED
        };

        (result_tags, result_post, result_safety)
    }

    // returns the signals where it was able to find new bounds
    pub fn deduce_round(&mut self)-> Vec<usize>{
        let mut new_signal_bounds:Vec<usize> = Vec::new();
        let mut new_signal_bounds_iteration = Vec::new();

        self.initialize_bounds_preconditions();

        let filter_const = std::mem::take(&mut self.constraints);

        for c in filter_const{
            let should_remove = deduction_rule_integrity_domain(&mut self.deductions, &c, &self.field); 
            if !should_remove{ 
                self.constraints.push(c);
            }
        } 

        for c in &self.constraints{
            new_signal_bounds_iteration.append(&mut deduction_rule_apply_bounds_constraint(&mut self.deductions, &c, &self.field, self.verbose));
        }

        while !new_signal_bounds_iteration.is_empty(){
            new_signal_bounds.append(&mut new_signal_bounds_iteration);
            for c in &self.constraints{
              
                new_signal_bounds_iteration.append(&mut deduction_rule_apply_bounds_constraint(&mut self.deductions, &c, &self.field, self.verbose));
            }
        }
        new_signal_bounds
    }


    pub fn try_prove_tags(&self)-> PossibleResult{
        let mut cfg = Config::new();
        cfg.set_timeout_msec(self.verification_timeout);
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let zero = z3::ast::Int::from_i64(&ctx, 0);
        let field = z3::ast::Int::from_str(&ctx, &self.field.to_string()).unwrap();
        let mut aux_signals_to_smt_rep = HashMap::new();
        for s in &self.signals{
            let aux_signal_to_smt = z3::ast::Int::new_const(&ctx, format!("s_{}", s));
            
            match self.deductions.get(s){
                None =>{ // cambiar a que sea un -p/2 a p/2 + 1?
                    solver.assert(&aux_signal_to_smt.ge(&zero));
                    solver.assert(&aux_signal_to_smt.lt(&field));
                }
                Some(bounds) =>{

                    let condition = get_z3_condition_bounds(
                        &ctx, 
                        &aux_signal_to_smt, 
                        &bounds.min, 
                        &bounds.max, 
                        &self.field
                    );

                    solver.assert(&condition);
                }
            }
            aux_signals_to_smt_rep.insert(*s, aux_signal_to_smt);
        }

        let mut value_preconditions = z3::ast::Bool::from_bool(&ctx, true);
        for precondition in &self.preconditions{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }
        for precondition in &self.preconditions_intermediates{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }
        for precondition in &self.tags_preconditions{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }
        for precondition in &self.facts{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }
        if self.verbose{
            println!("Preconditions: {}", value_preconditions.to_string());
        }

        solver.assert(&value_preconditions);


        let mut i = 0;
        for constraint in &self.constraints{
            insert_constraint_in_smt(constraint, &ctx, &solver, &aux_signals_to_smt_rep, &self.field, 
                                        &self.deductions, i, &field, self.verbose);
            i = i + 1;
        }


        for implication in &self.tags_implications{
            insert_implication_in_smt(implication, &ctx, &solver, &aux_signals_to_smt_rep, &self.field);
        }

        if self.check_postconditions{
            for implication in &self.implications{
                insert_implication_in_smt(implication, &ctx, &solver, &aux_signals_to_smt_rep, &self.field);
            }
        }

        let mut value_postconditions = z3::ast::Bool::from_bool(&ctx, true);
        for postcondition in &self.tags_postconditions{
            value_postconditions &= get_z3_expression_bool(&ctx, &postcondition, &aux_signals_to_smt_rep).unwrap();
        }
        for postcondition in &self.tags_postconditions_intermediates{
            value_postconditions &= get_z3_expression_bool(&ctx, &postcondition, &aux_signals_to_smt_rep).unwrap();
        }
        if self.verbose{
            println!("Postconditions: {}", value_postconditions.to_string());
        }

        solver.assert(&!value_postconditions);

        match solver.check(){
            SatResult::Sat =>{
                println!("### THE VERIFICATION OF THE TAGS OF THE TEMPLATE FAILED. FOUND COUNTEREXAMPLE USING SMT:");
                //if self.verbose{

                 let model = solver.get_model().unwrap();
                 for s in &self.signals{
                     let v = model.eval(aux_signals_to_smt_rep.get(s).unwrap(), true).unwrap();
                     println!("Signal {}: {}", s, v.to_string());
                 }
                //}
                PossibleResult::FAILED
            },
            SatResult::Unsat =>{
                println!("### SUCCESS: THE TAGS OF THE TEMPLATE ARE VERIFIED");
                PossibleResult::VERIFIED
            },
            _=> {
                println!("### UNKNOWN: VERIFICATION OF THE TAGS TIMEOUT");
                PossibleResult::UNKNOWN
            }
        }
    }

    pub fn try_prove_postconditions(&self)-> PossibleResult{
        let mut cfg = Config::new();
        cfg.set_timeout_msec(self.verification_timeout);
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let zero = z3::ast::Int::from_i64(&ctx, 0);
        let field = z3::ast::Int::from_str(&ctx, &self.field.to_string()).unwrap();
        let mut aux_signals_to_smt_rep = HashMap::new();
        for s in &self.signals{
            let aux_signal_to_smt = z3::ast::Int::new_const(&ctx, format!("s_{}", s));
            
            match self.deductions.get(s){
                None =>{ // cambiar a que sea un -p/2 a p/2 + 1?
                    solver.assert(&aux_signal_to_smt.ge(&zero));
                    solver.assert(&aux_signal_to_smt.lt(&field));
                }
                Some(bounds) =>{

                    let condition = get_z3_condition_bounds(
                        &ctx, 
                        &aux_signal_to_smt, 
                        &bounds.min, 
                        &bounds.max, 
                        &self.field
                    );

                    if self.verbose{
                        println!("Signal bounds: {}", condition.to_string());  
                    }
                    solver.assert(&condition);
                }
            }
            aux_signals_to_smt_rep.insert(*s, aux_signal_to_smt);
        }

        let mut value_preconditions = z3::ast::Bool::from_bool(&ctx, true);
        for precondition in &self.preconditions{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }
        for precondition in &self.preconditions_intermediates{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }
        for precondition in &self.tags_preconditions{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }
        if self.add_tags_info{
            for precondition in &self.tags_postconditions_intermediates{
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
            }
            for precondition in &self.tags_postconditions{
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
            }
        }
        for precondition in &self.facts{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
        }

        if self.verbose{
            println!("Preconditions: {}", value_preconditions.to_string());
        }

        solver.assert(&value_preconditions);


        let mut i = 0;
        for constraint in &self.constraints{
            insert_constraint_in_smt(constraint, &ctx, &solver, &aux_signals_to_smt_rep, &self.field, 
                                        &self.deductions, i, &field, self.verbose);
            i = i + 1;
        }
        if self.check_tags{
            for implication in &self.tags_implications{
                insert_implication_in_smt(implication, &ctx, &solver, &aux_signals_to_smt_rep, &self.field);
            }
        }
        for implication in &self.implications{
            insert_implication_in_smt(implication, &ctx, &solver, &aux_signals_to_smt_rep, &self.field);
        }

        let mut value_postconditions = z3::ast::Bool::from_bool(&ctx, true);
        for postcondition in &self.postconditions{
            value_postconditions &= get_z3_expression_bool(&ctx, &postcondition, &aux_signals_to_smt_rep).unwrap();
        }
        for postcondition in &self.postconditions_intermediates{
            value_postconditions &= get_z3_expression_bool(&ctx, &postcondition, &aux_signals_to_smt_rep).unwrap();
        }
        //if self.verbose{
        //    println!("Postconditions: {}", value_postconditions.to_string());
        //}

        solver.assert(&!value_postconditions);

        //if self.print_smt{
        //    println!("{:?}", solver);
        //}

        match solver.check(){
            SatResult::Sat =>{
                println!("### THE VERIFICATION OF THE SPECIFICATION OF THE TEMPLATE FAILED. FOUND COUNTEREXAMPLE USING SMT:");
                //if self.verbose{

                 let model = solver.get_model().unwrap();
                 for s in &self.signals{
                     let v = model.eval(aux_signals_to_smt_rep.get(s).unwrap(), true).unwrap();
                     println!("Signal {}: {}", s, v.to_string());
                 }
                //}
                PossibleResult::FAILED
            },
            SatResult::Unsat =>{
                println!("### SUCCESS: THE SPECIFICATION OF THE TEMPLATE IS VERIFIED");
                PossibleResult::VERIFIED
            },
            _=> {
                println!("### UNKNOWN: VERIFICATION OF THE TEMPLATE SPECIFICATION TIMEOUT");
                PossibleResult::UNKNOWN
            }
        }
    }


    pub fn try_prove_safety(&self) -> PossibleResult{
        let mut cfg = Config::new();
        cfg.set_timeout_msec(self.verification_timeout);
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let zero = z3::ast::Int::from_i64(&ctx, 0);
        let field = z3::ast::Int::from_str(&ctx, &self.field.to_string()).unwrap();
        let mut aux_signals_to_smt_rep = HashMap::new();
        let mut aux_signals_to_smt_rep_aux = HashMap::new();

        for s in &self.signals{
            let is_input = s >= &(self.initial_signal + self.number_outputs) && s < &(self.initial_signal + self.number_outputs + self.number_inputs);

            let aux_signal_to_smt = z3::ast::Int::new_const(&ctx, format!("s_{}", s));
            let copy_aux_signal_to_smt = if !is_input{
                z3::ast::Int::new_const(&ctx, format!("saux_{}", s))
            } else{
                z3::ast::Int::new_const(&ctx, format!("s_{}", s))
            };
            aux_signals_to_smt_rep.insert(*s, aux_signal_to_smt.clone());
            aux_signals_to_smt_rep_aux.insert(*s, copy_aux_signal_to_smt.clone());

            match self.deductions.get(s){
                None =>{
                    solver.assert(&aux_signal_to_smt.ge(&zero));
                    solver.assert(&aux_signal_to_smt.lt(&field));
                    solver.assert(&copy_aux_signal_to_smt.ge(&zero));
                    solver.assert(&copy_aux_signal_to_smt.lt(&field));
                }
                Some(bounds) =>{

                    let condition = get_z3_condition_bounds(
                        &ctx, 
                        &aux_signal_to_smt, 
                        &bounds.min, 
                        &bounds.max, 
                        &self.field
                    );
                    solver.assert(&condition);

                    let condition = get_z3_condition_bounds(
                        &ctx, 
                        &copy_aux_signal_to_smt, 
                        &bounds.min, 
                        &bounds.max, 
                        &self.field
                    );
                    solver.assert(&condition);
                }
            }

        }

        let mut value_preconditions = z3::ast::Bool::from_bool(&ctx, true);
        for precondition in &self.preconditions{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();

        }
        for precondition in &self.preconditions_intermediates{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();

        }
        for precondition in &self.tags_preconditions{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();

        }
        if self.add_tags_info{
            for precondition in &self.tags_postconditions_intermediates{
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();
            }
            for precondition in &self.tags_postconditions{
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();

            }
        }
        if self.add_postconditions_info{
            for precondition in &self.postconditions_intermediates{
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();
            }
            for precondition in &self.postconditions{
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
                value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();
            }
        }

        for precondition in &self.facts{
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep).unwrap();
            value_preconditions &= get_z3_expression_bool(&ctx, &precondition, &aux_signals_to_smt_rep_aux).unwrap();
        }

        solver.assert(&value_preconditions);

        let mut i = 0;
        for constraint in &self.constraints{
            insert_constraint_in_smt(constraint, &ctx, &solver, &aux_signals_to_smt_rep, &self.field, 
                                        &self.deductions, i, &field, self.verbose);
            i = i + 1;
            insert_constraint_in_smt(constraint, &ctx, &solver, &aux_signals_to_smt_rep_aux, &self.field, 
                &self.deductions, i, &field, self.verbose);
            i = i + 1;
        }


        apply_deduction_rule_homologues(&self.constraints,  &ctx, &solver, &aux_signals_to_smt_rep, &aux_signals_to_smt_rep_aux, &self.field, &field);



        for (inputs, outputs) in &self.implications_safety{
            let mut implication_left = z3::ast::Bool::from_bool(&ctx, true);
            for s in inputs{
                let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
                let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
                implication_left &= s_1._eq(s_2);
            }
            let mut implication_right = z3::ast::Bool::from_bool(&ctx, true);
            for s in outputs{
                let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
                let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
                implication_right &= s_1._eq(s_2);
            }

            solver.assert(&implication_left.implies(&implication_right));
        }
        if self.check_tags{
            for implication in &self.tags_implications{
                insert_implication_in_smt(implication, &ctx, &solver, &aux_signals_to_smt_rep, &self.field);
            }
        }
        if self.check_postconditions{
            for implication in &self.implications{
                insert_implication_in_smt(implication, &ctx, &solver, &aux_signals_to_smt_rep, &self.field);
            }
        }



        let mut all_outputs_equal = z3::ast::Bool::from_bool(&ctx, true);
        for s in 0..self.number_outputs{
            let s_1 = aux_signals_to_smt_rep.get(&(self.initial_signal + s)).unwrap();
            let s_2 = aux_signals_to_smt_rep_aux.get(&(self.initial_signal + s)).unwrap();
            all_outputs_equal &= s_1._eq(s_2);
        } 

        solver.assert(&!all_outputs_equal);
        
        //if self.print_smt{
        //    println!("{:?}", solver);
        //}

        match solver.check(){
            SatResult::Sat =>{
                println!("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:");
                //if self.verbose{

                let model = solver.get_model().unwrap();
                for s in 0..self.number_inputs{
                    let v = model.eval(aux_signals_to_smt_rep.get(&(self.initial_signal + self.number_outputs + s)).unwrap(), true).unwrap();
                    println!("Input signal {}: {}", self.initial_signal + self.number_outputs + s, v.to_string());

                }
                for s in 0..self.number_outputs{
                    let v = model.eval(aux_signals_to_smt_rep.get(&(self.initial_signal + s)).unwrap(), true).unwrap();
                    let v1 = model.eval(aux_signals_to_smt_rep_aux.get(&(self.initial_signal + s)).unwrap(), true).unwrap();

                    println!("Output signal {}: values {} | {}", self.initial_signal + s, v.to_string(), v1.to_string());

                }

                PossibleResult::FAILED
                //}
            },
            SatResult::Unsat =>{
                println!("### WEAK SAFETY ENSURED BY THE TEMPLATE");
                PossibleResult::VERIFIED
            },
            _=> {
                println!("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT");
                PossibleResult::UNKNOWN
            }
        }



    }
}


pub fn update_bounds_signal(deductions: &mut Signal2Bounds, signal: usize, min: BigInt, max: BigInt, field: &BigInt) -> bool{
    let pos_bounds = deductions.get_mut(&signal);
    match pos_bounds{
        None => {

            deductions.insert(
                signal,
                ExecutedInequation{signal, min, max}
            );
            true
        }
        

        Some(bounds) => {
            if !(&bounds.min <= &BigInt::from(0) && &max >= &(field - &BigInt::from(1))){
                bounds.update_bounds(min, max)
            } else{
                false
            }
        }
    }
}

pub fn solve_signal_plus_coef(a: &HashMap<usize, BigInt>, field: &BigInt) -> Option<(usize,BigInt)> {

    if (a.len() == 1 && !a.contains_key(&0)) || (a.len() == 2 && a.contains_key(&0)){
        let mut to_solve_signal = 0;
        let mut coef_indep = &BigInt::from(0);
        let mut coef_signal =  &BigInt::from(0);
        for (signal, coef) in a{
            if *signal == 0 {
                coef_indep = coef;
            } else{
                to_solve_signal = *signal;
                coef_signal = coef;
            }
        }
        match modular_arithmetic::div(&modular_arithmetic::prefix_sub(coef_indep, field), coef_signal, field){
            Ok(value) => Some((to_solve_signal, value)),
            Err(_) => None
        }
    } else{
        Option::None
    }
}

pub fn check_same_field_round(a: &BigInt, b: &BigInt, field: &BigInt)-> bool{
    check_correct_signs(a, b) && (a / field == b / field)
}

fn check_consecutive_field_round(min: &BigInt, max: &BigInt, field: &BigInt)-> bool{
    // queremos que acepte cosas como [-1, 1] y lo guarde --> ahora mismo no funciona
    let zero = &BigInt::from(0);
    let two = &BigInt::from(2);
    if min < zero && max >= zero{
        min > &(- field / two) && max <= &(field / two) // o quiza solo que este entro (-field, field)
    } else if min < max{
        min / field == field / field - 1
    } else{
        false
    }
}

pub fn check_correct_signs(a: &BigInt, b: &BigInt)-> bool{
    // revisar esta también
    let zero = &BigInt::from(0);
    !(a >= zero && b < zero) && !(b >= zero && a < zero) 
}

fn compute_bounds_linear_expression(deductions: &Signal2Bounds, le: &HashMap<usize, BigInt>, field: &BigInt) -> (BigInt, BigInt){
    let mut lower_limit = BigInt::from(0);
    let mut upper_limit = BigInt::from(0);
    for (signal, coef) in le{
        let (min, max) = if deductions.contains_key(&signal){
            let bounds = deductions.get(&signal).unwrap();
            (bounds.min.clone(), bounds.max.clone())
        } else{
            (BigInt::from(0), field - &BigInt::from(1))
        };
        if is_positive(coef, field){
            upper_limit = upper_limit + coef * max;
            lower_limit = lower_limit + coef * min;
        } else{
            let neg_coef = field - coef;
            upper_limit = upper_limit - &neg_coef * min;
            lower_limit = lower_limit - &neg_coef * max;
        }
    }
    (lower_limit, upper_limit)
}

fn compute_bounds_linear_expression_strict(deductions: &Signal2Bounds, le: &HashMap<usize, BigInt>, field: &BigInt) -> (BigInt, BigInt){
    let mut lower_limit = BigInt::from(0);
    let mut upper_limit = BigInt::from(0);
    for (signal, coef) in le{
        let (min, max) = if deductions.contains_key(&signal){
            let bounds = deductions.get(&signal).unwrap();
            if bounds.min >= BigInt::from(0){
                (bounds.min.clone(), bounds.max.clone())
            }
            else {
                (BigInt::from(0), field - &BigInt::from(1))
            }
        } else{
            (BigInt::from(0), field - &BigInt::from(1))
        };
        if is_positive(coef, field){
            upper_limit = upper_limit + coef * max;
            lower_limit = lower_limit + coef * min;
        } else{
            let neg_coef = field - coef;
            upper_limit = upper_limit - &neg_coef * min;
            lower_limit = lower_limit - &neg_coef * max;
        }
    }
    (lower_limit, upper_limit)
}

fn compute_bounds_product(min_1: &BigInt, max_1: &BigInt, min_2: &BigInt, max_2: &BigInt)-> (BigInt, BigInt){
    let zero = &BigInt::from(0);
    if min_1 >= zero{ // bounds_1 are positive
        if min_2 >= zero{ // bounds_2 are two-positive
            (min_1 * min_2, max_1 * max_2)
        } else if max_2 >= zero{ // bounds_2 are neg/pos
            (max_1 * min_2, max_1 * max_2)
        } else{ // bounds_2 are two_negative
            (max_1 * min_2, min_1 * max_2)
        }
    } else if max_1 >= zero{ // bounds_1 are neg/pos
        if min_2 >= zero{ // bounds_2 are two-positive
            (min_1 * max_2, max_1 * max_2)
        } else if max_2 >= zero{ // bounds_2 are neg/pos
            (max(min_1 * max_2, min_2 * max_1), max(min_1 * min_2, max_1 * max_2))
        } else{ // bounds_2 are two_negative
            (max_1 * min_2, min_1 * min_2)
        }
    } else{ // bounds_1 are negative
        if min_2 >= zero{ // bounds_2 are two-positive
            (min_1 * max_2, max_1 * min_2)
        } else if max_2 >= zero{ // bounds_2 are neg/pos
            (min_1 * max_2, min_1 * min_2)
        } else{ // bounds_2 are two_negative
            (max_1 * max_2, min_1 * min_2)
        }
    }
}

// fn deduction_rule_implications_with_deduced_preconditions(
//     deductions: &mut Signal2Bounds, 
//     implication: &ExecutedImplication, 
//     field: &BigInt
// ) -> Vec<usize> {
//     let mut updated_signals = Vec::new();
//     let mut check_preconditions = true;
    
//     for precondition in &implication.left {
//         check_preconditions &= implies_bounds_signal(deductions, precondition.signal, &precondition.min, &precondition.max, field);
//     }
//     if check_preconditions {
//         for postcondition in &implication.right{
//             if update_bounds_signal(deductions, postcondition.signal, postcondition.min.clone(), postcondition.max.clone(), field){
//                 updated_signals.push(postcondition.signal.clone());
//             }
//         }
//     }
//     updated_signals
// }

// (x - a)*(x - b) = 0 ==> a <= x <= b

pub fn deduction_rule_integrity_domain(
    deductions: &mut Signal2Bounds,
    constraint: &Constraint<usize>, 
    field: &BigInt
) -> bool{
    let mut updated_signals = Vec::new();
    let mut completely_studied = false;
    
    let a = constraint.a();
    let b = constraint.b();
    let c = constraint.c();

    if let Option::Some((a_signal, a_value)) = solve_signal_plus_coef(a, field) {
        if let Option::Some((b_signal, b_value)) = solve_signal_plus_coef(b, field) {
            if a_signal == b_signal && c.is_empty() {

                if a_value > b_value {
                    completely_studied = &a_value - &b_value == BigInt::from(1);
                    if update_bounds_signal(deductions, a_signal, b_value, a_value, field){
                        
                        updated_signals.push(a_signal);
                    }
                }
                else {
                    completely_studied = &b_value - &a_value ==  BigInt::from(1);
                    if update_bounds_signal(deductions, a_signal, a_value, b_value, field){
                        
                        updated_signals.push(a_signal);
                    }  
                }

            }
        }
    }
    completely_studied
}

pub fn deduction_rule_apply_bounds_constraint(
    deductions: &mut Signal2Bounds,
    constraint: &Constraint<usize>,
    field: &BigInt, 
    verbose: bool,
)-> Vec<usize> {
    let mut updated_signals = Vec::new();

    let a = constraint.a();
    let b = constraint.b();
    let c = constraint.c();

    let (lower_limit_a, upper_limit_a) = compute_bounds_linear_expression(deductions, &a, field);
    let (lower_limit_b, upper_limit_b) = compute_bounds_linear_expression(deductions, &b, field);

    let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
        &lower_limit_a, 
        &upper_limit_a, 
        &lower_limit_b, 
        &upper_limit_b
    );

    //println!("Cota superior ab {}", upper_limit_ab);
    //println!("Cota inferior ab {}", lower_limit_ab);
    
    let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression(deductions, &c, field);

    let lower_limit = lower_limit_c - upper_limit_ab;
    let upper_limit = upper_limit_c - lower_limit_ab;

    //println!("Cota superior {}", upper_limit);
    //println!("Cota inferior {}", lower_limit);

    for (signal, coef) in c{
        if coef == &BigInt::from(1) || *coef == field - &BigInt::from(1) {
            let (min, max) = if deductions.contains_key(signal){
                let bounds = deductions.get(signal).unwrap();
                (bounds.min.clone(), bounds.max.clone())
            } else{
                (BigInt::from(0), field - BigInt::from(1))
            };
            let (pos_max, pos_min);
            let (valid_bounds, valid_consecutive) = if coef == &BigInt::from(1){
                let (aux_min, aux_max) = (&upper_limit - max, &lower_limit - min);
                pos_min = (field - &aux_min) % field;
                pos_max = (field - &aux_max) % field;
                (
                    check_same_field_round(&(field - &aux_min), &(field - &aux_max), field),
                    check_consecutive_field_round(&(field - &aux_min), &(field - &aux_max), field)
                )
            } else{
                let (aux_min, aux_max) = (&lower_limit + max, &upper_limit + min);
                pos_min = &aux_min % field;
                pos_max = &aux_max % field;
                (
                    check_same_field_round(&aux_min, &aux_max, field),
                    check_consecutive_field_round(&aux_min, &aux_max, field) 
                )          
            };
    
            if valid_bounds{
                if update_bounds_signal(deductions, *signal, pos_min, pos_max, field){
                    updated_signals.push(signal.clone());
                }
            }
            else if false && valid_consecutive{
                if verbose{
                    println!("Annadiendo bounds {} {} como de distinta ronda", pos_min, pos_max);
                }
                if update_bounds_signal(deductions, *signal, field - pos_min, pos_max, field){
                    updated_signals.push(signal.clone());
                }
            }
        }
        
    }
    updated_signals
}


pub fn apply_deduction_rule_homologues(
    constraints: &Vec<Constraint<usize>>,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>,
    signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>,
    field: &BigInt,
    p : &z3::ast::Int,
){
    for c in constraints{
        let mut value_a = z3::ast::Int::from_u64(ctx, 0);
        let mut value_b = z3::ast::Int::from_u64(ctx, 0);
        let mut value_c = z3::ast::Int::from_u64(ctx, 0);

        let mut value_a1 = z3::ast::Int::from_u64(ctx, 0);
        let mut value_b1 = z3::ast::Int::from_u64(ctx, 0);
        let mut value_c1 = z3::ast::Int::from_u64(ctx, 0);

        for (signal, value) in c.a(){
            if *signal == 0{
                value_a += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_a1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();         
            } else{
                value_a += signals_to_smt_symbols_1.get(signal).unwrap() *
                    &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_a1 += signals_to_smt_symbols_2.get(signal).unwrap() *
                    &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in c.b(){
            if *signal == 0{
                value_b += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_b1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();

            } else{
                value_b += signals_to_smt_symbols_1.get(signal).unwrap() *
                    &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_b1 += signals_to_smt_symbols_2.get(signal).unwrap() *
                    &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in c.c(){
            if *signal == 0{
                value_c += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_c1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();

            } else{
                value_c += signals_to_smt_symbols_1.get(signal).unwrap() *
                    &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_c1 += signals_to_smt_symbols_2.get(signal).unwrap() *
                    &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            }
        }

        let zero = z3::ast::Int::from_u64(&ctx, 0);
        let condition_aa = &(&value_a - &value_a1)._eq(&zero);
        let condition_bb = &(&value_b - &value_b1)._eq(&zero);
        let condition_cc = &(&value_c - &value_c1)._eq(&zero);

        let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
        value_cond |= !condition_aa;
        value_cond |=  !condition_bb;
        value_cond |=  condition_cc;
        solver.assert(&value_cond);


        let condition_a_not_zero = !&value_a.modulo(&p)._eq(&zero);
        let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
        value_cond |= !(condition_aa & condition_a_not_zero);
        value_cond |=  !condition_cc;
        value_cond |=  condition_bb;
        solver.assert(&value_cond);

        let condition_b_not_zero = !&value_b.modulo(&p)._eq(&zero);
        let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
        value_cond |= !(condition_bb & condition_b_not_zero);
        value_cond |=  !condition_cc;
        value_cond |=  condition_aa;
        solver.assert(&value_cond);

    }

    

}


pub fn insert_constraint_in_smt(
    constraint: &Constraint<usize>,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols: &HashMap<usize, z3::ast::Int>,
    field: &BigInt,
    deductions: &Signal2Bounds,
    num_k : usize,
    p : &z3::ast::Int,
    verbose: bool,
){
    let mut value_a = z3::ast::Int::from_u64(ctx, 0);
    let mut value_b = z3::ast::Int::from_u64(ctx, 0);
    let mut value_c = z3::ast::Int::from_u64(ctx, 0);


    for (signal, value) in constraint.a(){
        if *signal == 0{
            value_a += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else{
            value_a += signals_to_smt_symbols.get(signal).unwrap() *
                &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.b(){
        if *signal == 0{
            value_b += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else{
            value_b += signals_to_smt_symbols.get(signal).unwrap() *
                &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.c(){
        if *signal == 0{
            value_c += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else{
            value_c += signals_to_smt_symbols.get(signal).unwrap() *
                &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }


    let a = constraint.a();
    let b = constraint.b();
    let c = constraint.c();
    let (lower_limit_a, upper_limit_a) = compute_bounds_linear_expression_strict(deductions, &a, field);
    let (lower_limit_b, upper_limit_b) = compute_bounds_linear_expression_strict(deductions, &b, field);

    let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
        &lower_limit_a, 
        &upper_limit_a, 
        &lower_limit_b, 
        &upper_limit_b
    );

 
    let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression_strict(deductions, &c, field);
    
    let lower_limit_k =  (&lower_limit_c - &upper_limit_ab)/field;
    let upper_limit_k = if (&upper_limit_c - &lower_limit_ab)/field > BigInt::from(0) && (&upper_limit_c - &lower_limit_ab)%field != BigInt::from(0) {
        (&upper_limit_c - &lower_limit_ab)/field + BigInt::from(1)
    } else{
        (&upper_limit_c - &lower_limit_ab)/field
    };

    let lower_limit_k_a = &lower_limit_a / field;
    let upper_limit_k_a = if &upper_limit_a / field > BigInt::from(0) && &upper_limit_a%field != BigInt::from(0) {
        &upper_limit_a/field + BigInt::from(1)
    } else{
        &upper_limit_a/field
    };

    let lower_limit_k_b = &lower_limit_b / field;
    let upper_limit_k_b = if &upper_limit_b / field > BigInt::from(0) && &upper_limit_b%field != BigInt::from(0) {
        &upper_limit_b/field + BigInt::from(1)
    } else{
        &upper_limit_b/field
    };

    let lower_limit_k_c = &lower_limit_c / field;
    let upper_limit_k_c = if &upper_limit_c / field > BigInt::from(0) && &upper_limit_c%field != BigInt::from(0) {
        &upper_limit_c/field + BigInt::from(1)
    } else{
        &upper_limit_c/field
    };


    // Apply transformation rule A * B = 0 => (A = 0) \/ (B = 0)
    if &upper_limit_c == &lower_limit_c && &upper_limit_c == &BigInt::from(0) {
        let mut value_or = z3::ast::Bool::from_bool(&ctx, false);
        


        let value_or_a = 
            if upper_limit_k_a == lower_limit_k_a{
                let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_a.to_string()).unwrap() * p;
                value_a._eq(&value_right)
            } else{
                let k = z3::ast::Int::new_const(&ctx, format!("k_{}_a", num_k));
        
                let value_right = &k*p;
                solver.assert( 
                    &k.ge(
                        &z3::ast::Int::from_str(&ctx, &lower_limit_k_a.to_string()).unwrap()
                    )
                );
                solver.assert(
                    &k.le(
                        &z3::ast::Int::from_str(&ctx, &upper_limit_k_a.to_string()).unwrap()
                    )
                );
                    
                value_a._eq(&value_right)
            };  
        

        let value_or_b = 
            if upper_limit_k_b == lower_limit_k_b{
                let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_b.to_string()).unwrap() * p;
                value_b._eq(&value_right)
            } else {
                let k = z3::ast::Int::new_const(&ctx, format!("k_{}_b", num_k));
        
                let value_right = &k*p;
                solver.assert( 
                    &k.ge(
                        &z3::ast::Int::from_str(&ctx, &lower_limit_k_b.to_string()).unwrap()
                    )
                );
                solver.assert(
                    &k.le(
                        &z3::ast::Int::from_str(&ctx, &upper_limit_k_b.to_string()).unwrap()
                    )
                );
                    
                value_b._eq(&value_right)
            };
        
        value_or |= value_or_a;
        value_or |= value_or_b;
        solver.assert(&value_or);
    } else{
        // Apply deduction rule A * B = C => (C != 0) \/ (A = 0) \/ (B = 0)
        let condition_c = 
            if upper_limit_k_c == lower_limit_k_c{
                let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_c.to_string()).unwrap() * p;
                value_c._eq(&value_right)
            } else{
                let k = z3::ast::Int::new_const(&ctx, format!("k_{}_c", num_k));
        
                let value_right = &k*p;
                solver.assert( 
                    &k.ge(
                        &z3::ast::Int::from_str(&ctx, &lower_limit_k_c.to_string()).unwrap()
                    )
                );
                solver.assert(
                    &k.le(
                        &z3::ast::Int::from_str(&ctx, &upper_limit_k_c.to_string()).unwrap()
                    )
                );
                value_c._eq(&value_right)
            };

        let condition_a: ast::Bool =
            if upper_limit_k_a == lower_limit_k_a{
                let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_a.to_string()).unwrap() * p;
                value_a._eq(&value_right)
            } else{
                let k = z3::ast::Int::new_const(&ctx, format!("k_{}_a", num_k));
        
                let value_right = &k*p;
                solver.assert( 
                    &k.ge(
                        &z3::ast::Int::from_str(&ctx, &lower_limit_k_a.to_string()).unwrap()
                    )
                );
                solver.assert(
                    &k.le(
                        &z3::ast::Int::from_str(&ctx, &upper_limit_k_a.to_string()).unwrap()
                    )
                );
                    
                value_a._eq(&value_right)
            };


        let condition_b = 
            if upper_limit_k_b == lower_limit_k_b{
                let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_b.to_string()).unwrap() * p;
                value_b._eq(&value_right)
            } else{
                let k = z3::ast::Int::new_const(&ctx, format!("k_{}_b", num_k));
    
                let value_right = &k*p;
                solver.assert( 
                    &k.ge(
                        &z3::ast::Int::from_str(&ctx, &lower_limit_k_b.to_string()).unwrap()
                    )
                );
                solver.assert(
                    &k.le(
                        &z3::ast::Int::from_str(&ctx, &upper_limit_k_b.to_string()).unwrap()
                    )
                );
                
                value_b._eq(&value_right)
            };

        let mut value_or = z3::ast::Bool::from_bool(&ctx, false);
        value_or |= !condition_c;
        value_or |= condition_a;
        value_or |= condition_b;
        solver.assert(&value_or);


        // APPLY TRANSFORMATION RULE REMOVE MOD
        if lower_limit_k == upper_limit_k{
    
            let value_left = value_c - (value_a * value_b);
            let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k.to_string()).unwrap() * p;
            if verbose{
                println!("Constraint (does not need k because only one possible value) {} = {}", value_left.to_string(), value_right.to_string());
            }
            solver.assert(&value_left._eq(&value_right));
        } else{
            let k = z3::ast::Int::new_const(&ctx, format!("k_{}", num_k));
        
            let value_left =  value_c - (value_a * value_b);
            let value_right = &k*p;
            solver.assert(
                 &k.ge(
                    &z3::ast::Int::from_str(&ctx, &lower_limit_k.to_string()).unwrap()
                )
            );
            solver.assert(
                &k.le(
                    &z3::ast::Int::from_str(&ctx, &upper_limit_k.to_string()).unwrap()
                )               
            );
            if verbose{
                println!("Constraint {} = {}", value_left.to_string(), value_right.to_string());
                println!("Possible values k : {} - {}", lower_limit_k, upper_limit_k);
            }
            solver.assert(&value_left._eq(&value_right));
        }
    }
    
}


pub fn insert_implication_in_smt(
    implication: &ExecutedImplication,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols: &HashMap<usize, z3::ast::Int>,
    _field: &BigInt,
){
    let mut value_left = z3::ast::Bool::from_bool(ctx, true);
    let mut value_right = z3::ast::Bool::from_bool(ctx, true);

    for condition_left in &implication.left{
        value_left &= get_z3_expression_bool(ctx, condition_left, signals_to_smt_symbols).unwrap();
    }

    for condition_right in &implication.right{
        value_right &= get_z3_expression_bool(ctx, condition_right, signals_to_smt_symbols).unwrap();

    }

    //println!("Implication: {} implies {}", value_left, value_right);
    solver.assert(&value_left.implies(&value_right));
    
}



pub fn get_z3_condition_bounds<'a>(ctx: &'a Context,signal: &'a z3::ast::Int<'a>, min: &'a BigInt, max: &'a BigInt, field: &'a BigInt) -> z3::ast::Bool<'a>{
    if min >= &BigInt::from(0){
        
        &signal.ge(
            &z3::ast::Int::from_str(&ctx, &min.to_string()).unwrap()
        )
        &                                           
        &signal.le(
            &z3::ast::Int::from_str(&ctx, &max.to_string()).unwrap()
        )
        
    } else{
        
                &z3::ast::Int::from_str(&ctx, &(field + min).to_string()).unwrap().le(
                    signal)
                & 
                &signal.lt(
                    &z3::ast::Int::from_str(&ctx, &field.to_string()).unwrap()
                )
            |
            
                &z3::ast::Int::from_i64(&ctx, 0).le(
                    &signal
                )
                &
                signal.le(
                    &z3::ast::Int::from_str(&ctx, &max.to_string()).unwrap()
            
                )
    }

}


fn get_z3_expression_int<'a>(ctx: &'a Context, expr: &Expression, signals_to_smt_symbols: &HashMap<usize, z3::ast::Int<'a>>) -> Result<z3::ast::Int<'a>, ()>{
    use Expression::*;
    use ExpressionInfixOpcode::*;
    use circom_algebra::num_traits::ToPrimitive;
    use circom_algebra::num_traits::pow;

        match expr{
            Number(_,v) => {
                Ok(z3::ast::Int::from_str(&ctx, &v.to_string()).unwrap())
            }
            Variable {name, ..} => {
                Ok(signals_to_smt_symbols.get(&name.parse::<usize>().unwrap()).unwrap().clone())
            }
            InfixOp { lhe, infix_op, rhe, .. } => {
                let l_string = get_z3_expression_int(ctx, lhe, signals_to_smt_symbols)?;
                let r_string = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols)?;

                match infix_op{
                    Mul => Ok(l_string * r_string),
                    Add => Ok(l_string + r_string),
                    Mod => Ok(l_string % r_string),
                    ShiftL => {
                        if rhe.is_number(){
                            match *rhe.clone(){
                                Expression::Number(_, value) => {
                                    let pow_value = pow(BigInt::from(2), value.to_usize().unwrap());
                                    Ok(l_string * z3::ast::Int::from_str(&ctx, &pow_value.to_string()).unwrap())
                                }
                                _ => {
                                    Err(())
                                }
                            }
                        } else{
                            Err(())
                        }
                        
                    },
                    ShiftR => {
                        if rhe.is_number(){
                            match *rhe.clone(){
                                Expression::Number(_, value) => {
                                    let pow_value = pow(BigInt::from(2), value.to_usize().unwrap());
                                    Ok(l_string / z3::ast::Int::from_str(&ctx, &pow_value.to_string()).unwrap())
                                }
                                _ => {
                                    Err(())
                                }
                            }
                        } else{
                            Err(())
                        }
                        
                    }
                    ExpressionInfixOpcode::Sub => Ok(l_string - r_string),
                    

                    ExpressionInfixOpcode::IntDiv => Ok(l_string / r_string),
                    _ => Err(()),
                }
        
            }
            PrefixOp {  prefix_op, rhe, .. } => {
                let r_string = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols)?;
                match prefix_op{
                    ExpressionPrefixOpcode::Sub => Ok(- r_string),
                    _ => Err(()),
                }
        
            }
            
            _ => { Err(()) }
        }
}

fn get_z3_expression_bool<'a>(ctx: &'a Context, expr: &Expression, signals_to_smt_symbols: &HashMap<usize, z3::ast::Int<'a>>) ->    Result<z3::ast::Bool<'a>, ()>{
    use Expression::*;
    use ExpressionInfixOpcode::*;
    use ExpressionPrefixOpcode::*;


        match expr{

            Number(_,v) => {
                if v == &BigInt::from(0){
                    Ok(z3::ast::Bool::from_bool(ctx, false))
                }else{
                    Ok(z3::ast::Bool::from_bool(ctx, true))
                }
            }
            Variable {name, ..} => {
                let signal_bool_rep = signals_to_smt_symbols.get(&name.parse::<usize>().unwrap()).unwrap().clone();
                Ok(!signal_bool_rep._eq(&z3::ast::Int::from_i64(&ctx, 0)))
            }

            InfixOp { lhe, infix_op, rhe, .. } => {
                match infix_op{
                    LesserEq => {
                        let l_string = get_z3_expression_int(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string.le(&r_string))
                    },
                    GreaterEq => {
                        let l_string = get_z3_expression_int(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string.ge(&r_string))
                    },
                    Lesser => {
                        let l_string = get_z3_expression_int(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string.lt(&r_string))
                    },
                    Greater => {
                        let l_string = get_z3_expression_int(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string.gt(&r_string))
                    },
                    Eq => {

                        let l_string_int = get_z3_expression_int(ctx, lhe, signals_to_smt_symbols);
                        let r_string_int = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols);
                        match (l_string_int, r_string_int){
                            (Ok(l_int), Ok(r_int)) => {
                                Ok(l_int._eq(&r_int))
                            }
                            _ => {
                                let l_string_bool = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                                let r_string_bool = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                                Ok(l_string_bool._eq(&r_string_bool))
                            }
                        }
                    },  
                    NotEq => {
                        let l_string_int = get_z3_expression_int(ctx, lhe, signals_to_smt_symbols);
                        let r_string_int = get_z3_expression_int(ctx, rhe, signals_to_smt_symbols);
                        match (l_string_int, r_string_int){
                            (Ok(l_int), Ok(r_int)) => {
                                
                                Ok(!l_int._eq(&r_int))
                            }
                            _ => {
                                let l_string_bool = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                                let r_string_bool = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                                Ok(!l_string_bool._eq(&r_string_bool))
                            }
                        }
                    },  
                    BoolOr => {
                        let l_string = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string | r_string)
                    },  
                    BoolAnd => {
                        let l_string = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string & r_string)
                    },  
                    BitOr => {
                        let l_string = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string | r_string)
                    },  
                    BitAnd => {
                        let l_string = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string & r_string)
                    },  
                    BoolImplication => {
                        let l_string = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                        let r_string = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                        Ok(l_string.implies(&r_string))
                    }, 
                    _ => Err(()),
                }
        
            }
            PrefixOp {  prefix_op, rhe, .. } => {
                let r_string = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                match prefix_op{
                    BoolNot => Ok(! r_string),
                    _ => Err(()),
                }
        
            }
            
            _ => {Err(()) }
        }
}

enum PossibleBounds{
    Signal(usize),
    Number(BigInt),
    NoBound,
}

fn get_bounds_expression_int(expr: &Expression) -> PossibleBounds{
    use Expression::*;


        match expr{
            Number(_,v) => {
                PossibleBounds::Number(v.clone())
            }
            Variable {name, ..} => {
                PossibleBounds::Signal(name.parse::<usize>().unwrap())
            } 
            
            _ => { PossibleBounds::NoBound}
        }
}



fn get_bounds_expression_bool(expr: &Expression, field: &BigInt) -> HashMap<usize, (BigInt, BigInt)>{
    use Expression::*;

    let mut map = HashMap::new();

    match expr{
            InfixOp { lhe, infix_op, rhe, .. } => {
                match infix_op{
                    ExpressionInfixOpcode::LesserEq => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, (v, field - 1));
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, (BigInt::from(0), v));
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::GreaterEq => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, (BigInt::from(0), v));
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, (v, field - 1));
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::Lesser => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, (v + 1, field - 1));
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, (BigInt::from(0), v - 1));
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::Greater => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, (BigInt::from(0), v - 1));
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, (v + 1, field - 1));
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::Eq => {

                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, (v.clone(), v));
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, (v.clone(), v));
                            },
                            _ =>{},
                        }
                    },  
                    ExpressionInfixOpcode::NotEq => {},  
                    ExpressionInfixOpcode::BoolOr => {
                        let bounds_l = get_bounds_expression_bool(lhe, field);
                        let bounds_r = get_bounds_expression_bool(rhe, field);
                        update_bounds_or(&mut map, bounds_l, bounds_r)
                    },  
                    ExpressionInfixOpcode::BoolAnd => {
                        let bounds_l = get_bounds_expression_bool(lhe, field);
                        let bounds_r = get_bounds_expression_bool(rhe, field);
                        update_bounds_and(&mut map, bounds_l, bounds_r)
                    },  
                    ExpressionInfixOpcode::BitOr => {
                        let bounds_l = get_bounds_expression_bool(lhe, field);
                        let bounds_r = get_bounds_expression_bool(rhe, field);
                        update_bounds_or(&mut map, bounds_l, bounds_r)
                    },  
                    ExpressionInfixOpcode::BitAnd => {
                        let bounds_l = get_bounds_expression_bool(lhe, field);
                        let bounds_r = get_bounds_expression_bool(rhe, field);
                        update_bounds_and(&mut map, bounds_l, bounds_r)
                    },  
                    _ => {},
                }
        
            },
            _  => {}
    }
    map
    
}

fn update_bounds_or(map: &mut HashMap<usize, (BigInt, BigInt)>, left: HashMap<usize, (BigInt, BigInt)>, right: HashMap<usize, (BigInt, BigInt)>){
    use std::cmp::min;
    for (s, (min_l, max_l)) in left{
        match right.get(&s){
            Some((min_r, max_r)) =>{
                map.insert(s, (max(min_l, min_r.clone()), min(max_l, max_r.clone())));
            },
            None =>{

            },
        }
    }
}


fn update_bounds_and(map: &mut HashMap<usize, (BigInt, BigInt)>, left: HashMap<usize, (BigInt, BigInt)>, right: HashMap<usize, (BigInt, BigInt)>){
    use std::cmp::min;
    for (s, (min_l, max_l)) in left{
        map.insert(s, (min_l, max_l));
    }
    for (s, (min_r, max_r)) in right{
        match map.get(&s){
            Some((min_l, max_l)) =>{
                map.insert(s, (max(min_l.clone(), min_r), min(max_l.clone(), max_r)));
            },
            None =>{
                map.insert(s, (min_r, max_r));
            }
        }
    }


}
