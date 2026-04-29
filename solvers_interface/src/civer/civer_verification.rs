use std::collections::{HashMap, LinkedList};
use program_structure::ast::{Expression, ExpressionInfixOpcode, ExpressionPrefixOpcode};
use crate::{CompleteVerificationResult, ExecutedImplication, PossibleResult, SafetyImplication};
use rand::Rng;
use circom_algebra::num_bigint::BigInt;
use crate::Constraint;
use std::fs::File;
use std::io::Write;

use crate::civer::expression_handler::get_bounds_expression_bool;
use crate::civer::deduction_rules::*;


use crate::VerificationProblem;

        use z3::Config;
        use z3::Context;
        use z3::Solver;
        use z3::ast::Ast;
        use z3::*;


#[derive(Clone)]
pub struct Bounds {
    pub min: BigInt,
    pub max: BigInt
}

pub fn update_bounds(bounds: &mut Bounds, new_bounds: &Bounds)-> bool{
    let mut updated = false;
    if new_bounds.min > bounds.min{
        bounds.min = new_bounds.min.clone();
        updated = true;
    }
    if new_bounds.max < bounds.max{
        bounds.max = new_bounds.max.clone();
        updated = true;
    }
    assert!(new_bounds.min >= BigInt::from(0));
    assert!(new_bounds.max >= BigInt::from(0));

    updated
}



pub type Signal2Bounds = HashMap<usize, Bounds>;

pub fn update_bounds_signal(deductions: &mut Signal2Bounds, signal: usize, bounds: &Bounds, field: &BigInt) -> bool{
    let pos_bounds = deductions.get_mut(&signal);

    if bounds.min >= BigInt::from(0) && bounds.max <= (field - &BigInt::from(1)){
        match pos_bounds{
            None => {
                deductions.insert(
                    signal,
                    bounds.clone()
                );
                true
            }
            Some(prev_bounds) => {
                if !(&prev_bounds.min <= &BigInt::from(0) && &prev_bounds. max >= &(field - &BigInt::from(1))){
                    update_bounds(prev_bounds, & bounds)
                } else{
                    false
                }
            }
       }
    } else{
        false
    }
}


pub struct TemplateVerification {
    pub template_name: String,
    pub signals: LinkedList<usize>,
    pub initial_signal: usize,
    pub number_outputs: usize,
    pub number_inputs: usize,
    pub preconditions: Vec<Expression>,
    pub postconditions : Vec<Expression>,
    pub constraints: Vec<Constraint>,
    pub implications_correctness: Vec<ExecutedImplication>,
    pub implications_safety: Vec<SafetyImplication>,
    pub deductions: Signal2Bounds,
    pub field: BigInt,
    pub verbose: bool,
    pub verification_timeout: u64,
    pub check_tags: bool,
    pub check_safety: bool,
}

impl TemplateVerification{

    pub fn new(
        problem: &VerificationProblem
    ) -> TemplateVerification {
        let mut fixed_constraints = Vec::new();
        for c in &problem.constraints{
            let mut new_c = c.clone();
            Constraint::fix_constraint(&mut new_c, &problem.field);
            fixed_constraints.push(new_c);
        }
        let mut substitutions = HashMap::new();
        for s in &problem.signals{
            substitutions.insert(*s, *s);
        }

        let mut postconditions = problem.specification_intermediates.clone();
        postconditions.append(&mut problem.specification_postconditions.clone());
        TemplateVerification {
            template_name: problem.template_name.clone(),
            signals: problem.signals.clone(),
            initial_signal: problem.initial_signal,
            number_inputs: problem.number_inputs,
            number_outputs: problem.number_outputs,
            preconditions: problem.specification_preconditions.clone(),
            postconditions,
            implications_correctness: problem.tags_implications.clone(),
            implications_safety: problem.implications_safety.clone(),
            deductions: HashMap::new(),
            constraints: fixed_constraints,
            field: problem.field.clone(),
            verbose: problem.config.verbose,      
            verification_timeout: problem.config.verification_timeout, 
            check_tags: problem.config.check_tags, 
            check_safety: problem.config.check_safety,
        }
    }

    pub fn initialize_bounds_preconditions(&mut self){

        self.deductions.insert(0, Bounds{ min: BigInt::from(1), max: BigInt::from(1)});
        
        for expr in &self.preconditions{
            let possible_bounds = get_bounds_expression_bool(expr, &self.field);
            for(signal, bounds) in possible_bounds{
                update_bounds_signal(&mut self.deductions, signal, &bounds, &self.field);
            }
            
        }


    }


    pub fn deduce(&mut self)-> CompleteVerificationResult {        //self.print_pretty_template_verification();
        
        self.deduce_round();
        let mut logs = Vec::new();

        let tags_result = if self.check_tags{
            if self.postconditions.is_empty() {
                logs.push(format!("### NOTHING TO VERIFY: THE TEMPLATE DOES NOT CONTAIN TAGGED SIGNALS WITH SPECIFICATIONS \n"));
                Some(PossibleResult::NOTHING)
            } else{
                Some(self.try_prove_tags(&mut logs))
            }
        } else{
            None
        };

        let safety_result = if self.check_safety{
            Some(self.try_prove_safety(&mut logs))
        } else{
            None
        };

        CompleteVerificationResult { safety_result, tags_result, logs }
    }

    // normalizes the constraints choosing the smaller coefficients
    // pub fn normalize(&mut self){
    //     let old_constraints = std::mem::take(&mut self.constraints);
    //     for c in old_constraints{
    //         let new_c = normalize_constraint(c, &self.deductions, &self.field);
    //         self.constraints.push(new_c);
    //     }
    // }

    // returns the signals where it was able to find new bounds
    pub fn deduce_round(&mut self){

        self.initialize_bounds_preconditions();

        let filter_const = std::mem::take(&mut self.constraints);

        for c in filter_const{
            let (_updated, should_remove) = deduction_rule_integrity_domain(&mut self.deductions, &c, &self.field); 
            if !should_remove{ 
                self.constraints.push(c);
            }
        } 

        let mut updated_bounds = true;

        while updated_bounds{
            updated_bounds = false;
            for c in &self.constraints{
                updated_bounds |= deduction_rule_apply_bounds_constraint(&mut self.deductions, &c, &self.field, self.verbose);
            }
        }
        
    }


    pub fn try_prove_tags(&self, logs: &mut Vec<String>)-> PossibleResult{
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

        solver.assert(&value_preconditions);


        let mut i = 0;
        for constraint in &self.constraints{
            insert_constraint_in_smt(constraint, &ctx, &solver, &aux_signals_to_smt_rep, &self.field, 
                                        &self.deductions, i, &field, self.verbose);
            i = i + 1;
        }


        for implication in &self.implications_correctness{
            insert_implication_in_smt(implication, &ctx, &solver, &aux_signals_to_smt_rep, &self.field);
        }


        let mut value_postconditions = z3::ast::Bool::from_bool(&ctx, true);
        for postcondition in &self.postconditions{
            value_postconditions &= get_z3_expression_bool(&ctx, &postcondition, &aux_signals_to_smt_rep).unwrap();
        }


        solver.assert(&!value_postconditions);

        if self.verbose{
            
            let mut rng = rand::thread_rng();
            let random_number: u32 = rng.gen();
            let short_filename = self.template_name.split("(").next().unwrap();
            let new_file_name: String = format!("{}_{}.smt2", short_filename,random_number);
            let mut file: File = File::create(&new_file_name).expect("Unable to create SMT2 file");
            file.write_all(format!("{}",solver).as_bytes()).expect("Unable to write SMT2 file");
        
            file.sync_all().expect("Failed to sync SMT2 file to disk");
            file.flush().expect("Failed to flush SMT2 file");
            // `file` dropped here
    
        }

        match solver.check(){
            SatResult::Sat =>{
                logs.push(format!("### THE VERIFICATION OF THE TAGS OF THE TEMPLATE FAILED. FOUND COUNTEREXAMPLE USING SMT:\n"));
                //if self.verbose{

                 let model = solver.get_model().unwrap();
                 for s in &self.signals{
                     let v = model.eval(aux_signals_to_smt_rep.get(s).unwrap(), true).unwrap();
                     logs.push(format!("Signal {}: {}\n", s, v.to_string()));
                 }
                //}
                PossibleResult::FAILED
            },
            SatResult::Unsat =>{
                logs.push(format!("### SUCCESS: THE TAGS OF THE TEMPLATE ARE VERIFIED\n"));
                PossibleResult::VERIFIED
            },
            _=> {
                logs.push(format!("### UNKNOWN: VERIFICATION OF THE TAGS TIMEOUT\n"));
                PossibleResult::UNKNOWN
            }
        }
    }

    

    pub fn try_prove_safety(&self, logs: &mut Vec<String>) -> PossibleResult{
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

        apply_deduction_assigned(
                &self.constraints, 
                &ctx, 
                &solver, 
                &aux_signals_to_smt_rep, 
                &aux_signals_to_smt_rep_aux
            );
        


        for implication in &self.implications_safety{
            let mut implication_left = z3::ast::Bool::from_bool(&ctx, true);
            for s in &implication.left{
                let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
                let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
                implication_left &= s_1._eq(s_2);
            }
            let mut implication_right = z3::ast::Bool::from_bool(&ctx, true);
            for s in &implication.right{
                let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
                let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
                implication_right &= s_1._eq(s_2);
            }

            solver.assert(&implication_left.implies(&implication_right));
        }

        let mut all_outputs_equal = z3::ast::Bool::from_bool(&ctx, true);
        for s in 0..self.number_outputs{
            let s_1 = aux_signals_to_smt_rep.get(&(self.initial_signal + s)).unwrap();
            let s_2 = aux_signals_to_smt_rep_aux.get(&(self.initial_signal + s)).unwrap();
            all_outputs_equal &= s_1._eq(s_2);
        } 
        solver.assert(&!all_outputs_equal);

        if self.verbose{
            
            let mut rng = rand::thread_rng();
            let random_number: u32 = rng.gen();
            let short_filename = self.template_name.split("(").next().unwrap();
            let new_file_name: String = format!("{}_{}.smt2", short_filename,random_number);
            let mut file: File = File::create(&new_file_name).expect("Unable to create SMT2 file");
            file.write_all(format!("{}",solver).as_bytes()).expect("Unable to write SMT2 file");
        
            file.sync_all().expect("Failed to sync SMT2 file to disk");
            file.flush().expect("Failed to flush SMT2 file");
            // `file` dropped here
    
        }
        
        match solver.check(){
            SatResult::Sat =>{
                logs.push(format!("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"));

                let model = solver.get_model().unwrap();
                for s in 0..self.number_inputs{
                    let v = model.eval(aux_signals_to_smt_rep.get(&(self.initial_signal + self.number_outputs + s)).unwrap(), true).unwrap();
                    logs.push(format!("Input signal {}: {}\n", self.initial_signal + self.number_outputs + s, v.to_string()));

                }
                for s in 0..self.number_outputs{
                    let v = model.eval(aux_signals_to_smt_rep.get(&(self.initial_signal + s)).unwrap(), true).unwrap();
                    let v1 = model.eval(aux_signals_to_smt_rep_aux.get(&(self.initial_signal + s)).unwrap(), true).unwrap();

                    logs.push(format!("Output signal {}: values {} | {}\n", self.initial_signal + s, v.to_string(), v1.to_string()));

                }

                PossibleResult::FAILED
                //}
            },
            SatResult::Unsat =>{
                logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
                PossibleResult::VERIFIED
            },
            _=> {
                logs.push(format!("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n"));
                PossibleResult::UNKNOWN
            }
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

pub fn apply_deduction_assigned(
    constraints: &Vec<Constraint>,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>,
    signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>,
) {
    for c in constraints{
        let all_signals = c.take_signals();
        let only_linear_signals = c.take_only_linear_signals();

        // in case there are signals that are only_linear 
        for s_deduced in only_linear_signals{
            
            // Generate the implication all signals in C are deterministic
            //  => s_deduced is deterministic
            
            let value_right_1 = signals_to_smt_symbols_1.get(s_deduced).unwrap();
            let value_right_2 = signals_to_smt_symbols_2.get(s_deduced).unwrap();
            let right_side = value_right_1._eq(&value_right_2);

            let mut left_side = z3::ast::Bool::from_bool(&ctx, true);
            
            for s in &all_signals{
                if *s != s_deduced{
                    let value_s_1 = signals_to_smt_symbols_1.get(s).unwrap();
                    let value_s_2 = signals_to_smt_symbols_2.get(s).unwrap();
                    let new_left_side = value_s_1._eq(&value_s_2);

                    left_side &= new_left_side;
                }
            }

            let mut value_cond = !left_side;
            value_cond |=  &right_side;
            solver.assert(&value_cond);
        }
    }
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

pub fn insert_constraint_in_smt(
    constraint: &Constraint,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols: &HashMap<usize, z3::ast::Int>,
    field: &BigInt,
    deductions: &Signal2Bounds,
    num_k : usize,
    p : &z3::ast::Int,
    _verbose: bool,
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
    let bounds_a = compute_bounds_linear_expression(deductions, &a, field);
    let bounds_b = compute_bounds_linear_expression(deductions, &b, field);

    let bounds_ab = compute_bounds_product(
        &bounds_a, 
        &bounds_b,
    );

 
    let bounds_c = compute_bounds_linear_expression(deductions, &c, field);

    fn compute_limits_overflows_k(bounds: &Bounds, field: &BigInt)->(BigInt, BigInt){
        let lower_limit_k = &bounds.min / field;
        let upper_limit_k = if &bounds.max / field > BigInt::from(0) && &bounds.max%field != BigInt::from(0) {
            &bounds.max/field + BigInt::from(1)
        } else{
            &bounds.max/field
        };
        (lower_limit_k, upper_limit_k)
    }
    

    let bounds_dif = Bounds{
        min: &bounds_c.min - &bounds_ab.max,
        max: &bounds_c.max - &bounds_ab.min
    };

    let (lower_limit_k, upper_limit_k) = compute_limits_overflows_k(&bounds_dif, field);
    let (lower_limit_k_a, upper_limit_k_a) = compute_limits_overflows_k(&bounds_a, field);
    let (lower_limit_k_b, upper_limit_k_b) = compute_limits_overflows_k(&bounds_b, field);
    let (lower_limit_k_c, upper_limit_k_c) = compute_limits_overflows_k(&bounds_c, field);


    // Apply transformation rule A * B = 0 => (A = 0) \/ (B = 0)
    if &bounds_c.min == &bounds_c.max && &bounds_c.max == &BigInt::from(0) {
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

                    ExpressionInfixOpcode::Eq => {
                        let is_eq = l_string._eq(&r_string);
                        Ok(is_eq.ite(&z3::ast::Int::from_i64(&ctx, 1), &z3::ast::Int::from_i64(&ctx, 0)))
                    }
                   
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
                    // BoolImplication => {
                    //     let l_string = get_z3_expression_bool(ctx, lhe, signals_to_smt_symbols)?;
                    //     let r_string = get_z3_expression_bool(ctx, rhe, signals_to_smt_symbols)?;
                    //     Ok(l_string.implies(&r_string))
                    // }, 
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


// pub fn compute_upper_lower_bounds(c: &Constraint<usize>, bounds: &HashMap<usize, ExecutedInequation<usize>>, field: &BigInt) -> (BigInt, BigInt) {
//     let a = c.a();
//     let b = c.b();
//     let c = c.c();
    
    
//     let (lower_limit_a, upper_limit_a) = compute_bounds_linear_expression_strict(bounds, &a, field);
//     let (lower_limit_b, upper_limit_b) = compute_bounds_linear_expression_strict(bounds, &b, field);

//     let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
//         &lower_limit_a, 
//         &upper_limit_a, 
//         &lower_limit_b, 
//         &upper_limit_b
//     );

 
//     let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression_strict(bounds, &c, field);
    
//     (&lower_limit_c - &upper_limit_ab, &upper_limit_c - &lower_limit_ab) // lower and upper bounds

// }  


// pub fn normalize_constraint(c: Constraint<usize>, bounds: &HashMap<usize, ExecutedInequation<usize>>, field: &BigInt) -> Constraint<usize>{
//     // to consider all possible normalizations
//     use circom_algebra::algebra::ArithmeticExpression;
//     let c_elements = c.c();
//     //println!("Normalizing constraint");
//     //c.print_pretty_constraint();    
//     let (initial_lower, initial_upper) = compute_upper_lower_bounds(&c, bounds, field);
//     let mut best_difference = initial_upper - initial_lower;
//     let mut best_c = c.clone();
    
//     // try to normalize using all elements in C
//     for (_signal, coef) in c_elements{
//         // divide by the coef to get the new constraint
//         let mut new_c_a = c.a().clone();
//         let new_c_b = c.b().clone();
//         let mut new_c_c = c.c().clone();

//         ArithmeticExpression::divide_coefficients_by_constant(
//                 coef,
//             &mut new_c_a,
//                 field,
//             );
//         ArithmeticExpression::divide_coefficients_by_constant(
//                 coef,
//             &mut new_c_c,
//                 field,
//             );
        
//         let new_c = Constraint::new(new_c_a, new_c_b, new_c_c);
//         let (new_lower, new_upper) = compute_upper_lower_bounds(&new_c, bounds, field);
//         let new_dif = new_upper - new_lower;
//         if new_dif < best_difference{
//             best_difference = new_dif;
//             best_c = new_c.clone();
//         }
//     }
//     //println!("Chosen representative");
//     //best_c.print_pretty_constraint();    

//     best_c
// }