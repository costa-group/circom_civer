use std::{cmp::max, collections::{HashMap, LinkedList}};
use std::sync::atomic::AtomicBool;
use num_bigint_dig::BigInt;
use crate::{PossibleResult, SafetyVerification};

use circom_algebra::{modular_arithmetic, algebra::{
    Constraint, ExecutedInequation}};

use super::safety_z3::try_prove_safety_with_z3;
use super::safety_z3::try_prove_safety_with_z3_cancel;



fn is_positive(a: &BigInt, field: &BigInt) -> bool{
    a <= &(field / BigInt::from(2))
}

pub type Signal2Bounds = HashMap<usize, ExecutedInequation<usize>>;

pub struct TemplateVerification {
    pub template_name: String,
    pub signals: LinkedList<usize>,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
    pub constraints: Vec<Constraint<usize>>,
    pub implications_safety: Vec<(Vec<usize>, Vec<usize>)>,
    pub deductions: Signal2Bounds,
    pub substitutions: HashMap<usize, usize>,
    pub field: BigInt,
    pub verbose: bool,
    pub verification_timeout: u64,
    pub apply_deduction_assigned: bool,
}

impl TemplateVerification{

    pub fn new(
        problem: &SafetyVerification,
    ) -> TemplateVerification {

        let mut substitutions = HashMap::new();
        for s in &problem.signals{
            substitutions.insert(*s, *s);
        }

        TemplateVerification {
            template_name: problem.template_name.clone(),
            signals: problem.signals.clone(),
            inputs: problem.inputs.clone(),
            outputs: problem.outputs.clone(), 
            implications_safety: problem.implications_safety.clone(),
            deductions: HashMap::new(),
            substitutions,
            constraints: problem.constraints.clone(),
            field: problem.field.clone(),
            verbose: false,      
            verification_timeout: problem.verification_timeout, 
            apply_deduction_assigned: problem.apply_deduction_assigned,
        }
    }

    pub fn initialize_bounds_preconditions(&mut self){
        self.deductions.insert(0, ExecutedInequation{signal: 0, min: BigInt::from(1), max: BigInt::from(1)});

    }


    pub fn deduce(&mut self)-> (PossibleResult, Vec<String>) {        //self.print_pretty_template_verification();
        
        //self.deduce_round();
        //self.normalize();

        let mut logs = Vec::new();

        let result_safety = self.try_prove_safety(&mut logs);

        (result_safety, logs)
    }

    pub fn deduce_with_cancel(&mut self, cancel_flag: &AtomicBool)-> (PossibleResult, Vec<String>) {
        let mut logs = Vec::new();

        let result_safety = self.try_prove_safety_with_cancel(&mut logs, cancel_flag);

        (result_safety, logs)
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


     // normalizes the constraints choosing the smaller coefficients
    pub fn normalize(&mut self){
        let old_constraints = std::mem::take(&mut self.constraints);
        for c in old_constraints{
            let new_c = normalize_constraint(c, &self.deductions, &self.field);
            self.constraints.push(new_c);
        }
    }


    pub fn try_prove_safety(&mut self, logs: &mut Vec<String>) -> PossibleResult{
        let signals_vec = self.signals.iter().cloned().collect::<Vec<_>>();

        self.deduce_round();
        try_prove_safety_with_z3(
                &self.inputs,
                &self.outputs,
                &signals_vec,
                &self.constraints,
                &self.implications_safety,
                &self.deductions,
                &self.field,
                self.verification_timeout,
                self.apply_deduction_assigned,
                logs,
        )
    }

    pub fn try_prove_safety_with_cancel(&mut self, logs: &mut Vec<String>, cancel_flag: &AtomicBool) -> PossibleResult{
        let signals_vec = self.signals.iter().cloned().collect::<Vec<_>>();

        self.deduce_round();
        try_prove_safety_with_z3_cancel(
                &self.inputs,
                &self.outputs,
                &signals_vec,
                &self.constraints,
                &self.implications_safety,
                &self.deductions,
                &self.field,
                self.verification_timeout,
                self.apply_deduction_assigned,
                logs,
                cancel_flag,
        )
    }
}


pub fn update_bounds_signal(deductions: &mut Signal2Bounds, signal: usize, min: BigInt, max: BigInt, field: &BigInt) -> bool{
    let pos_bounds = deductions.get_mut(&signal);

    if &min >= &BigInt::from(0) && &max <= &(field - &BigInt::from(1)){
        match pos_bounds{
            Option::None => {
    
                deductions.insert(
                    signal,
                    ExecutedInequation{signal, min, max}
                );
                true
            }
            
    
            Option::Some(bounds) => {
                if !(&bounds.min <= &BigInt::from(0) && &max >= &(field - &BigInt::from(1))){
                    bounds.update_bounds(min, max)
                } else{
                    false
                }
            }
       }
    } else{
        false
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

pub fn compute_bounds_linear_expression_strict(deductions: &Signal2Bounds, le: &HashMap<usize, BigInt>, field: &BigInt) -> (BigInt, BigInt){
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

pub fn compute_bounds_product(min_1: &BigInt, max_1: &BigInt, min_2: &BigInt, max_2: &BigInt)-> (BigInt, BigInt){
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
    _verbose: bool,
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

    
    let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression(deductions, &c, field);

    let lower_limit = lower_limit_c - upper_limit_ab;
    let upper_limit = upper_limit_c - lower_limit_ab;

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
                if update_bounds_signal(deductions, *signal, field - pos_min, pos_max, field){
                    updated_signals.push(signal.clone());
                }
            }
        }
        
    }
    updated_signals
}












pub fn compute_upper_lower_bounds(c: &Constraint<usize>, bounds: &HashMap<usize, ExecutedInequation<usize>>, field: &BigInt) -> (BigInt, BigInt) {
    let a = c.a();
    let b = c.b();
    let c = c.c();
    
    
    let (lower_limit_a, upper_limit_a) = compute_bounds_linear_expression_strict(bounds, &a, field);
    let (lower_limit_b, upper_limit_b) = compute_bounds_linear_expression_strict(bounds, &b, field);

    let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
        &lower_limit_a, 
        &upper_limit_a, 
        &lower_limit_b, 
        &upper_limit_b
    );

 
    let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression_strict(bounds, &c, field);
    
    (&lower_limit_c - &upper_limit_ab, &upper_limit_c - &lower_limit_ab) // lower and upper bounds

}  


pub fn normalize_constraint(c: Constraint<usize>, bounds: &HashMap<usize, ExecutedInequation<usize>>, field: &BigInt) -> Constraint<usize>{
    // to consider all possible normalizations
    use circom_algebra::algebra::ArithmeticExpression;
    let c_elements = c.c();
    //println!("Normalizing constraint");
    //c.print_pretty_constraint();    
    let (initial_lower, initial_upper) = compute_upper_lower_bounds(&c, bounds, field);
    let mut best_difference = initial_upper - initial_lower;
    let mut best_c = c.clone();
    
    // try to normalize using all elements in C
    for (_signal, coef) in c_elements{
        // divide by the coef to get the new constraint
        let mut new_c_a = c.a().clone();
        let new_c_b = c.b().clone();
        let mut new_c_c = c.c().clone();

        let _ = ArithmeticExpression::divide_coefficients_by_constant(
                coef,
            &mut new_c_a,
                field,
            );
        let _ = ArithmeticExpression::divide_coefficients_by_constant(
                coef,
            &mut new_c_c,
                field,
            );
        
        let new_c = Constraint::new(new_c_a, new_c_b, new_c_c);
        let (new_lower, new_upper) = compute_upper_lower_bounds(&new_c, bounds, field);
        let new_dif = new_upper - new_lower;
        if new_dif < best_difference{
            best_difference = new_dif;
            best_c = new_c.clone();
        }
    }
    //println!("Chosen representative");
    //best_c.print_pretty_constraint();    

    best_c
}
