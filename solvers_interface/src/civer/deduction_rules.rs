use crate::civer::civer_verification::{Signal2Bounds, Bounds, update_bounds_signal};
use crate::Constraint;
use circom_algebra::{num_bigint::BigInt, modular_arithmetic};
use std::cmp::{max, min};
use std::collections::HashMap;





pub fn deduction_rule_integrity_domain(
    deductions: &mut Signal2Bounds,
    constraint: &Constraint, 
    field: &BigInt
) -> (bool, bool){
    let mut completely_studied = false;
    let mut updated = false;
    
    let a = constraint.a();
    let b = constraint.b();
    let c = constraint.c();

    if let Option::Some((a_signal, a_value)) = solve_signal_plus_coef(a, field) {
        if let Option::Some((b_signal, b_value)) = solve_signal_plus_coef(b, field) {
            if a_signal == b_signal && c.is_empty() {

                let bounds = if a_value > b_value{
                    Bounds{
                        min: b_value,
                        max: a_value
                    }
                } else{
                    Bounds{
                        min: a_value,
                        max: b_value
                    }
                };
                completely_studied = &bounds.max - &bounds.min == BigInt::from(1);
                updated = update_bounds_signal(deductions, a_signal, &bounds, field);      

            }
        }
    }
    (updated, completely_studied)
}

pub fn deduction_rule_apply_bounds_constraint(
    deductions: &mut Signal2Bounds,
    constraint: &Constraint,
    field: &BigInt, 
    _verbose: bool,
)-> bool {

    let a = constraint.a();
    let b = constraint.b();
    let c = constraint.c();

    let bounds_a = compute_bounds_linear_expression(deductions, &a, field);
    let bounds_b = compute_bounds_linear_expression(deductions, &b, field);

    let bounds_ab = compute_bounds_product(
        &bounds_a, 
        &bounds_b
    );

    
    let bounds_c = compute_bounds_linear_expression(deductions, &c, field);

    let lower_limit = bounds_c.min - bounds_ab.max;
    let upper_limit = bounds_c.max - bounds_ab.min;

    let mut updated = false;

    for (signal, coef) in c{
        if coef == &BigInt::from(1) || *coef == field - &BigInt::from(1) {
            let (min, max) = if deductions.contains_key(signal){
                let bounds = deductions.get(signal).unwrap();
                (bounds.min.clone(), bounds.max.clone())
            } else{
                (BigInt::from(0), field - BigInt::from(1))
            };
            let (pos_max, pos_min);
            let (valid_bounds, _valid_consecutive) = if coef == &BigInt::from(1){
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
                let bounds = Bounds{
                    min: pos_min,
                    max: pos_max
                };
                updated |= update_bounds_signal(deductions, *signal, &bounds, field);
            }
            // else if false && valid_consecutive{
            //     if update_bounds_signal(deductions, *signal, field - pos_min, pos_max, field){
            //         updated_signals.push(signal.clone());
            //     }
            // }
        }
        
    }
    updated
}



// pub fn apply_deduction_rule_homologues(
//     constraints: &Vec<Constraint<usize>>,
//     ctx: &Context,
//     solver: &Solver,
//     signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>,
//     signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>,
//     deductions: &Signal2Bounds,
//     field: &BigInt,
//     p : &z3::ast::Int,
// ){
//     for c in constraints{
//         let mut value_a = z3::ast::Int::from_u64(ctx, 0);
//         let mut value_b = z3::ast::Int::from_u64(ctx, 0);
//         let mut value_c = z3::ast::Int::from_u64(ctx, 0);

//         let mut value_a1 = z3::ast::Int::from_u64(ctx, 0);
//         let mut value_b1 = z3::ast::Int::from_u64(ctx, 0);
//         let mut value_c1 = z3::ast::Int::from_u64(ctx, 0);

//         for (signal, value) in c.a(){
//             if *signal == 0{
//                 value_a += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//                 value_a1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();         
//             } else{
//                 value_a += signals_to_smt_symbols_1.get(signal).unwrap() *
//                     &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//                 value_a1 += signals_to_smt_symbols_2.get(signal).unwrap() *
//                     &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//             }
//         }
//         for (signal, value) in c.b(){
//             if *signal == 0{
//                 value_b += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//                 value_b1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();

//             } else{
//                 value_b += signals_to_smt_symbols_1.get(signal).unwrap() *
//                     &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//                 value_b1 += signals_to_smt_symbols_2.get(signal).unwrap() *
//                     &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//             }
//         }
//         for (signal, value) in c.c(){
//             if *signal == 0{
//                 value_c += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//                 value_c1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();

//             } else{
//                 value_c += signals_to_smt_symbols_1.get(signal).unwrap() *
//                     &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//                 value_c1 += signals_to_smt_symbols_2.get(signal).unwrap() *
//                     &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
//             }
//         }


//         let c_a = c.a();
//         let c_b = c.b();
//         let c_c = c.c();
//         let (lower_limit_a, upper_limit_a) = compute_bounds_linear_expression_strict(deductions, &c_a, field);
//         let (lower_limit_b, upper_limit_b) = compute_bounds_linear_expression_strict(deductions, &c_b, field);
//         let (lower_limit_c, upper_limit_c) = compute_bounds_linear_expression_strict(deductions, &c_c, field);
    
//         let lower_limit_k_aa =  (&lower_limit_a - &upper_limit_a)/field;
//         let upper_limit_k_aa = if (&upper_limit_a - &lower_limit_a)/field > BigInt::from(0) && (&upper_limit_a - &lower_limit_a)%field != BigInt::from(0) {
//             (&upper_limit_a - &lower_limit_a)/field + BigInt::from(1)
//         } else{
//             (&upper_limit_a - &lower_limit_a)/field
//         };

//         let lower_limit_k_bb =  (&lower_limit_b - &upper_limit_b)/field;
//         let upper_limit_k_bb = if (&upper_limit_b - &lower_limit_b)/field > BigInt::from(0) && (&upper_limit_b - &lower_limit_b)%field != BigInt::from(0) {
//             (&upper_limit_b - &lower_limit_b)/field + BigInt::from(1)
//         } else{
//             (&upper_limit_b - &lower_limit_b)/field
//         };

//         let lower_limit_k_cc =  (&lower_limit_c - &upper_limit_c)/field;
//         let upper_limit_k_cc = if (&upper_limit_c - &lower_limit_c)/field > BigInt::from(0) && (&upper_limit_c - &lower_limit_c)%field != BigInt::from(0) {
//             (&upper_limit_c - &lower_limit_c)/field + BigInt::from(1)
//         } else{
//             (&upper_limit_c - &lower_limit_c)/field
//         };

//         let zero = z3::ast::Int::from_u64(&ctx, 0);
        
//         let condition_aa = if lower_limit_k_aa == upper_limit_k_aa{
//             let value_left = &value_a - &value_a1;
//             let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_aa.to_string()).unwrap() * p;
//             value_left._eq(&value_right)
//         } else{
//             (&value_a - &value_a1).modulo(&p)._eq(&zero)
//         };
//         let condition_bb = if lower_limit_k_bb == upper_limit_k_bb{
//             let value_left = &value_b - &value_b1;
//             let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_bb.to_string()).unwrap() * p;
//             value_left._eq(&value_right)
//         } else{
//             (&value_b - &value_b1).modulo(&p)._eq(&zero)
//         };
//         let condition_cc = if lower_limit_k_cc == upper_limit_k_cc{
//             let value_left = &value_c - &value_c1;
//             let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_cc.to_string()).unwrap() * p;
//             value_left._eq(&value_right)
//         } else{
//             (&value_c - &value_c1).modulo(&p)._eq(&zero)
//         };

//         let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
//         value_cond |= !&condition_aa;
//         value_cond |=  !&condition_bb;
//         value_cond |=  &condition_cc;
//         solver.assert(&value_cond);

//         let lower_limit_k_a =  &lower_limit_a /field;
//         let upper_limit_k_a = if &upper_limit_a /field > BigInt::from(0) && &upper_limit_a%field != BigInt::from(0) {
//             &upper_limit_a /field + BigInt::from(1)
//         } else{
//             &upper_limit_a/field
//         };

//         let condition_a_not_zero = if lower_limit_k_a == upper_limit_k_a{
//             let value_left = &value_a;
//             let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_a.to_string()).unwrap() * p;
//             !value_left._eq(&value_right)
//         } else{
//             !&value_a.modulo(&p)._eq(&zero)
//         };
        
//         let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
//         value_cond |= !(&condition_aa & &condition_a_not_zero);
//         value_cond |=  !&condition_cc;
//         value_cond |=  &condition_bb;
//         solver.assert(&value_cond);

//         let lower_limit_k_b =  &lower_limit_b /field;
//         let upper_limit_k_b = if &upper_limit_b /field > BigInt::from(0) && &upper_limit_b%field != BigInt::from(0) {
//             &upper_limit_b /field + BigInt::from(1)
//         } else{
//             &upper_limit_b/field
//         };

//         let condition_b_not_zero = if lower_limit_k_b == upper_limit_k_b{
//             let value_left = &value_b;
//             let value_right = z3::ast::Int::from_str(ctx, &lower_limit_k_b.to_string()).unwrap() * p;
//             !value_left._eq(&value_right)
//         } else{
//             !&value_b.modulo(&p)._eq(&zero)
//         };  
//         let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
//         value_cond |= !(&condition_bb & condition_b_not_zero);
//         value_cond |=  !&condition_cc;
//         value_cond |=  &condition_aa;
//         solver.assert(&value_cond);

//     }

    

// }



/////////////// AUXILIAR FUNCIONTS



fn is_positive(a: &BigInt, field: &BigInt) -> bool{
    a <= &(field / BigInt::from(2))
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

fn check_correct_signs(a: &BigInt, b: &BigInt)-> bool{
    // revisar esta también
    let zero = &BigInt::from(0);
    !(a >= zero && b < zero) && !(b >= zero && a < zero) 
}

pub fn compute_bounds_linear_expression(deductions: &Signal2Bounds, le: &HashMap<usize, BigInt>, field: &BigInt) -> Bounds{
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
    Bounds { min: lower_limit, max: upper_limit }
}

/* 
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
}*/

pub fn compute_bounds_product(bounds_1: &Bounds, bounds_2: &Bounds)-> Bounds{
    let zero = &BigInt::from(0);
    if &bounds_1.min >= zero { // bounds_1 are positive
        if &bounds_2.min >= zero { // bounds_2 are two-positive
            Bounds { min: &bounds_1.min * &bounds_2.min, max: &bounds_1.max * &bounds_2.max }
        } else if &bounds_2.max >= zero { // bounds_2 are neg/pos
            Bounds { min: &bounds_1.max * &bounds_2.min, max: &bounds_1.max * &bounds_2.max }
        } else { // bounds_2 are two_negative
            Bounds { min: &bounds_1.max * &bounds_2.min, max: &bounds_1.min * &bounds_2.max }
        }
    } else if &bounds_1.max >= zero { // bounds_1 are neg/pos
        if &bounds_2.min >= zero { // bounds_2 are two-positive
            Bounds { min: &bounds_1.min * &bounds_2.max, max: &bounds_1.max * &bounds_2.max }
        } else if &bounds_2.max >= zero { // bounds_2 are neg/pos
            Bounds { 
                min: min(&bounds_1.min * &bounds_2.max, &bounds_1.max * &bounds_2.min), 
                max: max(&bounds_1.min * &bounds_2.min, &bounds_1.max * &bounds_2.max)
            }
        } else { // bounds_2 are two_negative
            Bounds { min: &bounds_1.max * &bounds_2.min, max: &bounds_1.min * &bounds_2.min }
        }
    } else { // bounds_1 are negative
        if &bounds_2.min >= zero { // bounds_2 are two-positive
            Bounds { min: &bounds_1.min * &bounds_2.max, max: &bounds_1.max * &bounds_2.min }
        } else if &bounds_2.max >= zero { // bounds_2 are neg/pos
            Bounds { min: &bounds_1.min * &bounds_2.max, max: &bounds_1.min * &bounds_2.min }
        } else { // bounds_2 are two_negative
            Bounds { min: &bounds_1.max * &bounds_2.max, max: &bounds_1.min * &bounds_2.min }
        }
    }
}
