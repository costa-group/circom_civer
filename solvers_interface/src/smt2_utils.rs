
use std::collections::{HashMap, LinkedList};
use crate::{BigInt, ExecutedImplication, Expression, SafetyImplication, VerificationProblem};
use program_structure::ast::{ExpressionInfixOpcode, ExpressionPrefixOpcode};


use circom_algebra::algebra::Constraint;
use circom_algebra::modular_arithmetic::*;


// ---------------------------------------------------------------------------
// Translation of comparisons into ff.range
//
// circom works with values in [0, p-1]: a specification is written with those
// semantics and nothing else. ffsol, on the other hand, reads the bounds of
// (ff.range x min max) over the SIGNED representative of the field, in [-h, h]
// with h = (p-1)/2: the constant p-1 is read as -1, not as the maximum.
//
// The conversion between the two views is done here, not in the specifications.
// An unsigned interval [a,b] of circom splits into at most two pieces of the
// signed domain:
//
//     [a, min(b,h)]           the part that is already non negative
//     [max(a,h+1)-p, b-p]     the part ffsol sees as negative
//
// and the translated condition is the disjunction of both. That way `min <= in`
// also covers the upper half of the field, which is what it means in circom,
// without whoever writes the specification having to split it by hand.
// ---------------------------------------------------------------------------

/// h = (p-1)/2, the largest positive value of the signed representative.
fn max_signed(prime: &BigInt) -> BigInt {
    (prime - BigInt::from(1)) / BigInt::from(2)
}

/// Field constant out of a possibly negative value.
fn ff_const(v: &BigInt, prime: &BigInt) -> String {
    let zero = BigInt::from(0);
    let unsigned = if *v < zero { v + prime } else { v.clone() };
    format!("(as ff{} FF0)", unsigned)
}

// Largest number of values of an interval that are enumerated as equalities
// instead of being left as an ff.range. ffsol propagates intervals but does not
// do case analysis on them: with the hypothesis "a in [0,1]" given as a range,
// proving the binary tag of OR() (out = a+b-a*b) does not terminate, because
// propagating intervals yields out in [-1,2]; with the hypothesis given as
// (or (= a 0) (= a 1)) the boolean layer does the case analysis in milliseconds.
const MAX_ENUMERATED_INTERVAL: u32 = 4;

fn interval_len(min: &BigInt, max: &BigInt) -> BigInt {
    max - min + BigInt::from(1)
}

fn is_narrow(min: &BigInt, max: &BigInt) -> bool {
    interval_len(min, max) <= BigInt::from(MAX_ENUMERATED_INTERVAL)
}

fn enumerate_values(min: &BigInt, max: &BigInt) -> Vec<BigInt> {
    let mut values = Vec::new();
    let mut v = min.clone();
    while v <= *max {
        values.push(v.clone());
        v += 1;
    }
    values
}

/// x is in the signed interval [min, max].
fn ff_interval(x: &str, min: &BigInt, max: &BigInt, prime: &BigInt) -> String {
    if min > max {
        // empty interval
        "false".to_string()
    } else if is_narrow(min, max) {
        let equalities: Vec<String> = enumerate_values(min, max).iter()
            .map(|v| format!("(= {} {})", x, ff_const(v, prime)))
            .collect();
        if equalities.len() == 1 {
            equalities[0].clone()
        } else {
            format!("(or {})", equalities.join(" "))
        }
    } else {
        format!("(ff.range {} {} {})", x, ff_const(min, prime), ff_const(max, prime))
    }
}

/// x, read as a circom value in [0, p-1], is in the UNSIGNED interval
/// [min, max]. It is the union of the two pieces it maps to in the signed
/// domain ffsol works with.
fn unsigned_interval(x: &str, min: &BigInt, max: &BigInt, prime: &BigInt) -> String {
    let zero = BigInt::from(0);
    let one = BigInt::from(1);
    let h = max_signed(prime);
    if *min > *max {
        return "false".to_string();
    }
    if *min == zero && *max == prime - &one {
        // the whole field
        return "true".to_string();
    }
    // non negative piece: [min, min(max, h)]
    let low = if *min <= h {
        let hi = if *max < h { max.clone() } else { h.clone() };
        ff_interval(x, min, &hi, prime)
    } else {
        "false".to_string()
    };
    // piece ffsol sees as negative: [max(min, h+1) - p, max - p]
    let high = if *max > h {
        let lo = if *min > h { min.clone() } else { &h + &one };
        ff_interval(x, &(lo - prime), &(max - prime), prime)
    } else {
        "false".to_string()
    };
    if low == "false" {
        high
    } else if high == "false" {
        low
    } else if low == "true" || high == "true" {
        "true".to_string()
    } else {
        format!("(or {} {})", low, high)
    }
}

/// x, read as a circom value, is OUTSIDE the unsigned interval [min, max]. The
/// complement within [0, p-1] is [0, min-1] U [max+1, p-1], emitted as positive
/// ranges: see below why the (not ...) is not left to the solver.
fn unsigned_not_interval(x: &str, min: &BigInt, max: &BigInt, prime: &BigInt) -> String {
    let zero = BigInt::from(0);
    let one = BigInt::from(1);
    let last = prime - &one;
    if *min > *max {
        return "true".to_string();
    }
    if is_narrow(min, max) {
        // few values: disequalities beat two wide ranges here
        let disequalities: Vec<String> = enumerate_values(min, max).iter()
            .map(|v| format!("(not (= {} {}))", x, ff_const(v, prime)))
            .collect();
        return if disequalities.len() == 1 {
            disequalities[0].clone()
        } else {
            format!("(and {})", disequalities.join(" "))
        };
    }
    let below = if *min > zero {
        unsigned_interval(x, &zero, &(min - &one), prime)
    } else {
        "false".to_string()
    };
    let above = if *max < last {
        unsigned_interval(x, &(max + &one), &last, prime)
    } else {
        "false".to_string()
    };
    if below == "false" {
        above
    } else if above == "false" {
        below
    } else {
        format!("(or {} {})", below, above)
    }
}

/// Normalizes a constant to the circom representative in [0, p-1].
fn to_unsigned(v: &BigInt, prime: &BigInt) -> BigInt {
    let r = v % prime;
    if r < BigInt::from(0) { r + prime } else { r }
}

/// lower <= x, with the bounds read as circom values: [lower, p-1].
fn range_lower_bound(x: &str, lower: &BigInt, prime: &BigInt) -> String {
    let lower = to_unsigned(lower, prime);
    unsigned_interval(x, &lower, &(prime - BigInt::from(1)), prime)
}

/// x <= upper, that is, x in [0, upper].
fn range_upper_bound(x: &str, upper: &BigInt, prime: &BigInt) -> String {
    let upper = to_unsigned(upper, prime);
    unsigned_interval(x, &BigInt::from(0), &upper, prime)
}

// Negations are translated as POSITIVE ranges. ffsol does accept
// (not (ff.range ...)) and decides it in many cases, but there are formulas
// where it does not terminate while the equivalent positive range is immediate:
// see smt2_ffsol/ for the cases, in particular an equality plus a negated range,
// which is exactly the shape of a negated tag postcondition. The complement of
// an unsigned interval is again a union of unsigned intervals, so negating it
// here costs nothing and avoids that failure mode.

/// not (lower <= x), that is, x in [0, lower-1].
fn range_not_lower_bound(x: &str, lower: &BigInt, prime: &BigInt) -> String {
    let lower = to_unsigned(lower, prime);
    unsigned_interval(x, &BigInt::from(0), &(lower - BigInt::from(1)), prime)
}

/// not (x <= upper), that is, x in [upper+1, p-1].
fn range_not_upper_bound(x: &str, upper: &BigInt, prime: &BigInt) -> String {
    let upper = to_unsigned(upper, prime);
    unsigned_interval(x, &(upper + BigInt::from(1)), &(prime - BigInt::from(1)), prime)
}


/* 
pub fn correctness_problem_to_smt2(problem: &CorrectnessVerification)->LinkedList<String>{
    let mut smt2_problem = LinkedList::new();
    let mut header = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
 
    for s in &problem.signals_1 {
        let name = format!("s_{}",s);
        smt2_problem.push_back(declare_signal(&name)); 
        signal_to_name.insert(*s,name.clone());
    }

    for s in &problem.signals_2 {
        smt2_problem.push_back(declare_signal(s)); 
    }

    for constraint in &problem.constraints_1 {

        smt2_problem.push_back(
            format!("(assert {})",
                constraint.constraint_to_smt2(&signal_to_name)
            )
        );
        
    }

    for constraint in &problem.constraints_2 {

        smt2_problem.push_back(
            format!("{}",
                constraint
            )
        );
        
    }


    // for imp in &problem.implications_equivalence{
    //     let new_imp = implication_to_smt2(imp,&signal_to_name,&signal_to_name_aux);
    //     smt2_problem.push_back(
    //         format!("(assert {})",
    //             new_imp
    //         )
    //     );
    // }

    smt2_problem.push_back(
        format!("(assert {})",
            declare_all_signals_equal_2(&problem.inputs_1, &signal_to_name, &problem.inputs_2)
        )
    );

    smt2_problem.push_back(
        format!("(assert (not {}))",
            declare_all_signals_equal_2(&problem.outputs_1, &signal_to_name, &problem.outputs_2)
        )
    );
    smt2_problem.push_back(format!("(check-sat)"));
    smt2_problem
    
}


pub fn equivalence_problem_to_smt2(problem: &EquivalenceVerification,use_old_syntax:bool)->LinkedList<String>{
    let mut smt2_problem = LinkedList::new();
    let mut header = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
    let mut signal_to_name_aux = HashMap::new();
 
    for s in &problem.signals_1 {
        let name = format!("s_{}",s);
        smt2_problem.push_back(declare_signal(&name)); 
        signal_to_name.insert(*s,name.clone());
    }

    for s in &problem.signals_2 {
        let name = format!("saux_{}",s);
        smt2_problem.push_back(declare_signal(&name)); 
        signal_to_name_aux.insert(*s,name.clone());
    }

    for constraint in &problem.constraints_1 {
        if use_old_syntax{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2_old(&signal_to_name)
                )
            );
        }else{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2(&signal_to_name)
                )
            );
        }
        
    }

    for constraint in &problem.constraints_2 {
        if use_old_syntax{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2_old(&signal_to_name_aux)
                )
            );
        }else{
            smt2_problem.push_back(
               format!("(assert {})",
                  constraint.constraint_to_smt2(&signal_to_name_aux)
                )
            );
        }
    }


    // for imp in &problem.implications_equivalence{
    //     let new_imp = implication_to_smt2(imp,&signal_to_name,&signal_to_name_aux);
    //     smt2_problem.push_back(
    //         format!("(assert {})",
    //             new_imp
    //         )
    //     );
    // }

    smt2_problem.push_back(
        format!("(assert {})",
            declare_all_signals_equal(&problem.inputs_1, &signal_to_name, &problem.inputs_2,&signal_to_name_aux)
        )
    );

    smt2_problem.push_back(
        format!("(assert (not {}))",
            declare_all_signals_equal(&problem.outputs_1, &signal_to_name, &problem.outputs_2,&signal_to_name_aux)
        )
    );
    smt2_problem.push_back(format!("(check-sat)"));
    smt2_problem
    
}

*/
pub fn safety_problem_to_smt2(
    problem: &VerificationProblem
)->LinkedList<String>{

    fn is_input_signal(problem: &VerificationProblem, signal: usize)-> bool{

        problem.initial_signal + problem.number_outputs <= signal && 
            signal < problem.initial_signal + problem.number_outputs + problem.number_inputs 
    }


    let mut smt2_problem = LinkedList::new();
    let mut header: LinkedList<String> = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
    let mut signal_to_name_aux = HashMap::new();
    for s in &problem.signals {
        // if already declared do not insert 
        if !signal_to_name.contains_key(s){
            let name = format!("s_{}",s);
            smt2_problem.push_back(declare_signal(&name)); 
            signal_to_name.insert(*s,name.clone());
            
            let name_aux = if is_input_signal(problem,*s){
                name
            }else{
                let aux = format!("s_{}_aux",s);
                smt2_problem.push_back(declare_signal(&aux)); 
                aux  
            };
            signal_to_name_aux.insert(*s,name_aux);
        }
  
    }

    // The specifications of the tags of the inputs are hypotheses when proving
    // weak safety too: the tag of an input is a contract the caller must meet
    // (and which is checked at the call site with --check_tags), so it is
    // asserted on BOTH copies. This is what try_prove_safety does in the
    // reference implementation with tags_preconditions; without it, a template
    // that is only deterministic for tagged inputs (binary, say) produced
    // spurious counterexamples.
    for precondition in &problem.specification_preconditions {
        smt2_problem.push_back(
            format!("(assert {})",
                transform_expression_to_smt2(precondition, &signal_to_name, &problem.field)
            )
        );
        smt2_problem.push_back(
            format!("(assert {})",
                transform_expression_to_smt2(precondition, &signal_to_name_aux, &problem.field)
            )
        );
    }

    // Under --add_tags_info the specifications of the tags that are NOT
    // hypotheses of this problem are assumed rather than proved here: the ones of
    // the outputs and intermediates of the template, and the ones of the outputs
    // of its subcomponents (the right hand side of the abstraction of each
    // child). They are proof obligations of --check_tags, of this template in the
    // first case and of the child in the second, so assuming them here is sound
    // as long as that check passes; it does make the weak safety result
    // conditional on it. What they add is range information about each copy,
    // which is what a determinism argument over a bit decomposition needs and the
    // constraints alone do not give.
    if problem.config.add_tags_info {
        let mut assumed: Vec<&Expression> = Vec::new();
        assumed.extend(problem.specification_intermediates.iter());
        assumed.extend(problem.specification_postconditions.iter());
        for imp in &problem.tags_implications {
            assumed.extend(imp.right.iter());
        }
        for condition in assumed {
            smt2_problem.push_back(
                format!("(assert {})",
                    transform_expression_to_smt2(condition, &signal_to_name, &problem.field)
                )
            );
            smt2_problem.push_back(
                format!("(assert {})",
                    transform_expression_to_smt2(condition, &signal_to_name_aux, &problem.field)
                )
            );
        }
    }

    for constraint in &problem.constraints {
        smt2_problem.push_back(
            format!("(assert {})",
                constraint.constraint_to_smt2(&signal_to_name)
            )
        );
        smt2_problem.push_back(
            format!("(assert {})",
                constraint.constraint_to_smt2(&signal_to_name_aux)
            )
        );

        // todo: add flag
        //if problem.apply_deduction_assigned{
            let deductions_uniqueness = apply_deduction_assigned(constraint,&signal_to_name,&signal_to_name_aux);
            for imp in deductions_uniqueness{
                smt2_problem.push_back(
                    format!("(assert {})", imp)
                );
            } 
        //}
    }


    for imp in &problem.implications_safety{
        let new_imp = safety_implication_to_smt2(imp,&signal_to_name,&signal_to_name_aux);
        smt2_problem.push_back(
            format!("(assert {})",
                new_imp
            )
        );
    }


    let outputs = (problem.initial_signal.. problem.initial_signal+problem.number_outputs).collect();

    smt2_problem.push_back(
        format!("(assert (not {}))",
            declare_all_signals_equal(&outputs, &signal_to_name, &outputs,&signal_to_name_aux)
        )
    );
    smt2_problem.push_back(format!("(check-sat)"));
    smt2_problem
    
}


pub fn tag_verification_problem_to_smt2(
    problem: &VerificationProblem
) -> LinkedList<String> {

    let mut smt2_problem = LinkedList::new();
    let mut header: LinkedList<String> = declare_header(&problem.field);
    smt2_problem.append(&mut header);

    let mut signal_to_name = HashMap::new();
    for s in &problem.signals {
        // if already declared do not insert 
        if !signal_to_name.contains_key(s){
            let name = format!("s_{}",s);
            smt2_problem.push_back(declare_signal(&name)); 
            signal_to_name.insert(*s,name.clone());
        }

    }

    for constraint in &problem.constraints {
        smt2_problem.push_back(
            format!("(assert {})",
                constraint.constraint_to_smt2(&signal_to_name)
            )
        );
    }

    // add the abstractions of the children (implications)
    for imp in &problem.tags_implications{
        let new_imp = implication_to_smt2(imp,&signal_to_name, &problem.field);
        smt2_problem.push_back(
            format!("(assert {})",
                new_imp
            )
        );
    }

    // add the preconditions
    let preconditions: String = if problem.specification_preconditions.len() == 0{
        "true".to_string()
    } else if problem.specification_preconditions.len() == 1{
        let s = &problem.specification_preconditions[0];
        format!("{}", transform_expression_to_smt2(s, &signal_to_name, &problem.field))
    } else{
        let mut aux = "(and ".to_string();
        for s in &problem.specification_preconditions{
            aux = format!("{} {} ", aux, transform_expression_to_smt2(&s, &signal_to_name, &problem.field));
        }
        aux = format!("{})",aux);
        aux
    };

    smt2_problem.push_back(format!("(assert {})", preconditions));

    // negate the postconditions: the negation is pushed down to the leaves so
    // that no negated range is left in the formula
    let negated: Vec<String> = problem.specification_intermediates.iter()
        .chain(problem.specification_postconditions.iter())
        .map(|s| transform_negated_expression_to_smt2(s, &signal_to_name, &problem.field))
        .collect();

    let negated_postconditions: String = if negated.len() == 0{
        // (not true)
        "false".to_string()
    } else if negated.len() == 1{
        negated[0].clone()
    } else{
        // not (p1 and ... and pn) = (not p1) or ... or (not pn)
        format!("(or {})", negated.join(" "))
    };

    smt2_problem.push_back(format!("(assert {})", negated_postconditions));



    smt2_problem.push_back(format!("(check-sat)"));
    smt2_problem
    
}



pub fn declare_signal(signal_name: &String)->String{
    format!("(declare-fun {} () FF0)",signal_name)
}


pub fn declare_header(prime: &BigInt)->LinkedList<String>{
    let mut aux = LinkedList::new();
    aux.push_back("(set-logic QF_FF)".to_string());
    aux.push_back(format!("(define-sort FF0 () (_ FiniteField {}))", prime));
    aux
}



pub fn implication_to_smt2(imp: &ExecutedImplication, signals_to_names: &HashMap<usize,String>, prime: &BigInt) -> String{
    let left: String = if imp.left.len() == 0{
        "true".to_string()
    } else if imp.left.len() == 1{
        let s = &imp.left[0];
        format!("{}", transform_expression_to_smt2(s, signals_to_names, prime))
    } else{
        let mut aux = "(and ".to_string();
        for s in &imp.left{
            aux = format!("{} {} ", aux, transform_expression_to_smt2(&s, signals_to_names, prime));
        }
        aux = format!("{})",aux);
        aux
    };

    let right = if imp.right.len() == 0{
        "true".to_string()
    } else if imp.right.len() == 1{
        let s = &imp.right[0];
        format!("{}", transform_expression_to_smt2(s, signals_to_names, prime))
    } else{
        let mut aux = "(and ".to_string();
        for s in &imp.right{
            aux = format!("{} {} ", aux, transform_expression_to_smt2(&s, signals_to_names, prime));
        }
        aux = format!("{})",aux);
        aux
    };

    format!("(=> {} {})", left, right)

}

pub fn safety_implication_to_smt2(imp: &SafetyImplication, signal_to_names: &HashMap<usize,String>, signal_to_names_aux: &HashMap<usize,String>) -> String{
    let left: String = if imp.left.len() == 0{
        "true".to_string()
    } else if imp.left.len() == 1{
        let s = imp.left[0];
        format!("(= {} {})", signal_to_names[&s], signal_to_names_aux[&s])
    } else{
        let mut aux = "(and ".to_string();
        for s in &imp.left{
            aux = format!("{} (= {} {}) ", aux, signal_to_names[s], signal_to_names_aux[s]);
        }
        aux = format!("{})",aux);
        aux
    };

    let right = if imp.right.len() == 0{
        "true".to_string()
    } else if imp.right.len() == 1{
        let s = imp.right[0];
        format!("(= {} {})", signal_to_names[&s], signal_to_names_aux[&s])
    } else{
        let mut aux = "(and ".to_string();
        for s in &imp.right{
            aux = format!("{} (= {} {}) ", aux, signal_to_names[s], signal_to_names_aux[s]);
        }
        aux = format!("{})",aux);
        aux
    };

    format!("(=> {} {})", left, right)

}


pub fn apply_deduction_assigned(
    c: &Constraint<usize>,
    signals_to_names: &HashMap<usize,String>,
    signals_to_names_aux: &HashMap<usize,String>,
)->Vec<String> {

    let all_signals = c.take_signals();
    let only_linear_signals = c.take_only_linear_signals();

    let mut uniqueness_implications = Vec::new();
    // in case there are signals that are only_linear
    for s_deduced in only_linear_signals {
        // Generate the implication all signals in C are deterministic
        //  => s_deduced is deterministic

        let value_right_1 = signals_to_names.get(s_deduced).unwrap();
        let value_right_2 = signals_to_names_aux.get(s_deduced).unwrap();
        let right_side = format!("(= {} {})",
            value_right_1,
            value_right_2
        );

        let left_side = if all_signals.len() == 1{
            "true".to_string()
        } else {
            let mut new_left_side = if all_signals.len() > 2{
                "(and ".to_string()
            }else{
                "".to_string()
            };
            for s in &all_signals {
                if *s != s_deduced {
                    let value_s_1 = signals_to_names.get(s).unwrap();
                    let value_s_2 = signals_to_names_aux.get(s).unwrap();
                    new_left_side = format!("{}(= {} {}) ",
                        new_left_side,
                        value_s_1,
                        value_s_2
                    );
    
                }
            }

            if all_signals.len() > 2{
                new_left_side = format!("{})", new_left_side);
            }

            new_left_side
        };

        uniqueness_implications.push(
            format!("(=> {} {})",
                left_side,
                right_side
            )
        );  

    }
    uniqueness_implications
}


pub fn declare_all_signals_equal(signals: &Vec<usize>, signal_to_names: &HashMap<usize,String>, signals_aux:&Vec<usize>,signal_to_names_aux: &HashMap<usize,String>) -> String{
    if signals.len() == 0{
        "true".to_string()
    } else if signals.len() == 1{
        let s = signals[0];
        let s_aux = signals_aux[0];
        format!("(= {} {})", signal_to_names[&s], signal_to_names_aux[&s_aux])
    } else{
        let mut aux = "(and ".to_string();
        for i in 0..signals.len(){
            aux = format!("{} (= {} {}) ", aux, signal_to_names[&signals[i]], signal_to_names_aux[&signals_aux[i]]);
        }
        aux = format!("{})",aux);
        aux
    }
}

pub fn declare_all_signals_equal_2(signals: &Vec<usize>, signal_to_names: &HashMap<usize,String>, signals_aux:&Vec<String>) -> String{
    if signals.len() == 0{
        "true".to_string()
    } else if signals.len() == 1{
        let s = signals[0];
        let s_aux = &signals_aux[0];
        format!("(= {} {})", signal_to_names[&s], s_aux)
    } else{
        let mut aux = "(and ".to_string();
        for i in 0..signals.len(){
            aux = format!("{} (= {} {}) ", aux, signal_to_names[&signals[i]], signals_aux[i]);
        }
        aux = format!("{})",aux);
        aux
    }
}



fn get_expression_number(
    expr: &Expression,
    prime: &BigInt
) -> Option<BigInt>{
    use Expression::*;

    match expr{
        Number(_,v) => {
            Some(v.clone())
        }
        Variable {name, ..} => {
            None
        }
        InfixOp { lhe, infix_op, rhe, .. } => {
            let l_number = get_expression_number(lhe, prime);
            let r_number = get_expression_number( rhe, prime);

            if l_number.is_none() || r_number.is_none() {
                return None;
            }
            let l_number = l_number.unwrap();
            let r_number = r_number.unwrap();
            let result = match infix_op{
                ExpressionInfixOpcode::Mul => mul(&l_number, &r_number, prime),
                ExpressionInfixOpcode::Add => add(&l_number, &r_number, prime),
                ExpressionInfixOpcode::Pow =>
                    circom_algebra::modular_arithmetic::pow(&l_number, &r_number, prime),
                ExpressionInfixOpcode::ShiftL => {
                    match shift_l(&l_number, &r_number, prime){
                        Ok(v) => v,
                        Err(_) => return None,
                    }
                },
                ExpressionInfixOpcode::Sub => sub(&l_number, &r_number, prime),
                ExpressionInfixOpcode::LesserEq => lesser_eq(&l_number, &r_number, prime),
                ExpressionInfixOpcode::GreaterEq => greater_eq(&l_number, &r_number, prime),
                ExpressionInfixOpcode::Lesser => lesser(&l_number,& r_number, prime),
                ExpressionInfixOpcode::Greater => greater_eq(&l_number, &r_number, prime),
                ExpressionInfixOpcode::Eq => eq(&l_number, &r_number, prime),
                ExpressionInfixOpcode::NotEq => not_eq(&l_number, &r_number, prime),
                ExpressionInfixOpcode::BoolOr => bool_or(&l_number,& r_number, prime),
                ExpressionInfixOpcode::BoolAnd => bool_and(&l_number, &r_number, prime),
               
                _ => unreachable!(),
            };
            Some(result)
    
        }
        PrefixOp {  prefix_op, rhe, .. } => {
            let r_value = get_expression_number(rhe, prime);
            if r_value.is_none(){
                return None
            }
            let r_value = r_value.unwrap();
            let result = match prefix_op{
                ExpressionPrefixOpcode::Sub => prefix_sub(&r_value, prime),
                ExpressionPrefixOpcode::BoolNot => not(&r_value, prime),

                _ => unreachable!(),
            };
            Some(result)
    
        }
        _ => unreachable!()
    }
}

/// Splits a comparison with one constant side into (x, bound, is_lower_bound).
fn split_comparison(
    lhe: &Expression,
    rhe: &Expression,
    lesser_eq: bool,
    signals_to_names: &HashMap<usize,String>,
    prime: &BigInt
) -> (String, BigInt, bool){
    if let Some(value) = get_expression_number(lhe, prime){
        // c <= x is a lower bound of x; c >= x is an upper bound
        let x = transform_expression_to_smt2(rhe, signals_to_names, prime);
        (x, value, lesser_eq)
    } else if let Some(value) = get_expression_number(rhe, prime){
        // x <= c is an upper bound of x; x >= c is a lower bound
        let x = transform_expression_to_smt2(lhe, signals_to_names, prime);
        (x, value, !lesser_eq)
    } else{
        unreachable!("Not valid expression")
    }
}

/// Returns (x, bound, is_lower_bound) when the expression is a comparison with
/// one constant side, and None otherwise.
fn bound_atom(
    expr: &Expression,
    signals_to_names: &HashMap<usize,String>,
    prime: &BigInt
) -> Option<(String, BigInt, bool)>{
    use Expression::*;

    match expr{
        InfixOp { lhe, infix_op, rhe, .. } => {
            let lesser_eq = match infix_op{
                ExpressionInfixOpcode::LesserEq => true,
                ExpressionInfixOpcode::GreaterEq => false,
                _ => return None,
            };
            if get_expression_number(lhe, prime).is_none()
                && get_expression_number(rhe, prime).is_none(){
                return None;
            }
            Some(split_comparison(lhe, rhe, lesser_eq, signals_to_names, prime))
        }
        _ => None,
    }
}

/// Recognizes "lo <= x && x <= hi" (in either order) and returns the UNSIGNED
/// interval [lo, hi] of x, in circom semantics. Each comparison on its own spans
/// half the field, so without merging them a narrow interval is never reached
/// and the case analysis ffsol needs is lost.
///
/// The intersection is taken in [0, p-1], just like range_lower_bound and
/// range_upper_bound do: "lo <= x" is [lo, p-1] and "x <= hi" is [0, hi], so the
/// conjunction is [lo, hi] when lo <= hi and the empty interval otherwise. Taking
/// it over the signed representative gave results that disagreed with the ones of
/// the two bounds taken separately.
fn try_merge_interval(
    lhe: &Expression,
    rhe: &Expression,
    signals_to_names: &HashMap<usize,String>,
    prime: &BigInt
) -> Option<(String, BigInt, BigInt)>{
    let (x_left, value_left, left_is_lower) = bound_atom(lhe, signals_to_names, prime)?;
    let (x_right, value_right, right_is_lower) = bound_atom(rhe, signals_to_names, prime)?;

    if x_left != x_right || left_is_lower == right_is_lower{
        return None;
    }
    let (lower, upper) = if left_is_lower{
        (value_left, value_right)
    } else{
        (value_right, value_left)
    };
    Some((x_left, to_unsigned(&lower, prime), to_unsigned(&upper, prime)))
}

/// Translates the negation of expr by pushing the not down to the leaves, so
/// that comparisons end up as positive ranges (see above).
fn transform_negated_expression_to_smt2(
    expr: &Expression,
    signals_to_names: &HashMap<usize,String>,
    prime: &BigInt
) -> String{
    use Expression::*;

    match expr{
        InfixOp { lhe, infix_op, rhe, .. } => {
            match infix_op{
                ExpressionInfixOpcode::BoolAnd => {
                    if let Some((x, lower, upper)) =
                        try_merge_interval(lhe, rhe, signals_to_names, prime){
                        return unsigned_not_interval(&x, &lower, &upper, prime);
                    }
                    let l = transform_negated_expression_to_smt2(lhe, signals_to_names, prime);
                    let r = transform_negated_expression_to_smt2(rhe, signals_to_names, prime);
                    format!("(or {} {})", l, r)
                },
                ExpressionInfixOpcode::BoolOr => {
                    let l = transform_negated_expression_to_smt2(lhe, signals_to_names, prime);
                    let r = transform_negated_expression_to_smt2(rhe, signals_to_names, prime);
                    format!("(and {} {})", l, r)
                },
                ExpressionInfixOpcode::LesserEq | ExpressionInfixOpcode::GreaterEq => {
                    let lesser_eq = *infix_op == ExpressionInfixOpcode::LesserEq;
                    let (x, bound, is_lower) =
                        split_comparison(lhe, rhe, lesser_eq, signals_to_names, prime);
                    if is_lower{
                        range_not_lower_bound(&x, &bound, prime)
                    } else{
                        range_not_upper_bound(&x, &bound, prime)
                    }
                },
                ExpressionInfixOpcode::Eq => {
                    let l = transform_expression_to_smt2(lhe, signals_to_names, prime);
                    let r = transform_expression_to_smt2(rhe, signals_to_names, prime);
                    format!("(not (= {} {}))", l, r)
                },
                ExpressionInfixOpcode::NotEq => {
                    let l = transform_expression_to_smt2(lhe, signals_to_names, prime);
                    let r = transform_expression_to_smt2(rhe, signals_to_names, prime);
                    format!("(= {} {})", l, r)
                },
                _ => {
                    let positive = transform_expression_to_smt2(expr, signals_to_names, prime);
                    format!("(not {})", positive)
                }
            }
        }
        PrefixOp { prefix_op, rhe, .. } if *prefix_op == ExpressionPrefixOpcode::BoolNot => {
            transform_expression_to_smt2(rhe, signals_to_names, prime)
        }
        _ => {
            let positive = transform_expression_to_smt2(expr, signals_to_names, prime);
            format!("(not {})", positive)
        }
    }
}

fn transform_expression_to_smt2(
    expr: &Expression,
    signals_to_names: &HashMap<usize,String>,
    prime: &BigInt
) -> String{
    use Expression::*;
    use circom_algebra::num_traits::ToPrimitive;

        match expr{
            Number(_,v) => {
                format!("(as ff{} FF0)", v)
            }
            Variable {name, ..} => {
                signals_to_names.get(&name.parse::<usize>().unwrap()).unwrap().clone()
            }
            InfixOp { lhe, infix_op, rhe, .. } => {

                match infix_op{
                    ExpressionInfixOpcode::Mul => {
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);
                        let r_string = transform_expression_to_smt2( rhe, signals_to_names, prime);
                        format!("(ff.mul {} {})", l_string, r_string)
                    },
                    ExpressionInfixOpcode::Add => {
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);
                        let r_string = transform_expression_to_smt2( rhe, signals_to_names, prime);
                        format!("(ff.add {} {})", l_string, r_string)
                    },
                    ExpressionInfixOpcode::ShiftL => {
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);

                        if rhe.is_number(){
                            match *rhe.clone(){
                                Expression::Number(_, value) => {
                                    let pow_value = circom_algebra::num_traits::pow(
                                        BigInt::from(2), value.to_usize().unwrap());
                                    format!("(ff.mul {} (as ff{} FF0))", l_string, pow_value)
                                }
                                _ => {
                                    todo!()
                                }
                            }
                        } else{
                            todo!()
                        }
                        
                    },

                    ExpressionInfixOpcode::Sub => {
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);
                        let r_string = transform_expression_to_smt2( rhe, signals_to_names, prime);
                        let minus_one = format!("(as ff{} FF0)", prime - 1);
                        let minus_b = format!("(ff.mul {} {})", minus_one, r_string);
                        format!("(ff.add {} {})", l_string, minus_b)

                    }

                    ExpressionInfixOpcode::LesserEq | ExpressionInfixOpcode::GreaterEq => {
                        let lesser_eq = *infix_op == ExpressionInfixOpcode::LesserEq;
                        let (x, bound, is_lower) =
                            split_comparison(lhe, rhe, lesser_eq, signals_to_names, prime);
                        if is_lower{
                            range_lower_bound(&x, &bound, prime)
                        } else{
                            range_upper_bound(&x, &bound, prime)
                        }
                    },
                    ExpressionInfixOpcode::Lesser => {
                        todo!()
                    },
                    ExpressionInfixOpcode::Greater => {
                        todo!()
                    },
                    ExpressionInfixOpcode::Eq => {
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);
                        let r_string = transform_expression_to_smt2( rhe, signals_to_names, prime);
                        format!("(= {} {})", l_string, r_string)

                    },  
                    ExpressionInfixOpcode::NotEq => {
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);
                        let r_string = transform_expression_to_smt2( rhe, signals_to_names, prime);
                        format!("(not (= {} {}))", l_string, r_string)

                    },  
                    ExpressionInfixOpcode::BoolOr => {
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);
                        let r_string = transform_expression_to_smt2( rhe, signals_to_names, prime);
                        format!("(or {} {})", l_string, r_string)

                    },  
                    ExpressionInfixOpcode::BoolAnd => {
                        if let Some((x, lower, upper)) =
                            try_merge_interval(lhe, rhe, signals_to_names, prime){
                            return unsigned_interval(&x, &lower, &upper, prime);
                        }
                        let l_string = transform_expression_to_smt2(lhe, signals_to_names, prime);
                        let r_string = transform_expression_to_smt2( rhe, signals_to_names, prime);
                        format!("(and {} {})", l_string, r_string)
                    },
                    
                   
                    _ => unreachable!(),
                }
        
            }
            PrefixOp {  prefix_op, rhe, .. } => {
                let r_string = transform_expression_to_smt2(rhe, signals_to_names, prime);
                match prefix_op{
                    ExpressionPrefixOpcode::Sub => {
                        let minus_one = format!("(as ff{} FF0)", prime - 1);
                        format!("(ff.mul {} {})", minus_one, r_string)
                    },
                    ExpressionPrefixOpcode::BoolNot => {
                        format!("(not {})", r_string)

                    },

                    _ => unreachable!(),
                }
        
            }
            _ => unreachable!()
            
        }
}
