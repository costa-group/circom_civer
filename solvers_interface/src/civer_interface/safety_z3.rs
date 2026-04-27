use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;
use num_bigint_dig::BigInt;
use crate::PossibleResult;
use circom_algebra::algebra::{Constraint, ExecutedInequation};

use z3::Config;
use z3::Context;
use z3::Solver;
use z3::ast::Ast;
use z3::*;

use super::tags_checking::{
    compute_bounds_linear_expression_strict,
    compute_bounds_product,
    Signal2Bounds,
};

pub type Signal2BoundsZ3 = HashMap<usize, ExecutedInequation<usize>>;

//This function only works if 0 <= a <= field - 1
fn to_neg(a: &BigInt, field: &BigInt) -> BigInt{
    if a < &(field/BigInt::from(2)){
        a.clone()
    }
    else {
        a - field
    }
}

pub fn try_prove_safety_with_z3(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<Constraint<usize>>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    verification_timeout: u64,
    opt_apply_deduction_assigned: bool,
    logs: &mut Vec<String>,
) -> PossibleResult {
    try_prove_safety_with_z3_internal(
        inputs,
        outputs,
        signals,
        constraints,
        implications_safety,
        deductions,
        field,
        verification_timeout,
        opt_apply_deduction_assigned,
        logs,
        None,
    )
}

pub fn try_prove_safety_with_z3_cancel(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<Constraint<usize>>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    verification_timeout: u64,
    opt_apply_deduction_assigned: bool,
    logs: &mut Vec<String>,
    cancel_flag: &AtomicBool,
) -> PossibleResult {
    try_prove_safety_with_z3_internal(
        inputs,
        outputs,
        signals,
        constraints,
        implications_safety,
        deductions,
        field,
        verification_timeout,
        opt_apply_deduction_assigned,
        logs,
        Some(cancel_flag),
    )
}

fn try_prove_safety_with_z3_internal(
    inputs: &Vec<usize>,
    outputs: &Vec<usize>,
    signals: &Vec<usize>,
    constraints: &Vec<Constraint<usize>>,
    implications_safety: &Vec<(Vec<usize>, Vec<usize>)>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    verification_timeout: u64,
    opt_apply_deduction_assigned: bool,
    logs: &mut Vec<String>,
    cancel_flag: Option<&AtomicBool>,
) -> PossibleResult {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(verification_timeout);
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let zero = z3::ast::Int::from_i64(&ctx, 0);
    let field_z3 = z3::ast::Int::from_str(&ctx, &field.to_string()).unwrap();
    let mut aux_signals_to_smt_rep = HashMap::new();
    let mut aux_signals_to_smt_rep_aux = HashMap::new();

    for s in signals {
        let is_input = inputs.contains(s);

        let aux_signal_to_smt = z3::ast::Int::new_const(&ctx, format!("s_{}", s));
        let copy_aux_signal_to_smt = if !is_input {
            z3::ast::Int::new_const(&ctx, format!("saux_{}", s))
        } else {
            z3::ast::Int::new_const(&ctx, format!("s_{}", s))
        };
        aux_signals_to_smt_rep.insert(*s, aux_signal_to_smt.clone());
        aux_signals_to_smt_rep_aux.insert(*s, copy_aux_signal_to_smt.clone());

        match deductions.get(s) {
            None => {
                solver.assert(&aux_signal_to_smt.ge(&zero));
                solver.assert(&aux_signal_to_smt.lt(&field_z3));
                solver.assert(&copy_aux_signal_to_smt.ge(&zero));
                solver.assert(&copy_aux_signal_to_smt.lt(&field_z3));
            }
            Some(bounds) => {
                let condition = get_z3_condition_bounds(
                    &ctx,
                    &aux_signal_to_smt,
                    &bounds.min,
                    &bounds.max,
                    &field,
                );
                solver.assert(&condition);

                let condition = get_z3_condition_bounds(
                    &ctx,
                    &copy_aux_signal_to_smt,
                    &bounds.min,
                    &bounds.max,
                    &field,
                );
                solver.assert(&condition);
            }
        }
    }

    let mut i = 0;
    for constraint in constraints {
        insert_constraint_in_smt(
            constraint,
            &ctx,
            &solver,
            &aux_signals_to_smt_rep,
            &field,
            &deductions,
            i,
            &field_z3,
            false,
        );
        i = i + 1;
        insert_constraint_in_smt(
            constraint,
            &ctx,
            &solver,
            &aux_signals_to_smt_rep_aux,
            &field,
            &deductions,
            i,
            &field_z3,
            false,
        );
        i = i + 1;
    }

    if opt_apply_deduction_assigned {
        apply_deduction_assigned(
            constraints,
            &ctx,
            &solver,
            &aux_signals_to_smt_rep,
            &aux_signals_to_smt_rep_aux,
        );
    } else {
        apply_deduction_rule_homologues(
            constraints,
            &ctx,
            &solver,
            &aux_signals_to_smt_rep,
            &aux_signals_to_smt_rep_aux,
            &deductions,
            &field,
            &field_z3,
        );
    }

    for (inputs_imp, outputs_imp) in implications_safety {
        let mut implication_left = z3::ast::Bool::from_bool(&ctx, true);
        for s in inputs_imp {
            let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
            let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
            implication_left &= s_1._eq(s_2);
        }
        let mut implication_right = z3::ast::Bool::from_bool(&ctx, true);
        for s in outputs_imp {
            let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
            let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
            implication_right &= s_1._eq(s_2);
        }

        solver.assert(&implication_left.implies(&implication_right));
    }

    let mut all_outputs_equal = z3::ast::Bool::from_bool(&ctx, true);
    for s in outputs {
        let s_1 = aux_signals_to_smt_rep.get(s).unwrap();
        let s_2 = aux_signals_to_smt_rep_aux.get(s).unwrap();
        all_outputs_equal &= s_1._eq(s_2);
    }

    solver.assert(&!all_outputs_equal);

    if cancel_flag.map_or(false, |flag| flag.load(Ordering::Relaxed)) {
        logs.push(format!("### CANCELLED BEFORE CHECKING CIVER Z3 MODEL\n"));
        return PossibleResult::UNKNOWN;
    }

    let finished = AtomicBool::new(false);
    let check_result = thread::scope(|scope| {
        let handle = ctx.handle();
        let finished_ref = &finished;
        if let Some(cancel_flag_ref) = cancel_flag {
            scope.spawn(move || {
                while !finished_ref.load(Ordering::Relaxed) {
                    if cancel_flag_ref.load(Ordering::Relaxed) {
                        handle.interrupt();
                        break;
                    }
                    thread::sleep(Duration::from_millis(10));
                }
            });
        }

        let result = solver.check();
        finished.store(true, Ordering::SeqCst);
        result
    });

    match check_result {
        SatResult::Sat => {
            logs.push(format!(
                "### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"
            ));

            let model = solver.get_model().unwrap();
            for s in inputs {
                let v = model
                    .eval(aux_signals_to_smt_rep.get(s).unwrap(), true)
                    .unwrap();
                logs.push(format!("Input signal {}: {}\n", s, v.to_string()));
            }
            for s in outputs {
                let v = model
                    .eval(aux_signals_to_smt_rep.get(s).unwrap(), true)
                    .unwrap();
                let v1 = model
                    .eval(aux_signals_to_smt_rep_aux.get(s).unwrap(), true)
                    .unwrap();

                logs.push(format!(
                    "Output signal {}: values {} | {}\n",
                    s,
                    v.to_string(),
                    v1.to_string()
                ));
            }

            PossibleResult::FAILED
        }
        SatResult::Unsat => {
            logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
            PossibleResult::VERIFIED
        }
        _ => {
            logs.push(format!(
                "### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n"
            ));
            PossibleResult::UNKNOWN
        }
    }
}

pub fn get_z3_condition_bounds<'a>(
    ctx: &'a Context,
    signal: &'a z3::ast::Int<'a>,
    min: &'a BigInt,
    max: &'a BigInt,
    field: &'a BigInt,
) -> z3::ast::Bool<'a> {
    if min >= &BigInt::from(0) {
        &signal.ge(&z3::ast::Int::from_str(&ctx, &min.to_string()).unwrap())
            &
            &signal.le(&z3::ast::Int::from_str(&ctx, &max.to_string()).unwrap())
    } else {
        &z3::ast::Int::from_str(&ctx, &(field + min).to_string())
            .unwrap()
            .le(signal)
            &
            &signal.lt(&z3::ast::Int::from_str(&ctx, &field.to_string()).unwrap())
            |
            &z3::ast::Int::from_i64(&ctx, 0).le(&signal)
            &
            signal.le(&z3::ast::Int::from_str(&ctx, &max.to_string()).unwrap())
    }
}

pub fn insert_constraint_in_smt(
    constraint: &Constraint<usize>,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols: &HashMap<usize, z3::ast::Int>,
    field: &BigInt,
    deductions: &Signal2Bounds,
    num_k: usize,
    p: &z3::ast::Int,
    _verbose: bool,
) {
    let mut value_a = z3::ast::Int::from_u64(ctx, 0);
    let mut value_b = z3::ast::Int::from_u64(ctx, 0);
    let mut value_c = z3::ast::Int::from_u64(ctx, 0);

    for (signal, value) in constraint.a() {
        if *signal == 0 {
            value_a += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else {
            value_a += signals_to_smt_symbols.get(signal).unwrap()
                * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.b() {
        if *signal == 0 {
            value_b += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else {
            value_b += signals_to_smt_symbols.get(signal).unwrap()
                * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.c() {
        if *signal == 0 {
            value_c += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap()
        } else {
            value_c += signals_to_smt_symbols.get(signal).unwrap()
                * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
        }
    }

    let a = constraint.a();
    let b = constraint.b();
    let c = constraint.c();
    let (lower_limit_a, upper_limit_a) =
        compute_bounds_linear_expression_strict(deductions, &a, field);
    let (lower_limit_b, upper_limit_b) =
        compute_bounds_linear_expression_strict(deductions, &b, field);

    let (lower_limit_ab, upper_limit_ab) = compute_bounds_product(
        &lower_limit_a,
        &upper_limit_a,
        &lower_limit_b,
        &upper_limit_b,
    );

    let (lower_limit_c, upper_limit_c) =
        compute_bounds_linear_expression_strict(deductions, &c, field);

    let lower_limit_k = (&lower_limit_c - &upper_limit_ab) / field;
    let upper_limit_k = if (&upper_limit_c - &lower_limit_ab) / field > BigInt::from(0)
        && (&upper_limit_c - &lower_limit_ab) % field != BigInt::from(0)
    {
        (&upper_limit_c - &lower_limit_ab) / field + BigInt::from(1)
    } else {
        (&upper_limit_c - &lower_limit_ab) / field
    };

    let lower_limit_k_a = &lower_limit_a / field;
    let upper_limit_k_a = if &upper_limit_a / field > BigInt::from(0)
        && &upper_limit_a % field != BigInt::from(0)
    {
        &upper_limit_a / field + BigInt::from(1)
    } else {
        &upper_limit_a / field
    };

    let lower_limit_k_b = &lower_limit_b / field;
    let upper_limit_k_b = if &upper_limit_b / field > BigInt::from(0)
        && &upper_limit_b % field != BigInt::from(0)
    {
        &upper_limit_b / field + BigInt::from(1)
    } else {
        &upper_limit_b / field
    };

    let lower_limit_k_c = &lower_limit_c / field;
    let upper_limit_k_c = if &upper_limit_c / field > BigInt::from(0)
        && &upper_limit_c % field != BigInt::from(0)
    {
        &upper_limit_c / field + BigInt::from(1)
    } else {
        &upper_limit_c / field
    };

    // Apply transformation rule A * B = 0 => (A = 0) \/ (B = 0)
    if &upper_limit_c == &lower_limit_c && &upper_limit_c == &BigInt::from(0) {
        let mut value_or = z3::ast::Bool::from_bool(&ctx, false);

        let value_or_a = if upper_limit_k_a == lower_limit_k_a {
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_a.to_string()).unwrap() * p;
            value_a._eq(&value_right)
        } else {
            let k = z3::ast::Int::new_const(&ctx, format!("k_{}_a", num_k));

            let value_right = &k * p;
            solver.assert(&k.ge(&z3::ast::Int::from_str(&ctx, &lower_limit_k_a.to_string()).unwrap()));
            solver.assert(
                &k.le(&z3::ast::Int::from_str(&ctx, &upper_limit_k_a.to_string()).unwrap()),
            );

            value_a._eq(&value_right)
        };

        let value_or_b = if upper_limit_k_b == lower_limit_k_b {
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_b.to_string()).unwrap() * p;
            value_b._eq(&value_right)
        } else {
            let k = z3::ast::Int::new_const(&ctx, format!("k_{}_b", num_k));

            let value_right = &k * p;
            solver.assert(&k.ge(&z3::ast::Int::from_str(&ctx, &lower_limit_k_b.to_string()).unwrap()));
            solver.assert(
                &k.le(&z3::ast::Int::from_str(&ctx, &upper_limit_k_b.to_string()).unwrap()),
            );

            value_b._eq(&value_right)
        };

        value_or |= value_or_a;
        value_or |= value_or_b;
        solver.assert(&value_or);
    } else {
        // Apply deduction rule A * B = C => (C != 0) \/ (A = 0) \/ (B = 0)

        let condition_c = if upper_limit_k_c == lower_limit_k_c {
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_c.to_string()).unwrap() * p;
            value_c._eq(&value_right)
        } else {
            let k = z3::ast::Int::new_const(&ctx, format!("k_{}_c", num_k));

            let value_right = &k * p;
            solver.assert(&k.ge(&z3::ast::Int::from_str(&ctx, &lower_limit_k_c.to_string()).unwrap()));
            solver.assert(
                &k.le(&z3::ast::Int::from_str(&ctx, &upper_limit_k_c.to_string()).unwrap()),
            );
            value_c._eq(&value_right)
        };

        let condition_a: ast::Bool = if upper_limit_k_a == lower_limit_k_a {
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_a.to_string()).unwrap() * p;
            value_a._eq(&value_right)
        } else {
            let k = z3::ast::Int::new_const(&ctx, format!("k_{}_a", num_k));

            let value_right = &k * p;
            solver.assert(&k.ge(&z3::ast::Int::from_str(&ctx, &lower_limit_k_a.to_string()).unwrap()));
            solver.assert(
                &k.le(&z3::ast::Int::from_str(&ctx, &upper_limit_k_a.to_string()).unwrap()),
            );

            value_a._eq(&value_right)
        };

        let condition_b = if upper_limit_k_b == lower_limit_k_b {
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_b.to_string()).unwrap() * p;
            value_b._eq(&value_right)
        } else {
            let k = z3::ast::Int::new_const(&ctx, format!("k_{}_b", num_k));

            let value_right = &k * p;
            solver.assert(&k.ge(&z3::ast::Int::from_str(&ctx, &lower_limit_k_b.to_string()).unwrap()));
            solver.assert(
                &k.le(&z3::ast::Int::from_str(&ctx, &upper_limit_k_b.to_string()).unwrap()),
            );

            value_b._eq(&value_right)
        };

        let mut value_or = z3::ast::Bool::from_bool(&ctx, false);
        value_or |= !condition_c;
        value_or |= condition_a;
        value_or |= condition_b;
        solver.assert(&value_or);

        // APPLY TRANSFORMATION RULE REMOVE MOD
        if lower_limit_k == upper_limit_k {
            let value_left = value_c - (value_a * value_b);
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k.to_string()).unwrap() * p;
            solver.assert(&value_left._eq(&value_right));
        } else {
            let k = z3::ast::Int::new_const(&ctx, format!("k_{}", num_k));

            let value_left = value_c - (value_a * value_b);
            let value_right = &k * p;
            solver.assert(&k.ge(&z3::ast::Int::from_str(&ctx, &lower_limit_k.to_string()).unwrap()));
            solver.assert(
                &k.le(&z3::ast::Int::from_str(&ctx, &upper_limit_k.to_string()).unwrap()),
            );
            solver.assert(&value_left._eq(&value_right));
        }
    }
}

pub fn apply_deduction_assigned(
    constraints: &Vec<Constraint<usize>>,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>,
    signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>,
) {
    for c in constraints {
        let all_signals = c.take_signals();
        let only_linear_signals = c.take_only_linear_signals();

        // in case there are signals that are only_linear
        for s_deduced in only_linear_signals {
            // Generate the implication all signals in C are deterministic
            //  => s_deduced is deterministic

            let value_right_1 = signals_to_smt_symbols_1.get(s_deduced).unwrap();
            let value_right_2 = signals_to_smt_symbols_2.get(s_deduced).unwrap();
            let right_side = value_right_1._eq(&value_right_2);

            let mut left_side = z3::ast::Bool::from_bool(&ctx, true);

            for s in &all_signals {
                if *s != s_deduced {
                    let value_s_1 = signals_to_smt_symbols_1.get(s).unwrap();
                    let value_s_2 = signals_to_smt_symbols_2.get(s).unwrap();
                    let new_left_side = value_s_1._eq(&value_s_2);

                    left_side &= new_left_side;
                }
            }

            let mut value_cond = !left_side;
            value_cond |= &right_side;
            solver.assert(&value_cond);
        }
    }
}

pub fn apply_deduction_rule_homologues(
    constraints: &Vec<Constraint<usize>>,
    ctx: &Context,
    solver: &Solver,
    signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>,
    signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>,
    deductions: &Signal2Bounds,
    field: &BigInt,
    p: &z3::ast::Int,
) {
    for c in constraints {
        let mut value_a = z3::ast::Int::from_u64(ctx, 0);
        let mut value_b = z3::ast::Int::from_u64(ctx, 0);
        let mut value_c = z3::ast::Int::from_u64(ctx, 0);

        let mut value_a1 = z3::ast::Int::from_u64(ctx, 0);
        let mut value_b1 = z3::ast::Int::from_u64(ctx, 0);
        let mut value_c1 = z3::ast::Int::from_u64(ctx, 0);

        for (signal, value) in c.a() {
            if *signal == 0 {
                value_a += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_a1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            } else {
                value_a += signals_to_smt_symbols_1.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_a1 += signals_to_smt_symbols_2.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in c.b() {
            if *signal == 0 {
                value_b += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_b1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            } else {
                value_b += signals_to_smt_symbols_1.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_b1 += signals_to_smt_symbols_2.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            }
        }
        for (signal, value) in c.c() {
            if *signal == 0 {
                value_c += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_c1 += &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            } else {
                value_c += signals_to_smt_symbols_1.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
                value_c1 += signals_to_smt_symbols_2.get(signal).unwrap()
                    * &z3::ast::Int::from_str(&ctx, &to_neg(value, field).to_string()).unwrap();
            }
        }

        let c_a = c.a();
        let c_b = c.b();
        let c_c = c.c();
        let (lower_limit_a, upper_limit_a) =
            compute_bounds_linear_expression_strict(deductions, &c_a, field);
        let (lower_limit_b, upper_limit_b) =
            compute_bounds_linear_expression_strict(deductions, &c_b, field);
        let (lower_limit_c, upper_limit_c) =
            compute_bounds_linear_expression_strict(deductions, &c_c, field);

        let lower_limit_k_aa = (&lower_limit_a - &upper_limit_a) / field;
        let upper_limit_k_aa = if (&upper_limit_a - &lower_limit_a) / field > BigInt::from(0)
            && (&upper_limit_a - &lower_limit_a) % field != BigInt::from(0)
        {
            (&upper_limit_a - &lower_limit_a) / field + BigInt::from(1)
        } else {
            (&upper_limit_a - &lower_limit_a) / field
        };

        let lower_limit_k_bb = (&lower_limit_b - &upper_limit_b) / field;
        let upper_limit_k_bb = if (&upper_limit_b - &lower_limit_b) / field > BigInt::from(0)
            && (&upper_limit_b - &lower_limit_b) % field != BigInt::from(0)
        {
            (&upper_limit_b - &lower_limit_b) / field + BigInt::from(1)
        } else {
            (&upper_limit_b - &lower_limit_b) / field
        };

        let lower_limit_k_cc = (&lower_limit_c - &upper_limit_c) / field;
        let upper_limit_k_cc = if (&upper_limit_c - &lower_limit_c) / field > BigInt::from(0)
            && (&upper_limit_c - &lower_limit_c) % field != BigInt::from(0)
        {
            (&upper_limit_c - &lower_limit_c) / field + BigInt::from(1)
        } else {
            (&upper_limit_c - &lower_limit_c) / field
        };

        let zero = z3::ast::Int::from_u64(&ctx, 0);

        let condition_aa = if lower_limit_k_aa == upper_limit_k_aa {
            let value_left = &value_a - &value_a1;
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_aa.to_string()).unwrap() * p;
            value_left._eq(&value_right)
        } else {
            (&value_a - &value_a1).modulo(&p)._eq(&zero)
        };
        let condition_bb = if lower_limit_k_bb == upper_limit_k_bb {
            let value_left = &value_b - &value_b1;
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_bb.to_string()).unwrap() * p;
            value_left._eq(&value_right)
        } else {
            (&value_b - &value_b1).modulo(&p)._eq(&zero)
        };
        let condition_cc = if lower_limit_k_cc == upper_limit_k_cc {
            let value_left = &value_c - &value_c1;
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_cc.to_string()).unwrap() * p;
            value_left._eq(&value_right)
        } else {
            (&value_c - &value_c1).modulo(&p)._eq(&zero)
        };

        let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
        value_cond |= !&condition_aa;
        value_cond |= !&condition_bb;
        value_cond |= &condition_cc;
        solver.assert(&value_cond);

        let lower_limit_k_a = &lower_limit_a / field;
        let upper_limit_k_a = if &upper_limit_a / field > BigInt::from(0)
            && &upper_limit_a % field != BigInt::from(0)
        {
            &upper_limit_a / field + BigInt::from(1)
        } else {
            &upper_limit_a / field
        };

        let condition_a_not_zero = if lower_limit_k_a == upper_limit_k_a {
            let value_left = &value_a;
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_a.to_string()).unwrap() * p;
            !value_left._eq(&value_right)
        } else {
            !&value_a.modulo(&p)._eq(&zero)
        };

        let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
        value_cond |= !(&condition_aa & &condition_a_not_zero);
        value_cond |= !&condition_cc;
        value_cond |= &condition_bb;
        solver.assert(&value_cond);

        let lower_limit_k_b = &lower_limit_b / field;
        let upper_limit_k_b = if &upper_limit_b / field > BigInt::from(0)
            && &upper_limit_b % field != BigInt::from(0)
        {
            &upper_limit_b / field + BigInt::from(1)
        } else {
            &upper_limit_b / field
        };

        let condition_b_not_zero = if lower_limit_k_b == upper_limit_k_b {
            let value_left = &value_b;
            let value_right =
                z3::ast::Int::from_str(ctx, &lower_limit_k_b.to_string()).unwrap() * p;
            !value_left._eq(&value_right)
        } else {
            !&value_b.modulo(&p)._eq(&zero)
        };
        let mut value_cond = z3::ast::Bool::from_bool(&ctx, false);
        value_cond |= !(&condition_bb & condition_b_not_zero);
        value_cond |= !&condition_cc;
        value_cond |= &condition_aa;
        solver.assert(&value_cond);
    }
}
