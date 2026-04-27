use crate::{PossibleResult,SafetyVerification,EquivalenceVerification};

use std::fs::File;
use std::io::Write;
use rand::Rng;

use z3::Config;
use z3::Context;
use z3::Solver;
use z3::ast::Ast;
use z3::*;
use num_bigint_dig::BigInt;

use std::collections::HashMap;
use circom_algebra::algebra::Constraint;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;

pub fn study_equivalence(problem: &EquivalenceVerification)-> (PossibleResult, Vec<String>){
    
    let (result_solver, mut logs) = try_prove_equivalence_with_z3(problem);

    match result_solver{
        PossibleResult::VERIFIED=>{
            logs.push(format!("### THE CONSTRAINT SYSTEMS ARE NOT EQUIVALENT. FOUND COUNTEREXAMPLE USING SMT:\n"));
        },
        PossibleResult::FAILED=>{
            logs.push(format!("### THE CONSTRAINT SYSTEMS ARE EQUIVALENT\n"));
        },
        PossibleResult::UNKNOWN=>{
            logs.push("### UNKNOWN: VERIFICATION OF EQUIVALENCE TIMEOUT\n".to_string());
        },
        _=>{
            unreachable!()
        }

    }

    (result_solver, logs)

}



pub fn study_safety(problem: &SafetyVerification)-> (PossibleResult, Vec<String>){
    
    
    let (result_solver,mut logs) = try_prove_safety_with_z3(problem);

    match result_solver{
        PossibleResult::VERIFIED=>{
            logs.push(format!("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"));
        },
        PossibleResult::FAILED=>{
            logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
        },
        PossibleResult::UNKNOWN=>{
            logs.push("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n".to_string());
        },
        _=>{
            unreachable!()
        }

    }

    (result_solver, logs)
}

pub fn study_safety_with_cancel(problem: &SafetyVerification, cancel_flag: &AtomicBool)-> (PossibleResult, Vec<String>){
    if cancel_flag.load(Ordering::Relaxed) {
        return (PossibleResult::UNKNOWN, vec!["### CANCELLED BEFORE STARTING Z3\n".to_string()]);
    }

    let (result_solver, mut logs) = try_prove_safety_with_z3_cancel(problem, cancel_flag);

    match result_solver{
        PossibleResult::VERIFIED=>{
            logs.push(format!("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"));
        },
        PossibleResult::FAILED=>{
            logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
        },
        PossibleResult::UNKNOWN=>{
            logs.push("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n".to_string());
        },
        _=>{
            unreachable!()
        }

    }

    (result_solver, logs)
}

pub fn try_prove_safety_with_z3_cancel(
    problem: &SafetyVerification,
    cancel_flag: &AtomicBool,
) -> (PossibleResult,Vec<String>) {

    try_prove_safety_with_z3_internal(problem, Some(cancel_flag))
}

fn try_prove_safety_with_z3_internal(
    problem: &SafetyVerification,
    cancel_flag: Option<&AtomicBool>,
) -> (PossibleResult,Vec<String>) {

    let logs = Vec::new();
    let mut cfg = Config::new();
    cfg.set_timeout_msec(problem.verification_timeout);
    let ctx = Context::new(&cfg);
    let mut solver = Solver::new(&ctx);
    let mut signals_1_to_smt_rep = HashMap::new();
    let mut signals_2_to_smt_rep = HashMap::new();

    for s in &problem.signals {
        let z3_s = declare_signal(&mut solver,format!("s1_{}",s),&problem.field);
        signals_1_to_smt_rep.insert(*s, z3_s);

        let z3_s2 = declare_signal(&mut solver,format!("s2_{}",s),&problem.field);
        signals_2_to_smt_rep.insert(*s, z3_s2);
    }

    for constraint in &problem.constraints {
        declare_constraint(&constraint, &solver, &signals_1_to_smt_rep, &problem.field);
        declare_constraint(&constraint, &solver, &signals_2_to_smt_rep, &problem.field);
        if problem.apply_deduction_assigned{
            apply_deduction_assigned(&constraint, &solver, &signals_1_to_smt_rep, &signals_2_to_smt_rep);
        }
    }

    let equal_inputs = declare_all_signals_equal(
        &solver,
        &problem.inputs,
        &signals_1_to_smt_rep,
        &problem.inputs,
        &signals_2_to_smt_rep
    );
    solver.assert(&equal_inputs);

    let equal_outputs = declare_all_signals_equal(
        &solver,
        &problem.outputs,
        &signals_1_to_smt_rep,
        &problem.outputs,
        &signals_2_to_smt_rep
    );
    solver.assert(&!equal_outputs);

    if problem.verbose{
        let mut rng = rand::thread_rng();
        let random_number: u32 = rng.gen();
        let new_file_name = format!("output_{}.smt2", random_number);

        let mut file: File = File::create(&new_file_name).expect("Unable to create SMT2 file");
        file.write_all(format!("{}",solver).as_bytes()).expect("Unable to write SMT2 file");
        file.sync_all().expect("Failed to sync SMT2 file to disk");
        file.flush().expect("Failed to flush SMT2 file");
    }

    if cancel_flag.map_or(false, |flag| flag.load(Ordering::Relaxed)) {
        return (PossibleResult::UNKNOWN, vec!["### CANCELLED BEFORE CHECKING Z3\n".to_string()]);
    }

    let finished = AtomicBool::new(false);
    let result = thread::scope(|scope| {
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

        let result = match solver.check() {
            SatResult::Sat => PossibleResult::FAILED,
            SatResult::Unsat => PossibleResult::VERIFIED,
            _ => PossibleResult::UNKNOWN,
        };

        finished.store(true, Ordering::SeqCst);
        result
    });

    (result, logs)
}




pub fn try_prove_equivalence_with_z3(
    problem: &EquivalenceVerification
) -> (PossibleResult,Vec<String>) {

    let logs = Vec::new();
    let mut cfg = Config::new();
    cfg.set_timeout_msec(problem.verification_timeout);
    let ctx = Context::new(&cfg);
    let mut solver = Solver::new(&ctx);
    let mut signals_1_to_smt_rep = HashMap::new();
    let mut signals_2_to_smt_rep = HashMap::new();

    for s in &problem.signals_1 {
        let z3_s = declare_signal(&mut solver,format!("s1_{}",s),&problem.field);
        signals_1_to_smt_rep.insert(*s, z3_s);
        
    }

    for s in &problem.signals_2 {
        let z3_s = declare_signal(&mut solver,format!("s2_{}",s),&problem.field);
        signals_2_to_smt_rep.insert(*s, z3_s);
        
    }

    for constraint in &problem.constraints_1 {
        declare_constraint(&constraint, &solver, &signals_1_to_smt_rep, &problem.field);
    }

    for constraint in &problem.constraints_2 {
        declare_constraint(&constraint, &solver, &signals_2_to_smt_rep, &problem.field);
    }

    let equal_inputs = declare_all_signals_equal(
        &solver, 
        &problem.inputs_1, 
        &signals_1_to_smt_rep, 
        &problem.inputs_2,
        &signals_2_to_smt_rep
    );
    solver.assert(&equal_inputs);

    let equal_outputs = declare_all_signals_equal(
        &solver, 
        &problem.outputs_1, 
        &signals_1_to_smt_rep, 
        &problem.outputs_2,
        &signals_2_to_smt_rep
    );
    solver.assert(&!equal_outputs);

    if problem.verbose{
        //produce a random number for the file name
        let mut rng = rand::thread_rng();
        let random_number: u32 = rng.gen();
        let new_file_name = format!("output_{}.smt2", random_number);

        // Ensure the SMT2 text is fully written and flushed to disk before continuing.
        let mut file: File = File::create(&new_file_name).expect("Unable to create SMT2 file");
        file.write_all(format!("{}",solver).as_bytes()).expect("Unable to write SMT2 file");
        file.sync_all().expect("Failed to sync SMT2 file to disk");
        file.flush().expect("Failed to flush SMT2 file");
    }


    let result = match solver.check() {
        SatResult::Sat => {
            // logs.push(format!(
            //     "### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"
            // ));

            // let model = solver.get_model().unwrap();
            // for s in &problem.inputs_1 {
            //     let v = model
            //         .eval(signals_1_to_smt_rep.get(s).unwrap(), true)
            //         .unwrap();
            //     logs.push(format!("Input signal {}: {}\n", s, v.to_string()));
            // }
            // for s in &problem.outputs_1 {
            //     let v = model
            //         .eval(signals_1_to_smt_rep.get(s).unwrap(), true)
            //         .unwrap();
            //     let v1 = model
            //         .eval(signals_2_to_smt_rep.get(s).unwrap(), true)
            //         .unwrap();

            //     logs.push(format!(
            //         "Output signal {}: values {} | {}\n",
            //         s,
            //         v.to_string(),
            //         v1.to_string()
            //     ));
            // }

            PossibleResult::FAILED
        }
        SatResult::Unsat => {
            //logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
            PossibleResult::VERIFIED
        }
        _ => {
            //logs.push(format!(
            //    "### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n"
            //));
            PossibleResult::UNKNOWN
        }
    };
    
    (result, logs)
}


pub fn try_prove_safety_with_z3(
    problem: &SafetyVerification
) -> (PossibleResult,Vec<String>) {
    try_prove_safety_with_z3_internal(problem, None)
}


pub fn declare_signal<'a>(
    solver: &z3::Solver<'a>,
    signal_name: String,
    field: &BigInt
) -> z3::ast::Int<'a> {
    let ctx: &Context = solver.get_context();
    let signal = z3::ast::Int::new_const(ctx, signal_name);

    let zero = z3::ast::Int::from_i64(ctx, 0);
    let prime = z3::ast::Int::from_str(ctx, &field.to_string()).unwrap();

    solver.assert(&signal.ge(&zero)); // >=0
    solver.assert(&signal.lt(&prime)); // < prime

    signal
}


pub fn declare_constraint(
    constraint: &Constraint<usize>,
    solver: &z3::Solver,
    signals_to_z3: &HashMap<usize, z3::ast::Int>,
    field: &BigInt,
) {
    let ctx: &Context = solver.get_context();

    let mut value_a = z3::ast::Int::from_u64(ctx, 0);
    let mut value_b = z3::ast::Int::from_u64(ctx, 0);
    let mut value_c = z3::ast::Int::from_u64(ctx, 0);

    for (signal, value) in constraint.a() {
        if *signal == 0 {
            value_a += &z3::ast::Int::from_str(&ctx, &value.to_string()).unwrap()
        } else {
            value_a += signals_to_z3.get(signal).unwrap()
                * &z3::ast::Int::from_str(&ctx, &value.to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.b() {
        if *signal == 0 {
            value_b += &z3::ast::Int::from_str(&ctx, &value.to_string()).unwrap()
        } else {
            value_b += signals_to_z3.get(signal).unwrap()
                * &z3::ast::Int::from_str(&ctx, &value.to_string()).unwrap();
        }
    }
    for (signal, value) in constraint.c() {
        if *signal == 0 {
            value_c += &z3::ast::Int::from_str(&ctx, &value.to_string()).unwrap()
        } else {
            value_c += signals_to_z3.get(signal).unwrap()
                * &z3::ast::Int::from_str(&ctx, &value.to_string()).unwrap();
        }
    }

    let prime = z3::ast::Int::from_str(ctx, &field.to_string()).unwrap();
    let value_left = (value_c - (value_a * value_b)).modulo(&prime);
    let value_right = z3::ast::Int::from_i64(ctx, 0);
    solver.assert(&value_left._eq(&value_right));

}

pub fn declare_all_signals_equal<'a>(
    solver: &z3::Solver<'a>,
    signals_1: &Vec<usize>, 
    signal_1_to_z3: &HashMap<usize,z3::ast::Int<'a>>, 
    signals_2: &Vec<usize>, 
    signal_2_to_z3: &HashMap<usize,z3::ast::Int<'a>>
)->z3::ast::Bool<'a>{
    let ctx: &Context = solver.get_context();
    let mut all_equal = z3::ast::Bool::from_bool(&ctx, true);
    for i in 0..signals_1.len(){
        let s_1 = signal_1_to_z3.get(&signals_1[i]).unwrap();
        let s_2 = signal_2_to_z3.get(&signals_2[i]).unwrap();
        all_equal &= s_1._eq(s_2);

    }

    all_equal
}



pub fn apply_deduction_assigned(
    c: &Constraint<usize>,
    solver: &Solver,
    signals_to_smt_symbols_1: &HashMap<usize, z3::ast::Int>,
    signals_to_smt_symbols_2: &HashMap<usize, z3::ast::Int>,
) {
        let ctx: &Context = solver.get_context();

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