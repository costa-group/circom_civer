use crate::EquivalenceVerification;
use crate::{PossibleResult,SafetyVerification,CorrectnessVerification};
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use std::collections::LinkedList;
use std::io::Read;
use wait_timeout::ChildExt;
use std::fs::File;
use std::io::Write;
use rand::Rng;
use std::os::unix::process::CommandExt;
use std::thread;
use nix::unistd::Pid;
use nix::sys::signal::Signal;
use nix::sys::signal::killpg;
use std::fs;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use crate::smt2_utils::{safety_problem_to_smt2,equivalence_problem_to_smt2,correctness_problem_to_smt2};


pub fn study_correctness(problem: &CorrectnessVerification)-> (PossibleResult, Vec<String>){
    let mut logs = Vec::new();
    
    let smt2_problem: LinkedList<String> = correctness_problem_to_smt2(problem);

    let result_solver = handling_cvc5_call(&smt2_problem, problem.verification_timeout,problem.verbose, None);

    match result_solver{
        PossibleResult::VERIFIED=>{
            logs.push(format!("### THE CONSTRAINT SYSTEMS AND THE FORMULA ARE NOT EQUIVALENT. FOUND COUNTEREXAMPLE USING SMT:\n"));
        },
        PossibleResult::FAILED=>{
            logs.push(format!("### THE CONSTRAINT SYSTEM AND THE FORMULA ARE EQUIVALENT\n"));
        },
        PossibleResult::UNKNOWN=>{
            logs.push("### UNKNOWN: VERIFICATION OF CORRECTNESS TIMEOUT\n".to_string());
        },
        _=>{
            unreachable!()
        }

    }

    (result_solver, logs)

}


pub fn study_equivalence(problem: &EquivalenceVerification)-> (PossibleResult, Vec<String>){
    let mut logs = Vec::new();
    
    let smt2_problem: LinkedList<String> = equivalence_problem_to_smt2(problem,false);

    let result_solver = handling_cvc5_call(&smt2_problem, problem.verification_timeout,problem.verbose, None);

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
    
    let mut logs = Vec::new();
    
    let smt2_problem: LinkedList<String> = safety_problem_to_smt2(problem);

    let result_solver = handling_cvc5_call(&smt2_problem, problem.verification_timeout,problem.verbose, None);

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
    let mut logs = Vec::new();

    if cancel_flag.load(Ordering::Relaxed) {
        logs.push("### CANCELLED BEFORE STARTING CVC5\n".to_string());
        return (PossibleResult::UNKNOWN, logs);
    }

    let smt2_problem: LinkedList<String> = safety_problem_to_smt2(problem);
    let result_solver = handling_cvc5_call(&smt2_problem, problem.verification_timeout,problem.verbose, Some(cancel_flag));

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



pub fn handling_cvc5_call(
    smt2_problem: &LinkedList<String>,
    timeout:u64,
    verbose:bool,
    cancel_flag: Option<&AtomicBool>
)-> PossibleResult{
    //produce a random number for the file name
    let mut rng = rand::thread_rng();
    let random_number: u32 = rng.gen();
    let new_file_name = format!("output_{}.smt2", random_number);


    // Ensure the SMT2 text is fully written and flushed to disk before continuing.
    {
        let mut file = File::create(&new_file_name).expect("Unable to create SMT2 file");
        for s in smt2_problem{
            file.write_all(format!("{}\n",s).as_bytes()).expect("Unable to write SMT2 file");
            
        }
        file.sync_all().expect("Failed to sync SMT2 file to disk");
        file.flush().expect("Failed to flush SMT2 file");
        // `file` dropped here
    }
    

    let mut command_args = Vec::new();
    command_args.push(&new_file_name);
    let mut child = unsafe { Command::new("cvc5")
        .args(command_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .pre_exec(|| {
            // Crear un nuevo process group
            libc::setsid();
            
            Ok(())
        })
        .spawn()
        .expect("Failed to execute the command")};


    let mut stdout = child.stdout.take().expect("Failed to take stdout");
    let mut stderr = child.stderr.take().expect("Failed to take stderr");


    let stdout_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout.read_to_end(&mut buf);
        buf
    });

    let stderr_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr.read_to_end(&mut buf);
        buf
    });

// -------------------- timeout/cancel --------------------
    let timeout = Duration::from_millis(timeout);
    let check_step = Duration::from_millis(50);
    let start = Instant::now();

    loop {
        if cancel_flag.map_or(false, |flag| flag.load(Ordering::Relaxed)) {
            let pgid = Pid::from_raw(child.id() as i32);
            let _ = killpg(pgid, Signal::SIGKILL);
            break;
        }

        let elapsed = start.elapsed();
        if elapsed >= timeout {
            let pgid = Pid::from_raw(child.id() as i32);
            let _ = killpg(pgid, Signal::SIGKILL);
            break;
        }

        let remaining = timeout - elapsed;
        let step = if remaining < check_step { remaining } else { check_step };

        match child.wait_timeout(step)
            .expect("Failed while waiting for the process")
        {
            Some(_) => break,
            None => {}
        };
    }

    // Esperar al proceso principal (NO wait_with_output)
    let status = child.wait().expect("Failed to wait on child");

    // Recoger stdout / stderr (ya no bloquea)
    let stdout = stdout_handle.join().expect("stdout thread panicked");
    let stderr = stderr_handle.join().expect("stderr thread panicked");

    // -------------------- output final --------------------
    let output = std::process::Output {
        status,
        stdout,
        stderr,
    };
    let stdout = String::from_utf8_lossy(&output.stdout);

    if !verbose{
        match fs::remove_file(&new_file_name) {
            Ok(_) => {},
            Err(e) => eprintln!("Error when eliminating the file: {}", e),
        }
    }

    if let Some(ultima_linea) = stdout.lines().rev().find(|l| !l.trim().is_empty()) {
        if ultima_linea == "unsat" { 
            PossibleResult::VERIFIED
       	} else if ultima_linea == "sat" {
            PossibleResult::FAILED
	    } else{
            PossibleResult::UNKNOWN
        }
    } else{
        PossibleResult::UNKNOWN
    }
}