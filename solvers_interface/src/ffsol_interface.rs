use crate::smt2_utils::tag_verification_problem_to_smt2;
use crate::{CompleteVerificationResult, PossibleResult, VerificationProblem};
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


#[derive(Clone)]
pub struct FfsolConfig {
    pub timeout: u64,
    pub use_cocoa: bool,
    pub model: Option<String>,
    pub success: bool,
    pub prime: Option<String>,
    pub apply_la_incremental: bool,
    pub apply_nra: bool,
    pub apply_nia: bool,
    pub sequential: bool,
    pub light_check_determinism: bool,
    pub apply_la: bool,
    pub la_with_overflowing_constraints: bool,
    pub linear_solver: bool,
    pub grobner_basis: bool,
    pub simple_deductions: bool,
    pub complete_deductions: bool,
    pub complete_non_overflowing_deductions: bool,
    pub gb_mode: String,
    pub gb_timeout: u64,
    pub inconsistent_timeout: u64,
    pub inconsistent_continue_on_timeout: bool,
    pub verbose: bool,
}

impl FfsolConfig {
    pub fn default(timeout: u64, verbose: bool) -> Self {
        Self {
            timeout,
            use_cocoa: true,
            model: None,
            success: false,
            prime: None,
            apply_la_incremental: true,
            apply_nra: true,
            apply_nia: true,
            sequential: false,
            light_check_determinism: true,
            apply_la: true,
            la_with_overflowing_constraints: false,
            linear_solver: true,
            grobner_basis: true,
            simple_deductions: true,
            complete_deductions: false,
            complete_non_overflowing_deductions: true,
            gb_mode: "parallel".to_string(),
            gb_timeout: 0,
            inconsistent_timeout: 0,
            inconsistent_continue_on_timeout: false,
            verbose,
        }
    }

    pub fn linear_diactivated(timeout: u64, verbose: bool) -> Self {
        let mut config = Self::default(timeout, verbose);
        config.linear_solver = false;
        config
    }

    pub fn build_args(&self, file_path: &str) -> Vec<String> {
        fn push_bool_arg(args: &mut Vec<String>, flag: &str, value: bool) {
            args.push(flag.to_string());
            args.push(value.to_string());
        }

        fn push_binary_arg(args: &mut Vec<String>, flag: &str, value: bool) {
            args.push(flag.to_string());
            args.push(if value { "1".to_string() } else { "0".to_string() });
        }

        let mut args = Vec::new();
        args.push("-tlimit".to_string());
        args.push(self.timeout.to_string());

        if self.use_cocoa {
            args.push("-using_cocoa".to_string());
        }

        if let Some(model) = &self.model {
            args.push("-model".to_string());
            args.push(model.clone());
        }

        push_bool_arg(&mut args, "-success", self.success);

        if let Some(prime) = &self.prime {
            args.push("-prime".to_string());
            args.push(prime.clone());
        }

        push_bool_arg(&mut args, "-apply_la_incremental", self.apply_la_incremental);
        push_bool_arg(&mut args, "-apply_nra", self.apply_nra);
        push_bool_arg(&mut args, "-apply_nia", self.apply_nia);
        push_bool_arg(&mut args, "-sequential", self.sequential);
        push_binary_arg(&mut args, "-light_check_determinism", self.light_check_determinism);
        push_binary_arg(&mut args, "-apply_la", self.apply_la);
        push_binary_arg(&mut args, "-la_with_overflowing_constraints", self.la_with_overflowing_constraints);
        push_binary_arg(&mut args, "-linear_solver", self.linear_solver);
        push_binary_arg(&mut args, "-grobner_basis", self.grobner_basis);
        push_binary_arg(&mut args, "-simple_deductions", self.simple_deductions);
        push_binary_arg(&mut args, "-complete_deductions", self.complete_deductions);
        push_binary_arg(&mut args, "-complete_non_overflowing_deductions", self.complete_non_overflowing_deductions);
        args.push("-gb_mode".to_string());
        args.push(self.gb_mode.clone());
        args.push("-gb_timeout".to_string());
        args.push(self.gb_timeout.to_string());
        args.push("-inconsistent_timeout".to_string());
        args.push(self.inconsistent_timeout.to_string());
        push_bool_arg(&mut args, "-inconsistent_continue_on_timeout", self.inconsistent_continue_on_timeout);

        args.push("-file".to_string());
        args.push(file_path.to_string());
        args
    }
}




pub fn solve_problem(
    problem: &VerificationProblem
) -> CompleteVerificationResult{
    use crate::smt2_utils::safety_problem_to_smt2;

    let mut logs = Vec::new();
    // todo: add verbose and timeout to config
    let config = FfsolConfig::default(problem.config.verification_timeout, problem.config.verbose);

    let safety_result = if problem.config.check_safety{

        logs.push(format!("### STUDYING SAFETY \n"));

        let smt2_problem: LinkedList<String> = safety_problem_to_smt2(problem);

        let result_solver = handling_ffsol_call(&smt2_problem, &problem.template_name, &config, None);

        match result_solver{
            PossibleResult::VERIFIED=>{
                logs.push(format!("### WEAK SAFETY ENSURED BY THE TEMPLATE\n"));
            },
            PossibleResult::FAILED=>{
                logs.push(format!("### THE TEMPLATE DOES NOT ENSURE SAFETY. FOUND COUNTEREXAMPLE USING SMT:\n"));
            },
            PossibleResult::UNKNOWN=>{
                logs.push("### UNKNOWN: VERIFICATION OF WEAK SAFETY USING THE SPECIFICATION TIMEOUT\n".to_string());
            },
            _=>{
                unreachable!()
            }
        }

        Some(result_solver)
    } else{
        None
    };

    let tags_result = if problem.config.check_tags{
        logs.push(format!("### STUDYING TAG CORRECTNESS \n"));

        let smt2_problem: LinkedList<String> = tag_verification_problem_to_smt2(problem);

        let result_solver = handling_ffsol_call(&smt2_problem, &problem.template_name, &config, None);

        match result_solver{
            PossibleResult::VERIFIED=>{
                logs.push(format!("### TAG CORRECTNESS ENSURED BY THE TEMPLATE\n"));
            },
            PossibleResult::FAILED=>{
                logs.push(format!("### THE TEMPLATE DOES NOT ENSURE TAG CORRECTNESS. FOUND COUNTEREXAMPLE USING SMT:\n"));
            },
            PossibleResult::UNKNOWN=>{
                logs.push("### UNKNOWN: VERIFICATION OF TAG CORRECTNESS USING THE SPECIFICATION TIMEOUT\n".to_string());
            },
            _=>{
                unreachable!()
            }
        }

        Some(result_solver)
    } else{
        None
    };

    CompleteVerificationResult { safety_result, tags_result, logs }

}



fn handling_ffsol_call(
    smt2_problem: &LinkedList<String>,
    filename: &String,
    config: &FfsolConfig,
    cancel_flag: Option<&AtomicBool>
)-> PossibleResult{

    //produce a random number for the file name
    let mut rng = rand::thread_rng();
    let random_number: u32 = rng.gen();
    let short_filename = filename.split("(").next().unwrap();
    let new_file_name = format!("{}_{}.smt2", short_filename,random_number);

    // Ensure the SMT2 text is fully written and flushed to disk before continuing.
    {
        let mut file: File = File::create(&new_file_name).expect("Unable to create SMT2 file");
        for s in smt2_problem{
            file.write_all(format!("{}\n",s).as_bytes()).expect("Unable to write SMT2 file");
            
        }
        file.sync_all().expect("Failed to sync SMT2 file to disk");
        file.flush().expect("Failed to flush SMT2 file");
        // `file` dropped here
    }
    

    let command_args = config.build_args(&new_file_name);
    let mut child = unsafe { Command::new("ffsol")
        .args(command_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .pre_exec(|| {
            // Create a new process group
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
    let timeout = Duration::from_millis(config.timeout);
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

    if !config.verbose{
        match fs::remove_file(&new_file_name) {
            Ok(_) => {},
            Err(e) => eprintln!("Error al eliminar el archivo: {}", e),
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

#[cfg(test)]
mod tests {
    use super::FfsolConfig;

    #[test]
    fn default_config_matches_ffsol_help_defaults() {
        let config = FfsolConfig::default(0, false);

        assert!(!config.success, "ffsol help defaults -success to false");
        assert!(config.apply_la_incremental, "ffsol help defaults -apply_la_incremental to true");
        assert!(config.apply_nra, "ffsol help defaults -apply_nra to true");
        assert!(config.apply_nia, "ffsol help defaults -apply_nia to true");
        assert!(!config.sequential, "ffsol help defaults -sequential to false");
        assert!(config.apply_la, "ffsol help defaults -apply_la to true");
        assert!(!config.la_with_overflowing_constraints, "ffsol help defaults -la_with_overflowing_constraints to false");
        assert!(config.linear_solver, "ffsol help defaults -linear_solver to true");
        assert!(config.grobner_basis, "ffsol help defaults -grobner_basis to true");
        assert!(config.simple_deductions, "ffsol help defaults -simple_deductions to true");
        assert!(!config.complete_deductions, "ffsol help defaults -complete_deductions to false");
        assert!(config.complete_non_overflowing_deductions, "ffsol help defaults -complete_non_overflowing_deductions to true");
        assert_eq!(config.gb_mode, "cocoa");
        assert_eq!(config.gb_timeout, 0);
        assert_eq!(config.inconsistent_timeout, 0);
        assert!(!config.inconsistent_continue_on_timeout);
    }
}

