use crate::smt2_utils::{tag_obligation_to_smt2, tag_obligations_to_smt2, tag_verification_problem_to_smt2};
use crate::{report_obligation, CompleteVerificationResult, PossibleResult, VerificationProblem};
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


/// Name of the SMT2 file of a query: the kind of query (safety or tags), the
/// name of the template and, for a single tag obligation, its label, with every
/// run of other characters turned into one '_'. The obligation
/// `output #3 [binary]` of `Num2Bits(254)` becomes
/// `tags_Num2Bits_254_output_3_binary_<n>.smt2`. The files are kept under
/// --verbose, and the name says which query each one is: cutting it at the
/// first parenthesis would lose the parameters of the template, and a number
/// would not identify the obligation, since a later round numbers the pending
/// ones again from 1.
fn smt_file_name(kind: &str, filename: &str, random_number: u32) -> String {
    let mut safe = String::new();
    for c in filename.chars() {
        if c.is_ascii_alphanumeric() {
            safe.push(c);
        } else if !safe.ends_with('_') {
            safe.push('_');
        }
    }
    let mut safe = safe.trim_matches('_').to_string();
    // the parameters of a template can be whole arrays of constants (the round
    // constants of Poseidon), far beyond the 255 bytes a file name may have:
    // keep the beginning and a hash of the whole name, so that it stays unique
    if safe.len() > MAX_NAME_LEN {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        filename.hash(&mut hasher);
        safe = format!("{}_{:016x}", safe[..MAX_NAME_LEN].trim_end_matches('_'), hasher.finish());
    }
    format!("{}_{}_{}.smt2", kind, safe, random_number)
}

/// Longest part of a file name taken from the name of the template and the
/// label, well below the 255 bytes of most file systems.
const MAX_NAME_LEN: usize = 150;

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

        let result_solver = handling_ffsol_call(&smt2_problem, &problem.template_name, &config, None, "safety");

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

    let mut tag_obligation_results: Vec<(String, PossibleResult)> = Vec::new();

    let tags_result = if problem.config.check_tags && problem.config.split_tags{
        Some(solve_tags_adaptive(problem, &config, &mut tag_obligation_results, &mut logs))
    } else if problem.config.check_tags{
        logs.push(format!("### STUDYING TAG CORRECTNESS \n"));

        let smt2_problem: LinkedList<String> = tag_verification_problem_to_smt2(problem);

        let result_solver = handling_ffsol_call(&smt2_problem, &problem.template_name, &config, None, "tags");

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

    CompleteVerificationResult { safety_result, tags_result, tag_obligation_results, logs }

}


/// Adaptive strategy: one query with all the obligations first, which is cheap
/// when it closes, and only if it comes back unknown retry them one at a time.
/// Both branches prove the same set, so what is verified never depends on which
/// one closes it.
fn solve_tags_adaptive(
    problem: &VerificationProblem,
    config: &FfsolConfig,
    results: &mut Vec<(String, PossibleResult)>,
    logs: &mut Vec<String>,
) -> PossibleResult {

    if problem.tag_obligations.is_empty(){
        logs.push(format!("### NOTHING TO VERIFY: NO TAG OBLIGATIONS\n"));
        return PossibleResult::NOTHING;
    }

    if !problem.config.always_split_tags{
        logs.push(format!("### STUDYING TAG CORRECTNESS, ALL {} OBLIGATIONS TOGETHER \n",
            problem.tag_obligations.len()));

        let all: Vec<&crate::TagObligation> = problem.tag_obligations.iter().collect();
        let smt2_problem: LinkedList<String> = tag_obligations_to_smt2(problem, &all);
        let result = handling_ffsol_call(&smt2_problem, &problem.template_name, config, None, "tags");

        match result{
            PossibleResult::VERIFIED=>{
                logs.push(format!("### TAG CORRECTNESS ENSURED BY THE TEMPLATE\n"));
                for o in &problem.tag_obligations{
                    results.push((o.label.clone(), PossibleResult::VERIFIED));
                }
                return PossibleResult::VERIFIED;
            },
            PossibleResult::FAILED=>{
                // sat on the combined query only says that some obligation
                // fails, not which one: split to find out
                logs.push(format!("### SOME OBLIGATION FAILS, SPLITTING TO FIND WHICH ONE\n"));
            },
            _=>{
                logs.push(format!("### COMBINED ATTEMPT TIMED OUT, SPLITTING\n"));
            }
        }
    }

    solve_tags_one_by_one(problem, config, results, logs)
}


/// Proves the obligations one by one: one query per obligation, each with the
/// full per component timeout. Aggregation: any refuted obligation refutes the
/// template; otherwise any obligation left unknown leaves it unknown.
///
/// A counterexample does not stop the round: the remaining obligations are
/// still tried. The counterexample may come from the abstraction of the
/// children, and every obligation proven now is one the next round, with their
/// constraints, no longer has to retry.
fn solve_tags_one_by_one(
    problem: &VerificationProblem,
    config: &FfsolConfig,
    results: &mut Vec<(String, PossibleResult)>,
    logs: &mut Vec<String>,
) -> PossibleResult {

    logs.push(format!("### STUDYING TAG CORRECTNESS, ONE OBLIGATION AT A TIME \n"));

    let total = problem.tag_obligations.len();
    let mut n_verified = 0;
    let mut n_unknown = 0;
    let mut failed: Vec<&String> = Vec::new();

    for (i, obligation) in problem.tag_obligations.iter().enumerate(){
        let smt2_problem: LinkedList<String> = tag_obligation_to_smt2(problem, obligation);
        let name = format!("{} {}", problem.template_name, obligation.label);
        let started = Instant::now();
        let result = handling_ffsol_call(&smt2_problem, &name, config, None, "tags");
        let elapsed = started.elapsed().as_secs_f64();

        let tag = match result{
            PossibleResult::VERIFIED => { n_verified += 1; "verified" },
            PossibleResult::FAILED => { failed.push(&obligation.label); "COUNTEREXAMPLE" },
            PossibleResult::UNKNOWN => { n_unknown += 1; "timeout" },
            _ => "unknown result",
        };
        logs.push(format!("###   [{}/{}] {}: {}\n", i + 1, total, obligation.label, tag));
        // report as we go: the logs are only flushed to the .civer file at the
        // end, and with hundreds of obligations that is too late to be useful
        report_obligation(&problem.template_name, i + 1, total, &obligation.label,
                          tag, elapsed);
        results.push((obligation.label.clone(), result.clone()));
    }

    logs.push(format!("### OBLIGATIONS: {} verified, {} counterexample, {} timeout, of {}\n",
        n_verified, failed.len(), n_unknown, total));

    if !failed.is_empty(){
        logs.push(format!(
            "### THE TEMPLATE DOES NOT ENSURE TAG CORRECTNESS. FOUND COUNTEREXAMPLE USING SMT FOR:\n"));
        for label in failed{
            logs.push(format!("###   {}\n", label));
        }
        PossibleResult::FAILED
    } else if n_unknown > 0{
        logs.push("### UNKNOWN: VERIFICATION OF TAG CORRECTNESS USING THE SPECIFICATION TIMEOUT\n".to_string());
        PossibleResult::UNKNOWN
    } else{
        logs.push(format!("### TAG CORRECTNESS ENSURED BY THE TEMPLATE\n"));
        PossibleResult::VERIFIED
    }
}


fn handling_ffsol_call(
    smt2_problem: &LinkedList<String>,
    filename: &String,
    config: &FfsolConfig,
    cancel_flag: Option<&AtomicBool>,
    kind: &str,
)-> PossibleResult{

    //produce a random number for the file name
    let mut rng = rand::thread_rng();
    let random_number: u32 = rng.gen();
    let new_file_name = smt_file_name(kind, filename, random_number);

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

