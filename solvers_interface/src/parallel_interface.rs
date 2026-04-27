use crate::{PossibleResult, SafetyVerification};
use crate::{civer_interface, ffsol_interface, cvc5_interface, z3_interface};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::mpsc::RecvTimeoutError;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

/// Runs FFSOL, CVC5, Z3, and CIVER simultaneously and returns the first decisive
/// result (VERIFIED or FAILED). If all solvers return UNKNOWN the function
/// returns UNKNOWN together with the merged logs.
pub fn study_safety(problem: &SafetyVerification) -> (PossibleResult, Vec<String>) {
    let start = Instant::now();
    println!("ALL: Starting parallel safety verification with FFSOL, FFSOL-NOLINEAR, CVC5, Z3, and CIVER...");
    let (tx, rx) = mpsc::channel::<(&'static str, PossibleResult, Vec<String>)>();
    let cancel_token = Arc::new(AtomicBool::new(false));

    let solvers: &[&str] = &[
        "ffsol",
        "ffsol-nolinear",
        "cvc5",
        "z3",
        "civer",
    ];

    let n_solvers = solvers.len();
    let mut winner: Option<(&'static str, PossibleResult, Vec<String>)> = None;
    let mut winner_elapsed_secs: Option<f64> = None;
    let mut unknown_count = 0usize;
    let mut fallback_logs: Vec<String> = Vec::new();

    thread::scope(|scope| {
        for name in solvers {
            let tx = tx.clone();
            let problem_clone = problem.clone();
            let cancel_token = Arc::clone(&cancel_token);
            let name = *name;

            scope.spawn(move || {
                if cancel_token.load(Ordering::Relaxed) {
                    return;
                }

                println!("ALL: launching solver {}", name);
                let result = match name {
                    "ffsol" => ffsol_interface::study_safety_with_cancel(&problem_clone, &cancel_token,&ffsol_interface::FfsolConfig::default(problem_clone.verification_timeout, problem_clone.verbose),
                    ),
                    "ffsol-nolinear" => ffsol_interface::study_safety_with_cancel(&problem_clone, &cancel_token,&ffsol_interface::FfsolConfig::linear_diactivated(problem_clone.verification_timeout, problem_clone.verbose),
                    ),
                    "cvc5" => cvc5_interface::study_safety_with_cancel(&problem_clone, &cancel_token),
                    "z3" => z3_interface::study_safety_with_cancel(&problem_clone, &cancel_token),
                    "civer" => civer_interface::study_safety_with_cancel(&problem_clone, &cancel_token),
                    _ => (PossibleResult::UNKNOWN, vec!["UNKNOWN SOLVER IN ALL MODE\n".to_string()]),
                };

                // Ignore send errors if receiver already decided.
                let _ = tx.send((name, result.0, result.1));
            });
        }

        // Close channel when all worker tx clones are dropped.
        drop(tx);

        let global_timeout = Duration::from_millis(problem.verification_timeout);

        loop {
            let elapsed = start.elapsed();
            if elapsed >= global_timeout {
                cancel_token.store(true, Ordering::SeqCst);
                fallback_logs.push(format!(
                    "### ALL: GLOBAL TIMEOUT REACHED AFTER {:.6} seconds\n",
                    elapsed.as_secs_f64()
                ));
                break;
            }

            let remaining = global_timeout - elapsed;
            match rx.recv_timeout(remaining) {
                Ok((name, result, logs)) => {
                    match result {
                        PossibleResult::VERIFIED | PossibleResult::FAILED => {
                            cancel_token.store(true, Ordering::SeqCst);
                            winner = Some((name, result, logs));
                            winner_elapsed_secs = Some(start.elapsed().as_secs_f64());
                            break;
                        }
                        _ => {
                            unknown_count += 1;
                            fallback_logs.push(format!("### ALL: {} returned UNKNOWN\n", name));
                            fallback_logs.extend(logs);
                            if unknown_count == n_solvers {
                                break;
                            }
                        }
                    }
                }
                Err(RecvTimeoutError::Timeout) => {
                    cancel_token.store(true, Ordering::SeqCst);
                    fallback_logs.push("### ALL: GLOBAL TIMEOUT WAITING FOR SOLVER RESPONSES\n".to_string());
                    break;
                }
                Err(RecvTimeoutError::Disconnected) => {
                    break;
                }
            }
        }

        // Signal every remaining solver to stop as early as possible.
        cancel_token.store(true, Ordering::SeqCst);
    });

    if let Some((winner_solver, result, mut logs)) = winner {
        let decisive_elapsed = winner_elapsed_secs.unwrap_or_else(|| start.elapsed().as_secs_f64());
        let total_elapsed = start.elapsed().as_secs_f64();
        println!(
            "ALL: winner solver = {}, decisive result = {:?}",
            winner_solver,
            result
        );
        println!("ALL: time to decisive result = {:.6} seconds", decisive_elapsed);
        println!("ALL: total time including cleanup = {:.6} seconds", total_elapsed);
        logs.push(format!(
            "### ALL: FIRST DECISIVE ANSWER = {:?}, FOUND BY SOLVER {}\n",
            result,
            winner_solver
        ));
        logs.push(format!("### ALL: TIME TO DECISIVE RESULT = {:.6} seconds\n", decisive_elapsed));
        logs.push(format!("### ALL: TOTAL TIME INCLUDING CLEANUP = {:.6} seconds\n", total_elapsed));
        (result, logs)
    } else {
        let elapsed = start.elapsed().as_secs_f64();
        println!("ALL: no decisive result, final result = UNKNOWN");
        println!("ALL: total time including cleanup = {:.6} seconds", elapsed);
        fallback_logs.push("### UNKNOWN: ALL PARALLEL SOLVERS TIMED OUT\n".to_string());
        fallback_logs.push(format!("### ALL: TOTAL TIME INCLUDING CLEANUP = {:.6} seconds\n", elapsed));
        (PossibleResult::UNKNOWN, fallback_logs)
    }
}
