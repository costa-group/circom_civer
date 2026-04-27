pub mod tags_checking;
pub mod safety_z3;

use self::tags_checking::TemplateVerification;
use crate::{PossibleResult, SafetyVerification};
use std::sync::atomic::{AtomicBool, Ordering};

pub use self::tags_checking::TemplateVerification as CiverTemplateVerification;

pub fn study_safety(problem: &SafetyVerification) -> (PossibleResult, Vec<String>) {
    let mut template_verification = TemplateVerification::new(problem);
    template_verification.deduce()
}

pub fn study_safety_with_cancel(
    problem: &SafetyVerification,
    cancel_flag: &AtomicBool,
) -> (PossibleResult, Vec<String>) {
    if cancel_flag.load(Ordering::Relaxed) {
        return (
            PossibleResult::UNKNOWN,
            vec!["### CANCELLED BEFORE STARTING CIVER\n".to_string()],
        );
    }

    let mut template_verification = TemplateVerification::new(problem);
    template_verification.deduce_with_cancel(cancel_flag)
}