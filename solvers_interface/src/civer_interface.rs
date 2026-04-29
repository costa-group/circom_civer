
use crate::{CompleteVerificationResult, VerificationProblem};
use crate::civer::civer_verification::TemplateVerification;

pub fn solve_problem(problem: &VerificationProblem ) -> CompleteVerificationResult{
    let mut template_verification = TemplateVerification::new(problem);
    template_verification.deduce()
}
