/* 
pub mod civer_interface;
pub mod cvc5_interface;
pub mod z3_interface;
pub mod parallel_interface;
*/
pub mod civer_interface;
pub mod ffsol_interface;
mod smt2_utils;
mod civer;


use std::collections::{HashMap, LinkedList};
use circom_algebra::num_bigint::BigInt;
use program_structure::ast::{ExpressionInfixOpcode, ExpressionPrefixOpcode, Expression};
type Constraint = circom_algebra::algebra::Constraint<usize>;




#[derive(PartialEq, Eq, Clone, Copy)] 
pub enum PossibleSolver{
    PICUS, CIVER, FFSOL, CVC5, Z3, ALL
}


#[derive(Clone)]
pub struct SafetyImplication{
    pub left: Vec<usize>,
    pub right: Vec<usize>,
}

#[derive(Clone)]
pub struct ExecutedImplication{
    pub left: Vec<Expression>,
    pub right: Vec<Expression>,
}

#[derive(Clone, Copy)] 
pub struct VerificationConfig{
    pub check_tags: bool,
    pub check_safety: bool,
    /// Assume the specifications of the tags of the outputs and intermediates,
    /// and of the outputs of the subcomponents, when proving weak safety.
    pub add_tags_info: bool,
    pub solver: PossibleSolver,
    pub verbose: bool,
    pub verification_timeout: u64
}

#[derive(Clone, Debug)]
pub struct ExecutedInequation<C>{
    pub signal: C,
    pub min: BigInt,
    pub max: BigInt,
} 
impl <C> ExecutedInequation<C>{

    pub fn update_bounds(&mut self, min: BigInt, max: BigInt) -> bool{
        let mut updated = false;
        if self.min < min{
            self.min = min;
            updated = true;
        }
        if self.max > max{
            self.max = max;
            updated = true;
        } 
        updated
    }

    pub fn implies_bounds(&self, min: &BigInt, max: &BigInt) -> bool{
        self.min >= *min && self.max <= *max
    }
}

pub type Signal2Bounds = HashMap<usize, ExecutedInequation<usize>>;

pub struct VerificationProblem {
    pub template_name: String,
    pub signals: LinkedList<usize>,
    pub initial_signal: usize,
    pub number_outputs: usize,
    pub number_inputs: usize,
    pub specification_preconditions: Vec<Expression>,
    pub specification_intermediates: Vec<Expression>,
    pub specification_postconditions : Vec<Expression>,
    pub constraints: Vec<Constraint>,
    pub tags_implications: Vec<ExecutedImplication>,
    pub implications_safety: Vec<SafetyImplication>,
    pub field: BigInt,
    pub config: VerificationConfig,
}

impl VerificationProblem{
    pub fn solve_problem(&self)-> CompleteVerificationResult{
        match self.config.solver{
            PossibleSolver::FFSOL => ffsol_interface::solve_problem(&self),
            PossibleSolver::CIVER => civer_interface::solve_problem(&self),
            _ => todo!()
        }
    }
}
#[derive(PartialEq, Eq, Clone)] 
pub enum PossibleResult{
    VERIFIED, UNKNOWN, FAILED, NOSTUDIED, NOTHING
} impl PossibleResult {
    pub fn finished_verification(&self) -> bool{
        // Depending if fast or not, it includes the childrens when timeout
        let fast_check = true;
        if fast_check{
            self == &PossibleResult::VERIFIED || self == &PossibleResult::NOSTUDIED || self == &PossibleResult::NOTHING || self == &PossibleResult::UNKNOWN
        }else{
            self == &PossibleResult::VERIFIED || self == &PossibleResult::NOSTUDIED || self == &PossibleResult::NOTHING
        }    
    }
    pub fn result_to_str(&self)-> String{
        match self{
            &PossibleResult::FAILED => {format!("FAILED -> FOUND COUNTEREXAMPLE\n")}
            &PossibleResult::UNKNOWN => {format!("UNKNOWN -> VERIFICATION TIMEOUT\n")}
            &PossibleResult::NOTHING => {format!("NOTHING TO VERIFY\n")}
            _ => {format!("VERIFIED\n")}
        }
    }
}


pub struct CompleteVerificationResult {
    pub safety_result: Option<PossibleResult>,
    pub tags_result: Option<PossibleResult>,
    pub logs: Vec<String>
}