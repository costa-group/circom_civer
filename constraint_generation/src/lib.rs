extern crate num_bigint_dig as num_bigint;
extern crate num_traits;

mod compute_constants;
mod environment_utils;
mod execute;
mod execution_data;
mod assignment_utils;

use ansi_term::Colour;
use circom_algebra::algebra::{ArithmeticError, ArithmeticExpression};
use compiler::hir::very_concrete_program::VCP;
use constraint_list::ConstraintList;
use constraint_writers::ConstraintExporter;
use dag::DAG;
use dag::modular_verification::VerificationTree;
use execution_data::executed_program::ExportResult;
use execution_data::ExecutedProgram;
use program_structure::ast::{self};
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::FileID;
use program_structure::program_archive::ProgramArchive;
use solvers_interface::{PossibleResult, PossibleSolver, VerificationConfig};
use std::rc::Rc;
use std::collections::{HashMap, };
use num_bigint_dig::BigInt;

pub struct BuildConfig {
    pub no_rounds: usize,
    pub flag_json_sub: bool,
    pub json_substitutions: String,
    pub flag_s: bool,
    pub flag_f: bool,
    pub flag_p: bool,
    pub flag_verbose: bool,
    pub flag_old_heuristics: bool,
    pub inspect_constraints: bool,
    pub prime: String,
    pub check_tags: bool,
    pub check_safety: bool,
    pub add_tags_info: bool,
    pub civer_file: String,
    pub solver: String,
    pub verification_timeout: u64
}

#[derive(Debug, Copy, Clone)]
pub struct FlagsExecution{
    pub verbose: bool,
    pub inspect: bool,
}

pub type ConstraintWriter = Box<dyn ConstraintExporter>;
type BuildResponse = Result<(ConstraintWriter, VCP), ()>;
pub fn build_circuit(program: ProgramArchive, config: BuildConfig) -> BuildResponse {
    let files = program.file_library.clone();
    let flags = FlagsExecution{
        verbose: config.flag_verbose,
        inspect: config.inspect_constraints,
    };
    let (exe, warnings) = instantiation(&program, flags, &config.prime).map_err(|r| {
        Report::print_reports(&r, &files);
    })?;
    Report::print_reports(&warnings, &files);
    let (mut dag, mut vcp, warnings) = export(exe, program, flags).map_err(|r| {
        Report::print_reports(&r, &files);
    })?;
    if config.inspect_constraints {
        Report::print_reports(&warnings, &files);
    }

    if config.check_tags || config.check_safety {
        let solver = match config.solver.as_str(){
            "z3" => PossibleSolver::Z3,
            "civer" => PossibleSolver::CIVER,
            "ffsol" => PossibleSolver::FFSOL,
            "cvc5" => PossibleSolver::CVC5,
            "all" => PossibleSolver::ALL,
            _ => unreachable!()
        };

        let verification_config = VerificationConfig{
            check_tags: config.check_tags,
            check_safety: config.check_safety,
            add_tags_info: config.add_tags_info,
            verbose: config.flag_verbose,
            verification_timeout: config.verification_timeout,
            solver,
        };
        
        let tree_constraints = dag.map_to_verification_tree();
        verify_circuit(
            config.civer_file.clone(),
            tree_constraints,
            &config.prime.clone(), 
            verification_config,
        );
        
    }

    if config.flag_f {
        sync_dag_and_vcp(&mut vcp, &mut dag);
        if config.flag_json_sub { 
            use constraint_writers::json_writer::SubstitutionJSON;
            let substitution_log = SubstitutionJSON::new(&config.json_substitutions).unwrap();
            let _ = substitution_log.end();
            println!("{} {}", Colour::Green.paint("Written successfully:"), config.json_substitutions);
        };

        Result::Ok((Box::new(dag), vcp))
    } else {
        let list = simplification_process(&mut vcp, dag, &config);
        if config.flag_json_sub { 
            println!("{} {}", Colour::Green.paint("Written successfully:"), config.json_substitutions);
        };
        Result::Ok((Box::new(list), vcp))
    }
}

type InstantiationResponse = Result<(ExecutedProgram, ReportCollection), ReportCollection>;
fn instantiation(program: &ProgramArchive, flags: FlagsExecution, prime: &String) -> InstantiationResponse {
    let execution_result = execute::constraint_execution(&program, flags, prime);
    match execution_result {
        Ok((program_exe, warnings)) => {
            let no_nodes = program_exe.number_of_nodes();
            let success = Colour::Green.paint("template instances");
            let nodes_created = format!("{}: {}", success, no_nodes);
            println!("{}", &nodes_created);
            InstantiationResponse::Ok((program_exe,warnings))
        }
        Err(reports) => InstantiationResponse::Err(reports),
    }
}

fn export(exe: ExecutedProgram, program: ProgramArchive, flags: FlagsExecution) -> ExportResult {
    let exported = exe.export(program, flags);
    exported
}

fn sync_dag_and_vcp(vcp: &mut VCP, dag: &mut DAG) {
    let witness = Rc::new(DAG::produce_witness(dag));
    VCP::add_witness_list(vcp, Rc::clone(&witness));
}

fn simplification_process(vcp: &mut VCP, dag: DAG, config: &BuildConfig) -> ConstraintList {
    use dag::SimplificationFlags;
    let flags = SimplificationFlags {
        flag_s: config.flag_s,
        parallel_flag: config.flag_p,
        port_substitution: config.flag_json_sub,
        json_substitutions: config.json_substitutions.clone(),
        no_rounds: config.no_rounds,
        flag_old_heuristics: config.flag_old_heuristics,
        prime : config.prime.clone(),
    };
    let list = DAG::map_to_list(dag, flags);
    VCP::add_witness_list(vcp, Rc::new(list.get_witness_as_vec()));
    list
}

struct NodeInfo{
    tags_result: PossibleResult,
    safety_result: PossibleResult,
    number_postconditions: usize
}
type StudiedNodes = HashMap<String, NodeInfo>;


fn verify_circuit(
    name: String,
    tree_constraints: VerificationTree, 
    prime: &String,
    config: VerificationConfig
)
    {
    use program_structure::constants::UsefulConstants;
    use std::fs::File;
    use std::io::Write;
    let mut studied_nodes = StudiedNodes::new();
    

    let previously_studied_nodes = HashMap::new();
    // Read the structure
    /* 
    if file_studied_nodes.is_some(){
        read_studied_nodes(file_studied_nodes.unwrap(), &mut previously_studied_nodes);
    }
    */

    let constants = UsefulConstants::new(prime);
    let field = constants.get_p().clone();
    
    let mut tags_verified = Vec::new();
    let mut tags_failed = Vec::new();
    let mut tags_timeout = Vec::new();
    let mut safety_verified = Vec::new();
    let mut safety_failed = Vec::new();
    let mut safety_timeout = Vec::new();

    
    let result_create = File::create(name);
    let mut cfile = if result_create.is_ok(){
        result_create.unwrap()
    } else{
        unreachable!("Should not enter here")
    };
    let logs = verify_node(
        &tree_constraints, 
        &mut studied_nodes, 
        &field,
        config, 
        &previously_studied_nodes
    );



    let mut total_cons  = 0;
    let mut total_verified = 0;

    let mut total_comps  = 0;
    let mut total_comps_verified = 0;

    let mut number_constraints = HashMap::new();
    let mut number_components = HashMap::new();

    count_constraints_node(&tree_constraints, &mut number_constraints, &mut number_components);


    if config.check_safety{
        (total_cons, total_verified) = compute_percentage_verified(&studied_nodes, &number_constraints);
        (total_comps, total_comps_verified) = compute_percentage_verified(&studied_nodes, &number_components);
    }

    for l in logs {
        let _result =  cfile.write_all(l.as_bytes());
    }
    let _result = cfile.flush();

    for (component, node_info) in &studied_nodes{
        //print!("Component {}: ", component);
        if config.check_tags{
            match node_info.tags_result{
                PossibleResult::FAILED => {
                	//println!("TAGS VERIFICATION FAILED || ");
                	tags_failed.push(component);
                }
                	
                PossibleResult::UNKNOWN => {
                	//println!("TAGS VERIFICATION UNKNOWN  || ");
                	tags_timeout.push(component);
                }
                _ => {
                    //print!("TAGS VERIFIED || ");
                    tags_verified.push(component);
                }
            }
        }

        if config.check_safety{
            match node_info.safety_result{
                PossibleResult::FAILED => {
                    safety_failed.push(component);
                    //println!("WEAK SAFETY VERIFICATION FAILED || ");
                },
                PossibleResult::UNKNOWN => {
                    safety_timeout.push(component);
                    //println!("WEAK SAFETY VERIFICATION UNKNOWN  || ");
                },
                _ => {
                    safety_verified.push(component);
                    //print!("WEAK SAFETY VERIFIED || ");
                }
            }
        }
    }

    let _postconditions_total = studied_nodes.get(tree_constraints.pretty_template_name()).unwrap();
    println!();

    println!("--------------------------------------------");
    println!("--------------------------------------------");
    println!("-------- CIVER VERIFICATION RESULTS --------");
    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

    if config.check_tags{
        if tags_failed.is_empty() && tags_timeout.is_empty(){
        	println!("-> All tags were verified :)");
        } else{
        	println!("-> CIVER could not verify all postconditions");
        	if !tags_failed.is_empty(){
        		println!("Components whose tags do not satisfy their specification: ");
        		for c in &tags_failed{
        			println!("    - {}, ", c);
        		}
        	}
        	if !tags_timeout.is_empty(){
        		println!("Components timeout when checking tags specifications: ");
        		for c in &tags_timeout{
        			println!("    - {}, ", c);
        		}
        	}
        }

        println!("  * Number of verified components (tags): {}", tags_verified.len());
        println!("  * Number of failed components (tags): {}", tags_failed.len());
        println!("  * Number of timeout components (tags): {}", tags_timeout.len());
        println!("\n");
    } 

    if config.check_safety{
        if safety_failed.is_empty() && safety_timeout.is_empty(){
        	println!("-> All components satisfy weak safety :)");
        } else{
        	println!("-> CIVER could not verify weak safety of all components");
        	if !safety_failed.is_empty(){
        		println!("Components that do not satisfy weak safety: ");
        		for c in &safety_failed{
        			println!("    - {}, ", c);
        		}
        	}
        	if !safety_timeout.is_empty(){
        		println!("Components timeout when checking weak-safety: ");
        		for c in &safety_timeout{
        			println!("    - {}, ", c);
        		}
        	}
        }
        println!("  * Number of verified components (weak-safety): {}", safety_verified.len());
        println!("  * Number of failed components (weak-safety): {}", safety_failed.len());
        println!("  * Number of timeout components (weak-safety): {}", safety_timeout.len());
        println!("  * Percentage of verified constraints: {} - ({} / {})", (total_verified as f64 / total_cons as f64) * 100.0, total_verified, total_cons);
        println!("  * Percentage of verified components: {} - ({} / {})", (total_comps_verified as f64 / total_comps as f64) * 100.0, total_comps_verified, total_comps);

        
        
        println!("\n");

    }

    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

}


fn verify_node(
    tree_constraints: &VerificationTree, 
    studied_nodes: &mut StudiedNodes, 
    field:&BigInt,
    config: VerificationConfig,
    previously_studied_nodes: &HashMap<String, PossibleResult>
) -> Vec<String>{
    if previously_studied_nodes.contains_key(tree_constraints.pretty_template_name()){
        let previous_result = previously_studied_nodes.get(tree_constraints.pretty_template_name()).unwrap();
        studied_nodes.insert(
            tree_constraints.pretty_template_name().clone(),
            NodeInfo { tags_result: PossibleResult::VERIFIED, safety_result: previous_result.clone(), number_postconditions: 0 }
        );
        Vec::new()
    } else{
        if !studied_nodes.contains_key(tree_constraints.pretty_template_name()){
            let mut number_postconditions = tree_constraints.get_no_postconditions();
            let mut logs = Vec::new();
            for subcomponent in tree_constraints.subcomponents(){
                logs.append(&mut verify_node(subcomponent, studied_nodes, field,
                    config, previously_studied_nodes
                ));
                number_postconditions += studied_nodes.get(subcomponent.pretty_template_name()).unwrap().number_postconditions;

            }

            let (safety_result, tags_result, mut new_logs) = tree_constraints.verify_tree(
                field,
                config,
            );
            logs.append(&mut new_logs);
            logs.push("\n\n".to_string());
            studied_nodes.insert(
                tree_constraints.pretty_template_name().clone(), 
                NodeInfo { 
                    tags_result, 
                    safety_result, 
                    number_postconditions
                }
            );
            logs
        } else{
            Vec::new()
        }
    }
}

fn count_constraints_node(
    tree_constraints: &VerificationTree,
    number_constraints: &mut HashMap<String, usize>,
    number_components: &mut HashMap<String, usize>,
){
    let node_constraints = tree_constraints.constraints().len();
    let node_name = tree_constraints.pretty_template_name();

    if number_constraints.contains_key(node_name){
        let value = number_constraints.get_mut(node_name).unwrap();
        *value += node_constraints;
        let number_components = number_components.get_mut(node_name).unwrap();
        *number_components += 1;
    } else{
        number_constraints.insert(node_name.clone(), node_constraints);
        number_components.insert(node_name.clone(), 1);
    }
    for subcomponent in tree_constraints.subcomponents(){
        count_constraints_node(subcomponent, number_constraints, number_components);
    }
}

fn compute_percentage_verified(
    studied_nodes: &StudiedNodes, 
    number_constraints: & HashMap<String, usize>,
) -> (usize, usize){
    let mut total_cons = 0;
    let mut verified_cons = 0;
    for (name, n_cons) in number_constraints{
        let result = studied_nodes.get(name).unwrap();
        total_cons += n_cons;
        if result.safety_result == PossibleResult::VERIFIED{
            verified_cons += n_cons;
        }
    }
    (total_cons, verified_cons)
}

