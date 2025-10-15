extern crate num_bigint_dig as num_bigint;
extern crate num_traits;

mod compute_constants;
mod environment_utils;
mod execute;
mod execution_data;

use ansi_term::Colour;
use circom_algebra::algebra::{ArithmeticError, ArithmeticExpression};
use compiler::hir::very_concrete_program::VCP;
use constraint_list::ConstraintList;
use constraint_writers::ConstraintExporter;
use dag::DAG;
use dag::PossibleResult;
use dag::TreeConstraints;
use execution_data::executed_program::ExportResult;
use execution_data::ExecutedProgram;
use program_structure::ast::{self};
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::FileID;
use program_structure::program_archive::ProgramArchive;
use std::rc::Rc;
use num_bigint_dig::BigInt;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;


pub struct BuildConfig {
    pub no_rounds: usize,
    pub flag_json_sub: bool,
    pub flag_s: bool,
    pub flag_f: bool,
    pub flag_p: bool,
    pub flag_verbose: bool,
    pub flag_old_heuristics: bool,
    pub inspect_constraints: bool,
    pub prime: String,
    pub civer: bool,
    pub verification_timeout: u64,
    pub check_tags: bool,
    pub check_postconditions: bool,
    pub check_safety: bool,
    pub add_tags_info: bool,
    pub add_postconditions_info: bool,
    pub civer_file: String,
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
    if config.check_tags ||config.check_postconditions || config.check_safety{
        if !config.civer{
            eprintln!("{}", Colour::Yellow.paint("Not including tag specifications: in case you want to add extra tag specifications, use the flag --civer followed by the name of the file including the specifications (example: --civer tags.circom)"));
        }
        let tree_constraints = dag.map_to_constraint_tree();
        check_tags(
            tree_constraints,
            &config.prime, 
            config.verification_timeout, 
            config.check_tags, 
            config.check_postconditions, 
            config.check_safety, 
            config.add_tags_info, 
            config.add_postconditions_info,
            &config.civer_file
        );
        
    }
    if config.flag_f {
        sync_dag_and_vcp(&mut vcp, &mut dag);
        Result::Ok((Box::new(dag), vcp))
    } else {
        let list = simplification_process(&mut vcp, dag, &config);
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

fn check_tags(tree_constraints: TreeConstraints, prime: &String,
        verification_timeout: u64, check_tags: bool, check_postconditions: bool,
        check_safety: bool, add_tags_info: bool,add_postconditions_info: bool,
        name: &String,
    )
    {
    use program_structure::constants::UsefulConstants;

    let mut studied_nodes: HashMap<String, ((usize, usize), (PossibleResult, PossibleResult, PossibleResult))> = HashMap::new();
        
    let constants = UsefulConstants::new(prime);
    let field = constants.get_p().clone();
    
    let mut tags_verified = Vec::new();
    let mut post_verified = Vec::new();
    let mut tags_failed = Vec::new();
    let mut post_failed = Vec::new();
    let mut tags_timeout = Vec::new();
    let mut post_timeout = Vec::new();
    let mut safety_verified = Vec::new();
    let mut safety_failed = Vec::new();
    let mut safety_timeout = Vec::new();

    
    let result_create = File::create(name);
    let mut cfile = if result_create.is_ok(){
        result_create.unwrap()
    } else{
        unreachable!("Should not enter here")
    };
    let logs = check_tags_node(&tree_constraints, &mut studied_nodes, &field,
        verification_timeout, check_tags, check_postconditions,
        check_safety, add_tags_info, add_postconditions_info
    );
    for l in logs {
        let _result =  cfile.write_all(l.as_bytes());
    }
    let _result = cfile.flush();

    for (component, (_, (result_tags, result_post, result_safety))) in &studied_nodes{
        //print!("Component {}: ", component);
        if check_tags{
            match result_tags{
                PossibleResult::FAILED => {
                	//println!("TAGS VERIFICATION FAILED || ");
                	tags_failed.push(component);
                }
                	
                PossibleResult::UNKNOWN => {
                	//println!("TAGS VERIFICATION UNKNOWN  || ");
                	tags_timeout.push(component);
                }

                PossibleResult::TOO_BIG => {
                	//println!("TAGS VERIFICATION UNKNOWN  || ");
                	tags_timeout.push(component);
                }
                _ => {
                    //print!("TAGS VERIFIED || ");
                    tags_verified.push(component);
                }
            }
        }
        if check_postconditions{
            match result_post{
                PossibleResult::FAILED => {
                	//println!("POSTCONDITIONS VERIFICATION FAILED || ");
                	post_failed.push(component);
                },
                PossibleResult::UNKNOWN => {
                	//println!("POSTCONDITIONS VERIFICATION UNKNOWN  || ");
                	post_timeout.push(component);
                }
                PossibleResult::TOO_BIG => {
                	//println!("POSTCONDITIONS VERIFICATION UNKNOWN  || ");
                	post_timeout.push(component);
                }
                _ => {
                    //print!("POSTCONDITIONS VERIFIED || ");
                    post_verified.push(component);
                }
            }
        }
        if check_safety{
            match result_safety{
                PossibleResult::FAILED => {
                    safety_failed.push(component);
                    //println!("WEAK SAFETY VERIFICATION FAILED || ");
                },
                PossibleResult::UNKNOWN => {
                    safety_timeout.push(component);
                    //println!("WEAK SAFETY VERIFICATION UNKNOWN  || ");
                },
                PossibleResult::TOO_BIG => {
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

    if check_tags{
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
    if check_postconditions{
        if post_failed.is_empty() && post_timeout.is_empty(){
        	println!("-> All postconditions were verified :)");
        } else{
        	println!("-> CIVER could not verify all postconditions");
        	if !post_failed.is_empty(){
        		println!("Components that do not satisfy their postconditions: ");
        		for c in &post_failed{
        			println!("    - {}, ", c);
        		}
        	}
        	if !post_timeout.is_empty(){
        		println!("Components timeout when checking postconditions: ");
        		for c in &post_timeout{
        			println!("    - {}, ", c);
        		}
        	}
        }

        println!("  * Number of verified components (postconditions): {}", post_verified.len());
        println!("  * Number of failed components (postconditions): {}", post_failed.len());
        println!("  * Number of timeout components (postconditions): {}", post_timeout.len());
        println!("\n");
    }

    if check_safety{
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
        println!("\n");

    }

    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

}

fn check_tags_node(
    tree_constraints: &TreeConstraints, 
    studied_nodes: &mut HashMap<String, ((usize, usize), (PossibleResult, PossibleResult, PossibleResult))>, 
    field:&BigInt,
    verification_timeout: u64, 
    check_tags: bool, 
    check_postconditions: bool, 
    check_safety: bool, 
    add_tags_info: bool, 
    add_postconditions_info: bool,
) -> Vec<String>{
    if !studied_nodes.contains_key(tree_constraints.pretty_template_name()){
        let mut number_tags_postconditions = tree_constraints.get_no_tags_postconditions();
        let mut number_postconditions = tree_constraints.get_no_postconditions();
        let mut logs = Vec::new();
        for subcomponent in tree_constraints.subcomponents(){
            logs.append(&mut check_tags_node(subcomponent, studied_nodes, field,
                verification_timeout, check_tags, check_postconditions, 
                check_safety, add_tags_info, add_postconditions_info,
            ));
            number_tags_postconditions += studied_nodes.get(subcomponent.pretty_template_name()).unwrap().0.0;
            number_postconditions += studied_nodes.get(subcomponent.pretty_template_name()).unwrap().0.1;

        }

        let (result_tags, result_post, result_safety, mut new_logs) = tree_constraints.check_tags(
            field,
            verification_timeout,
            check_tags,
            check_postconditions, 
            check_safety, 
            add_tags_info, 
            add_postconditions_info,
        );
        logs.append(&mut new_logs);
        logs.push("\n\n".to_string());
        let result_component = (result_tags, result_post, result_safety);
        studied_nodes.insert(tree_constraints.pretty_template_name().clone(), ((number_tags_postconditions, number_postconditions), result_component));
        logs
    } else{
        Vec::new()
    }
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
        no_rounds: config.no_rounds,
        flag_old_heuristics: config.flag_old_heuristics,
        prime : config.prime.clone(),
    };
    let list = DAG::map_to_list(dag, flags);
    VCP::add_witness_list(vcp, Rc::new(list.get_witness_as_vec()));
    list
}
