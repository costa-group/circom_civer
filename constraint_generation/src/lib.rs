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
use std::collections::{HashMap, BTreeMap};
use std::fs::File;
use std::io::Write;
use serde::{Serialize,Deserialize};



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
    pub initial_constraints_file: String,
    pub structure_file: String,
    pub apply_deduction_assigned: bool
}

#[derive(Debug, Copy, Clone)]
pub struct FlagsExecution{
    pub verbose: bool,
    pub inspect: bool,
}

pub type ConstraintWriter = Box<dyn ConstraintExporter>;
type BuildResponse = Result<(ConstraintWriter, VCP), ()>;

#[derive(Deserialize,Serialize, Debug)]
pub struct TimingInfo{
    pub graph_construction: f32,
    pub clustering: f32,
    pub dag_construction: f32,
    pub equivalency: f32,
    pub total: f32,
}

#[derive(Deserialize,Serialize, Debug, Clone)]
pub struct NodeInfo{
    pub node_id: usize,
    pub constraints: Vec<usize>, //ids of the constraints
    pub input_signals: Vec<usize>,
    pub output_signals: Vec<usize>,
    pub signals: Vec<usize>, 
    pub successors: Vec<usize> //ids of the successors 

}

#[derive(Deserialize, Serialize, Debug)]
pub struct StructureInfo {
    pub timing: TimingInfo,
    pub nodes: Vec<NodeInfo>, //all the nodes of the circuit, position of the node is not the position.
    pub local_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
    pub structural_equivalency: Vec<Vec<usize>>, //equivalence classes, each inner vector is a class
}


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

    let always_check = true;
    if config.check_tags ||config.check_postconditions || config.check_safety || always_check{
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
            config.apply_deduction_assigned,
            &config.civer_file,
            &config.initial_constraints_file,
            &config.structure_file
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
        apply_deduction_assigned: bool, name: &String, name_initial: &String,
        name_structure: &String
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
        check_safety, add_tags_info, add_postconditions_info,
        apply_deduction_assigned
    );

    let mut number_constraints = HashMap::new();
    let mut number_components = HashMap::new();
    let mut init_constraint_to_node =  BTreeMap::new();
    
    let mut equivalence_nodes = HashMap::new();
    let mut node_info = Vec::new();


    let mut init_c = 0;
    count_constraints_node(&tree_constraints, &mut number_constraints, &mut number_components, &mut init_constraint_to_node, &mut init_c);
    std::fs::write(
        name_initial,
        serde_json::to_string_pretty(&init_constraint_to_node).unwrap(),
    );


    let mut init_c = 0;
    let mut node_id = 0;
    build_structure_nodes(&tree_constraints, &mut node_id, &mut init_c, &mut node_info, &mut equivalence_nodes);
    let aux_timing = TimingInfo{
        graph_construction: 0.0,
        clustering: 0.0,
        dag_construction: 0.0,
        equivalency: 0.0,
        total: 0.0
    };

    let equiv_to_vec: Vec<Vec<usize>> = equivalence_nodes.into_iter()
                                        .map(|(_id, class)| class)
                                        .collect();
    let structure = StructureInfo{
        timing: aux_timing,
        nodes: node_info,
        local_equivalency: equiv_to_vec.clone(),
        structural_equivalency: equiv_to_vec
    };
     
    std::fs::write(
        name_structure,
        serde_json::to_string_pretty(&structure).unwrap(),
    );

    let mut total_cons  = 0;
    let mut total_verified = 0;

    let mut total_comps  = 0;
    let mut total_comps_verified = 0;

    if check_safety{
        (total_cons, total_verified) = compute_percentage_verified(&studied_nodes, &number_constraints);
        (total_comps, total_comps_verified) = compute_percentage_verified(&studied_nodes, &number_components);
    }

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
        println!("  * Percentage of verified constraints: {} - ({} / {})", (total_verified as f64 / total_cons as f64) * 100.0, total_verified, total_cons);
        println!("  * Percentage of verified components: {} - ({} / {})", (total_comps_verified as f64 / total_comps as f64) * 100.0, total_comps_verified, total_comps);

        
        
        println!("\n");

    }

    println!("--------------------------------------------");
    println!("--------------------------------------------\n");

}

fn count_constraints_node(
    tree_constraints: &TreeConstraints,
    number_constraints: &mut HashMap<String, usize>,
    number_components: &mut HashMap<String, usize>,
    init_constraint_to_node: &mut BTreeMap<usize, String>,
    init_c: &mut usize,
){
    let node_constraints = tree_constraints.constraints().len();
    let node_name = tree_constraints.pretty_template_name();
    init_constraint_to_node.insert(*init_c, node_name.clone());

    if number_constraints.contains_key(node_name){
        let value = number_constraints.get_mut(node_name).unwrap();
        *value += node_constraints;
        let number_components = number_components.get_mut(node_name).unwrap();
        *number_components += 1;
    } else{
        number_constraints.insert(node_name.clone(), node_constraints);
        number_components.insert(node_name.clone(), 1);
    }
    *init_c += node_constraints;
    for subcomponent in tree_constraints.subcomponents(){
        count_constraints_node(subcomponent, number_constraints, number_components, init_constraint_to_node, init_c);
    }
}

fn build_structure_nodes(
    tree_constraints: &TreeConstraints,
    node_id: &mut usize,
    init_c: &mut usize,
    node_info: &mut Vec<NodeInfo>,
    equivalence_nodes: &mut HashMap<usize, Vec<usize>>,
) -> usize{
    
    let my_node_id = *node_id;
    *node_id += 1;

    let equivalence_node_id = tree_constraints.node_id();
    if equivalence_nodes.contains_key(&equivalence_node_id){
        let ref_equiv = equivalence_nodes.get_mut(&equivalence_node_id).unwrap();
        ref_equiv.push(my_node_id);

    } else{
        equivalence_nodes.insert(equivalence_node_id, vec![my_node_id]);
    }

    let mut constraints = Vec::new();
    for i in 0..tree_constraints.constraints().len(){
        constraints.push(*init_c + i);
    }
    *init_c += tree_constraints.constraints().len();

    let mut output_signals = Vec::new();
    for i in 0..tree_constraints.number_outputs(){
        output_signals.push(tree_constraints.initial_signal() + i);
    } 

    let mut input_signals = Vec::new();
    for i in 0..tree_constraints.number_inputs(){
        input_signals.push(tree_constraints.initial_signal() + tree_constraints.number_outputs() + i);
    } 

    let mut signals = Vec::new();
    for i in 0..tree_constraints.number_signals(){
        signals.push(tree_constraints.initial_signal() + i);
    } 

    let new_node = NodeInfo{
        node_id: my_node_id,
        constraints,
        input_signals,
        output_signals,
        signals,
        successors: Vec::new()
    };
    node_info.push(new_node);

    let mut successors = Vec::new();
    for subcomponent in tree_constraints.subcomponents(){
        successors.push(
            build_structure_nodes(subcomponent, node_id, init_c, node_info, equivalence_nodes)
        );
    }
    node_info[my_node_id].successors = successors;

    my_node_id
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
    apply_deduction_assigned: bool,
) -> Vec<String>{
    if !studied_nodes.contains_key(tree_constraints.pretty_template_name()){
        let mut number_tags_postconditions = tree_constraints.get_no_tags_postconditions();
        let mut number_postconditions = tree_constraints.get_no_postconditions();
        let mut logs = Vec::new();
        for subcomponent in tree_constraints.subcomponents(){
            logs.append(&mut check_tags_node(subcomponent, studied_nodes, field,
                verification_timeout, check_tags, check_postconditions, 
                check_safety, add_tags_info, add_postconditions_info,
                apply_deduction_assigned
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
            apply_deduction_assigned
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

fn compute_percentage_verified(
    studied_nodes: & HashMap<String, ((usize, usize), (PossibleResult, PossibleResult, PossibleResult))>, 
    number_constraints: & HashMap<String, usize>,
) -> (usize, usize){
    let mut total_cons = 0;
    let mut verified_cons = 0;
    for (name, n_cons) in number_constraints{
        let (_, (_, _, result)) = studied_nodes.get(name).unwrap();
        total_cons += n_cons;
        if *result == PossibleResult::VERIFIED{
            verified_cons += n_cons;
        }
    }
    (total_cons, verified_cons)
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
