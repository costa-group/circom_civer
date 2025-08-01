use super::{Constraint, Edge, Node, SimplificationFlags, Tree, DAG};
use constraint_list::{ConstraintList, DAGEncoding, EncodingEdge, EncodingNode, SignalInfo, Simplifier};
use program_structure::utils::constants::UsefulConstants;
use std::collections::{HashSet, LinkedList};
use crate::TreeConstraints;

#[derive(Default)]
struct CHolder {
    linear: LinkedList<Constraint>,
    equalities: LinkedList<Constraint>,
    constant_equalities: LinkedList<Constraint>,
}

fn map_tree_constraints(
    tree: &Tree,
    witness: &mut Vec<usize>,
    c_holder: &mut CHolder,
    forbidden: &mut HashSet<usize>,
    tree_constraints: &mut TreeConstraints,
) -> usize {
    let mut no_constraints = 0;

    for signal in &tree.signals {
        Vec::push(witness, *signal);
        if tree.dag.nodes[tree.node_id].is_custom_gate {
            forbidden.insert(*signal);
        }
    }

    tree_constraints.template_name = tree.dag.nodes[tree.node_id].template_name.clone();
    tree_constraints.pretty_template_name = tree.dag.nodes[tree.node_id].pretty_template_name.clone();
    tree_constraints.is_custom = tree.dag.nodes[tree.node_id].is_custom_gate;
    tree_constraints.number_signals = tree.signals.len();
    tree_constraints.number_inputs = tree.dag.nodes[tree.node_id].inputs_length;
    tree_constraints.number_outputs = tree.dag.nodes[tree.node_id].outputs_length;
    tree_constraints.preconditions = tree.preconditions.clone();
    tree_constraints.preconditions_intermediates = tree.preconditions_intermediates.clone();
    tree_constraints.postconditions_intermediates = tree.postconditions_intermediates.clone();
    tree_constraints.postconditions_outputs = tree.postconditions_outputs.clone();
    tree_constraints.facts = tree.facts.clone();
    tree_constraints.tags_preconditions = tree.tags_preconditions.clone();
    tree_constraints.tags_postconditions_intermediates = tree.tags_postconditions_intermediates.clone();
    tree_constraints.tags_postconditions_outputs = tree.tags_postconditions_outputs.clone();
    if tree_constraints.number_signals > 0{
        tree_constraints.initial_signal = tree.signals[0];
    }

    tree_constraints.node_id = tree.node_id;

    for constraint in &tree.constraints {
        tree_constraints.constraints.push(constraint.clone());
        if Constraint::is_constant_equality(constraint) {
            LinkedList::push_back(&mut c_holder.constant_equalities, constraint.clone());
        } else if Constraint::is_equality(constraint, &tree.field) {
            LinkedList::push_back(&mut c_holder.equalities, constraint.clone());
        } else if Constraint::is_linear(constraint) {
            LinkedList::push_back(&mut c_holder.linear, constraint.clone());
        } else {
            no_constraints += 1;
        }
    }

    for edge in Tree::get_edges(tree) {
        let subtree = Tree::go_to_subtree(tree, edge);
        let mut subtree_constraints = TreeConstraints::default();
        no_constraints += map_tree_constraints(&subtree, witness, c_holder, forbidden, &mut subtree_constraints);
        tree_constraints.subcomponents.push_back(subtree_constraints);
    }
    no_constraints
}

fn map_tree(
    tree: &Tree,
    witness: &mut Vec<usize>,
    c_holder: &mut CHolder,
    forbidden: &mut HashSet<usize>
) -> usize {
    let mut no_constraints = 0;

    for signal in &tree.signals {
        Vec::push(witness, *signal);
        if tree.dag.nodes[tree.node_id].is_custom_gate {
            forbidden.insert(*signal);
        }
    }

    for constraint in &tree.constraints {
        if Constraint::is_constant_equality(constraint) {
            LinkedList::push_back(&mut c_holder.constant_equalities, constraint.clone());
        } else if Constraint::is_equality(constraint, &tree.field) {
            LinkedList::push_back(&mut c_holder.equalities, constraint.clone());
        } else if Constraint::is_linear(constraint) {
            LinkedList::push_back(&mut c_holder.linear, constraint.clone());
        } else {
            no_constraints += 1;
        }
    }

    for edge in Tree::get_edges(tree) {
        let subtree = Tree::go_to_subtree(tree, edge);
        no_constraints += map_tree(&subtree, witness, c_holder, forbidden);
    }
    no_constraints
}

fn produce_encoding(
    no_constraints: usize,
    init: usize,
    dag_nodes: Vec<Node>,
    dag_edges: Vec<Vec<Edge>>,
) -> DAGEncoding {
    let mut adjacency = Vec::new();
    let mut nodes = Vec::new();
    let mut id = 0;
    for node in dag_nodes {
        let encoded = map_node_to_encoding(id, node);
        Vec::push(&mut nodes, encoded);
        id += 1;
    }
    for edges in dag_edges {
        let mut encoded = Vec::new();
        for edge in edges {
            let new = map_edge_to_encoding(edge);
            Vec::push(&mut encoded, new);
        }
        Vec::push(&mut adjacency, encoded);
    }
    DAGEncoding { init, no_constraints, nodes, adjacency }
}

fn map_node_to_encoding(id: usize, node: Node) -> EncodingNode {
    let mut signals = Vec::new();
    let mut ordered_signals = Vec::new();
    let locals = node.locals;
    let mut non_linear = LinkedList::new();
    for c in node.constraints {
        if !Constraint::is_linear(&c) {
            LinkedList::push_back(&mut non_linear, c);
        }
    }

    for signal in node.ordered_signals {
        let signal_numbering = node.signal_correspondence.get(&signal).unwrap();
        ordered_signals.push(*signal_numbering);
    }

    for (name, id) in node.signal_correspondence {
        if HashSet::contains(&locals, &id) {
            let new_signal = SignalInfo { name, id };
            Vec::push(&mut signals, new_signal);
        }
    }
    signals.sort_by(|a, b| a.id.cmp(&b.id));

    EncodingNode {
        id,
        name: node.template_name,
        parameters: node.parameters,
        signals,
        ordered_signals,
        non_linear,
        is_custom_gate: node.is_custom_gate,
    }
}

fn map_edge_to_encoding(edge: Edge) -> EncodingEdge {
    EncodingEdge { goes_to: edge.goes_to, path: edge.label, offset: edge.in_number }
}

pub fn map(dag: DAG, flags: SimplificationFlags) -> ConstraintList {
    use std::time::SystemTime;
    // println!("Start of dag to list mapping");
    let now = SystemTime::now();
    let constants = UsefulConstants::new(&dag.prime);
    let field = constants.get_p().clone();
    let init_id = dag.main_id();
    let no_public_inputs = dag.public_inputs();
    let no_public_outputs = dag.public_outputs();
    let no_private_inputs = dag.private_inputs();
    let mut forbidden = dag.get_main().unwrap().forbidden_if_main.clone();
    let mut c_holder = CHolder::default();
    let mut signal_map = vec![0];
    let no_constraints = map_tree(&Tree::new(&dag), &mut signal_map, &mut c_holder, &mut forbidden);
    let max_signal = Vec::len(&signal_map);
    let name_encoding = produce_encoding(no_constraints, init_id, dag.nodes, dag.adjacency);
    let _dur = now.elapsed().unwrap().as_millis();
    // println!("End of dag to list mapping: {} ms", dur);
    Simplifier {
        field,
        no_public_inputs,
        no_public_outputs,
        no_private_inputs,
        forbidden,
        max_signal,
        dag_encoding: name_encoding,
        linear: c_holder.linear,
        equalities: c_holder.equalities,
        cons_equalities: c_holder.constant_equalities,
        no_rounds: flags.no_rounds,
        flag_s: flags.flag_s,
        parallel_flag: flags.parallel_flag,
        flag_old_heuristics: flags.flag_old_heuristics,
        port_substitution: flags.port_substitution,
    }
    .simplify_constraints()
}


pub fn map_to_constraint_tree(dag: &DAG) -> TreeConstraints {

    let mut c_holder = CHolder::default();
    let mut tree_constraints = TreeConstraints::default();
    let mut signal_map = vec![0];
    let mut forbidden = dag.get_main().unwrap().forbidden_if_main.clone();
    let _ = map_tree_constraints(&Tree::new(&dag), &mut signal_map, &mut c_holder,  &mut forbidden, &mut tree_constraints);
    
    tree_constraints
}