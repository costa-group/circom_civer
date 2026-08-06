use super::executed_bus::BusConnexion;
use super::type_definitions::*;
use super::ExecutedBus;
use circom_algebra::algebra::ArithmeticExpression;
use compiler::hir::very_concrete_program::*;
use dag::DAG;
use num_bigint::BigInt;
use program_structure::ast::{SignalType, Statement, Expression};
use std::collections::{HashMap, HashSet};
use crate::execution_data::AExpressionSlice;
use std::collections::LinkedList;
use program_structure::program_library::tag_specification_data::TagSpecificationInfo;
use program_structure::program_archive::ProgramArchive;
use crate::FlagsExecution;


struct Connexion {
    full_name: String,
    inspect: SubComponentData,
    dag_offset: usize,
    dag_component_offset: usize,
    dag_jump: usize,
    dag_component_jump: usize,
}

#[derive(Clone)]
pub struct PreExecutedTemplate {
    pub template_name: String,
    pub parameter_instances: Vec<AExpressionSlice>,
    pub inputs: HashMap<String, TagNames>,
    pub outputs: HashMap<String, TagNames>,
} 

impl PreExecutedTemplate {
    pub fn new(
        name: String,
        instance: Vec<AExpressionSlice>,
        inputs: HashMap<String, TagNames>,
        outputs: HashMap<String, TagNames>,
    ) -> PreExecutedTemplate {
        PreExecutedTemplate {
            template_name: name,
            parameter_instances: instance,
            inputs,
            outputs,
        }
    }

    pub fn template_name(&self) -> &String {
        &self.template_name
    }

    pub fn parameter_instances(&self) -> &Vec<AExpressionSlice>{
        &self.parameter_instances
    }

    pub fn inputs(&self) -> &HashMap<String, TagNames>{
        &self.inputs
    }

    pub fn outputs(&self) -> &HashMap<String, TagNames> {
        &self.outputs
    }
}



pub struct ExecutedTemplate {
    pub code: Statement,
    pub template_name: String,
    pub report_name: String,
    pub inputs: WireCollector,
    pub outputs: WireCollector,
    pub intermediates: WireCollector,
    pub ordered_signals: WireCollector,
    pub constraints: Vec<Constraint>,
    pub components: ComponentCollector,
    pub number_of_components: usize,
    pub public_inputs: HashSet<String>,
    pub parameter_instances: ParameterContext,
    pub tag_instances: HashMap<String, TagWire>,

    pub signal_to_tags: HashMap<Vec<String>, Vec<String>>, 
    pub signal_to_tags_with_value: HashMap<Vec<String>, BigInt>, 
    // only store the info of the tags with value
    // name of tag -> value
    pub is_parallel: bool,
    pub has_parallel_sub_cmp: bool,
    pub is_custom_gate: bool,
    pub underscored_signals: Vec<String>,
    connexions: Vec<Connexion>,
    pub bus_connexions: HashMap<String, BusConnexion>,
    pub is_extern_c: bool,

    pub specification_preconditions: LinkedList<Expression>,
    pub specification_intermediates: LinkedList<Expression>,
    pub specification_postconditions: LinkedList<Expression>,

}

impl ExecutedTemplate {
    pub fn new(
        public: Vec<String>,
        name: String,
        report_name: String,
        instance: ParameterContext,
        tag_instances: HashMap<String, TagWire>,
        code: Statement,
        is_parallel: bool,
        is_custom_gate: bool,
        is_extern_c: bool
    ) -> ExecutedTemplate {
        let public_inputs: HashSet<_> = public.iter().cloned().collect();


        ExecutedTemplate {
            report_name,
            public_inputs,
            is_parallel,
            has_parallel_sub_cmp: false,
            is_custom_gate,
            code: code.clone(),
            template_name: name,
            parameter_instances: instance,
            signal_to_tags: HashMap::new(),
            signal_to_tags_with_value: HashMap::new(),
            tag_instances,
            inputs: WireCollector::new(),
            outputs: WireCollector::new(),
            intermediates: WireCollector::new(),
            ordered_signals: WireCollector::new(),
            constraints: Vec::new(),
            components: ComponentCollector::new(),
            number_of_components: 0,
            connexions: Vec::new(),
            bus_connexions: HashMap::new(),
            underscored_signals: Vec::new(),
            is_extern_c,
            specification_preconditions: LinkedList::new(),
            specification_intermediates: LinkedList::new(),
            specification_postconditions: LinkedList::new()
        }
    }

    pub fn is_equal(&self, name: &str, context: &ParameterContext, tag_context: &HashMap<String, TagWire>) -> bool {
        self.template_name == name 
            && self.parameter_instances == *context
            && self.tag_instances == *tag_context
    }

    pub fn add_arrow(&mut self, component_name: String, data: SubComponentData) {
        let cnn =
            Connexion { full_name: component_name, inspect: data, dag_offset: 0, dag_component_offset: 0, dag_jump: 0, dag_component_jump: 0};
            self.connexions.push(cnn);
    }

    pub fn add_bus_arrow(&mut self, bus_name: String, data: BusData){
        let cnn =
            BusConnexion { full_name:bus_name.clone(), inspect: data, dag_offset: 0, dag_jump: 0};
            self.bus_connexions.insert(bus_name, cnn);
    }

    pub fn add_input(
        &mut self, 
        input_name: &str, 
        dimensions: &[usize], 
        is_bus: bool
    ) {
        let wire_info = WireData{
            name: input_name.to_string(),
            length: dimensions.to_vec(),
            is_bus
        };
        self.inputs.push(wire_info.clone());
        self.ordered_signals.push(wire_info);
    }

    pub fn add_output(
        &mut self, 
        output_name: &str, 
        dimensions: &[usize], 
        is_bus: bool
    ) {
        let wire_info = WireData{
            name: output_name.to_string(),
            length: dimensions.to_vec(),
            is_bus
        };
        self.outputs.push(wire_info.clone());
        self.ordered_signals.push(wire_info);
    }

    pub fn add_intermediate(
        &mut self, 
        intermediate_name: &str, 
        dimensions: &[usize], 
        is_bus: bool
    ) {
        let wire_info = WireData{
            name: intermediate_name.to_string(),
            length: dimensions.to_vec(),
            is_bus
        };
        self.intermediates.push(wire_info.clone());    
        self.ordered_signals.push(wire_info);
    }

    // Used to update the values of the signals 
    // We call to this function to store the signals with values
    // when we finish the execution of a template
    pub fn add_tag_signal(
        &mut self, 
        mut signal_name: Vec<String>, 
        tag_name: String,
        value: Option<BigInt>
    ){
        let tags_signal = self.signal_to_tags.get_mut(&signal_name);
        match tags_signal{
            None =>{
                self.signal_to_tags.insert(signal_name.clone(), vec![tag_name.clone()]);
            },
            Some(tags)=>{
                tags.push(tag_name.clone());
            }
        }
        if value.is_some(){
            signal_name.push(tag_name);
            self.signal_to_tags_with_value.insert(signal_name, value.unwrap());
        }
    }

    pub fn add_component(&mut self, component_name: &str, dimensions: &[usize], is_anonymous: bool) {
        let comp_data = ComponentData{
            name: component_name.to_string(),
            length: dimensions.to_vec(),
            is_anonymous
        };
        self.components.push(comp_data);
        self.number_of_components += dimensions.iter().fold(1, |p, c| p * (*c));
    }

    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    pub fn add_underscored_signal(&mut self, signal: &str) {
        self.underscored_signals.push(signal.to_string());
    }

    pub fn template_name(&self) -> &String {
        &self.template_name
    }

    pub fn parameter_instances(&self) -> &ParameterContext {
        &self.parameter_instances
    }

    pub fn tag_instances(&self) -> &HashMap<String, TagWire> {
        &self.tag_instances
    }

    pub fn inputs(&self) -> &WireCollector {
        &self.inputs
    }

    pub fn outputs(&self) -> &WireCollector {
        &self.outputs
    }

    pub fn intermediates(&self) -> &WireCollector {
        &self.intermediates
    }

    pub fn insert_in_dag(&mut self, dag: &mut DAG, buses_info : &Vec<ExecutedBus>, spec_context: &SpecificationContext) {
        let parameters = {
            let mut parameters = vec![];
            for (_, data) in self.parameter_instances.clone() {
                let (_, values) = data.destruct();
                for value in as_big_int(values) {
                    parameters.push(value);
                }
            }
            parameters
        }; // repeated code from function build_arguments in export_to_circuit

        dag.add_node(
            self.report_name.clone(),
            self.report_name.clone(), // TODO: improve?
            parameters,
            self.is_parallel,
            self.is_custom_gate
        );
        self.build_wires(dag, buses_info, spec_context);
        self.build_ordered_signals(dag, buses_info);
        self.build_connexions(dag);
        self.build_constraints(dag);
        self.build_specifications(dag);

    }

    fn build_wires(&mut self, dag: &mut DAG, buses_info : &Vec<ExecutedBus>, spec_context: &SpecificationContext) {
        
        let mut specification_preconditions = LinkedList::new();
        let mut specification_intermediates = LinkedList::new();
        let mut specification_postconditions = LinkedList::new();

        
        for wire_data in self.outputs() {
            let state = State { 
                basic_name: wire_data.name.clone(), 
                signal_field_names: vec![wire_data.name.clone()],
                name: wire_data.name.clone(), 
                dim: 0 
            };
            let config = SignalConfig { signal_type: 1, dimensions: &wire_data.length, is_public: false };
            let mut instantiated_spec = if wire_data.is_bus{
                generate_bus_symbols(
                    dag, 
                    state, 
                    &config, 
                    &self.bus_connexions, 
                    buses_info,
                    &self.signal_to_tags,
                    &self.signal_to_tags_with_value,
                    spec_context,
                 )
            } else{
                generate_symbols(
                    dag, 
                    state, 
                    &config,
                    &self.signal_to_tags,
                    &self.signal_to_tags_with_value,
                    spec_context,
                )
            };
            specification_postconditions.append(&mut instantiated_spec);

        }   
        for wire_data in self.inputs() {
            if self.public_inputs.contains(&wire_data.name) {
                let state = State { 
                    basic_name: wire_data.name.clone(), 
                    signal_field_names: vec![wire_data.name.clone()],
                    name: wire_data.name.clone(), 
                    dim: 0 
                };
                let config = SignalConfig { signal_type: 0, dimensions: &wire_data.length, is_public: true };
                let mut instantiated_spec = if wire_data.is_bus{
                    generate_bus_symbols(
                        dag, 
                        state, 
                        &config, 
                        &self.bus_connexions, 
                        buses_info,
                        &self.signal_to_tags,
                        &self.signal_to_tags_with_value,
                        spec_context,
                    )
                } else{
                    generate_symbols(
                        dag, 
                        state, 
                        &config,
                        &self.signal_to_tags,
                        &self.signal_to_tags_with_value,
                        spec_context,
                    )
                };
                specification_preconditions.append(&mut instantiated_spec);
            }
        }
        for wire_data in self.inputs() {
            if !self.public_inputs.contains(&wire_data.name) {
                let state = State { 
                    basic_name: wire_data.name.clone(), 
                    signal_field_names: vec![wire_data.name.clone()],
                    name: wire_data.name.clone(), 
                    dim: 0 
                };
                let config = SignalConfig { signal_type: 0, dimensions: &wire_data.length, is_public: false };
                let mut instantiated_spec = if wire_data.is_bus{
                    generate_bus_symbols(
                        dag, 
                        state, 
                        &config, 
                        &self.bus_connexions, 
                        buses_info,
                        &self.signal_to_tags,
                        &self.signal_to_tags_with_value,
                        spec_context,
                    )
                } else{
                    generate_symbols(
                        dag, 
                        state, 
                        &config,
                        &self.signal_to_tags,
                        &self.signal_to_tags_with_value,
                        spec_context,
                    )
                };
                specification_preconditions.append(&mut instantiated_spec);
            }
        }
        for wire_data in self.intermediates() {
            let state = State { 
                basic_name: wire_data.name.clone(), 
                signal_field_names: vec![wire_data.name.clone()],
                name: wire_data.name.clone(), 
                dim: 0 
            };
            let config = SignalConfig { signal_type: 2, dimensions: &wire_data.length, is_public: false };
            let mut instantiated_spec = if wire_data.is_bus{
                generate_bus_symbols(
                    dag, 
                    state, 
                    &config, 
                    &self.bus_connexions, 
                    buses_info,
                    &self.signal_to_tags,
                    &self.signal_to_tags_with_value,
                    spec_context,
                 )
            } else{
                generate_symbols(
                    dag, 
                    state, 
                    &config,
                    &self.signal_to_tags,
                    &self.signal_to_tags_with_value,
                    spec_context,
                )
            };
            specification_intermediates.append(&mut instantiated_spec);
        }

        self.specification_preconditions = specification_preconditions;
        self.specification_postconditions = specification_postconditions;
        self.specification_intermediates = specification_intermediates;


    }

    fn build_ordered_signals(&self, dag: &mut DAG, buses_info : &Vec<ExecutedBus>) {
        for wire_data in &self.ordered_signals {
            let state = State { 
                basic_name: wire_data.name.clone(), 
                signal_field_names: Vec::new(),// no needed in this case
                name: wire_data.name.clone(), 
                dim: 0 
            };
            let config = OrderedSignalConfig { dimensions: &wire_data.length };
            if wire_data.is_bus{
                generate_ordered_bus_symbols(dag, state, &config, &self.bus_connexions, buses_info );
            } else{
                generate_ordered_symbols(dag, state, &config);
            }
        }
    }

    fn build_connexions(&mut self, dag: &mut DAG) {
        self.connexions.sort_by(|l, r| {
            use std::cmp::Ordering;
            let l_data = &l.inspect;
            let r_data = &r.inspect;
            let cmp_0 = l_data.name.cmp(&r_data.name);
            match cmp_0 {
                Ordering::Equal => l_data.indexed_with.cmp(&r_data.indexed_with),
                v => v,
            }
        });
        let filtered_components = filter_used_components(self);
        self.components = filtered_components.0;
        self.number_of_components = filtered_components.1;
        for cnn in &mut self.connexions {
            cnn.dag_offset = dag.get_entry().unwrap().get_out();
            cnn.dag_component_offset = dag.get_entry().unwrap().get_out_component();
            dag.add_edge(cnn.inspect.goes_to, &cnn.full_name, cnn.inspect.is_parallel);
            cnn.dag_jump = dag.get_entry().unwrap().get_out() - cnn.dag_offset;
            cnn.dag_component_jump = dag.get_entry().unwrap().get_out_component() - cnn.dag_component_offset;
        }
        self.has_parallel_sub_cmp = dag.nodes[dag.main_id()].has_parallel_sub_cmp();
        dag.set_number_of_subcomponents_indexes(self.number_of_components);
    }
    fn build_constraints(&self, dag: &mut DAG) {
        
        for c in &self.constraints {
            let correspondence = dag.get_main().unwrap().correspondence();
            let cc = Constraint::apply_correspondence(c, correspondence);
            dag.add_constraint(cc);
        }
        for s in &self.underscored_signals{
            let correspondence = dag.get_main().unwrap().correspondence();
            let new_s = correspondence.get(s).unwrap().clone();
            dag.add_underscored_signal(new_s);
        }
    }

    fn build_specifications(&self, dag: &mut DAG) {
        for c in &self.specification_preconditions {
            let correspondence = dag.get_main().unwrap().correspondence();
            let cc = c.apply_correspondence(correspondence);
            dag.add_specification_precondition(cc);
        }
        for c in &self.specification_postconditions {
            let correspondence = dag.get_main().unwrap().correspondence();
            let cc = c.apply_correspondence(correspondence);
            dag.add_specification_postcondition(cc);
        }
        for c in &self.specification_intermediates {
            let correspondence = dag.get_main().unwrap().correspondence();
            let cc = c.apply_correspondence(correspondence);
            dag.add_specification_intermediate(cc);
        }
        
    }

    pub fn export_to_circuit(self, instances: &mut [TemplateInstance], buses_info : &Vec<BusInstance>) -> TemplateInstance {
        use SignalType::*;
        fn build_triggers(
            instances: &mut [TemplateInstance],
            connexions: Vec<Connexion>,
        ) -> Vec<Trigger> {
            let mut triggers = vec![];
            for cnn in connexions {
                let data = cnn.inspect;
                instances[data.goes_to].is_parallel_component |= data.is_parallel;
                instances[data.goes_to].is_not_parallel_component |= !(data.is_parallel);
                
                let mut external_wires = Vec::new();
                for wire in &instances[data.goes_to].wires{
                    if wire.xtype() != SignalType::Intermediate{
                        external_wires.push(wire.clone());
                    }
                }

                let trigger = Trigger {
                    offset: cnn.dag_offset,
                    component_offset: cnn.dag_component_offset,
                    component_name: data.name,
                    indexed_with: data.indexed_with,
                    is_parallel: data.is_parallel || instances[data.goes_to].is_parallel,
                    runs: instances[data.goes_to].template_header.clone(),
                    template_id: data.goes_to,
                    external_wires,
                    has_inputs: instances[data.goes_to].number_of_inputs > 0,
                };
                triggers.push(trigger);
            }
            triggers
        }

        fn build_components(components: ComponentCollector) -> Vec<Component> {
            let mut cmp = vec![];
            for c in components {
                cmp.push(Component { 
                    name: c.name, 
                    lengths: c.length, 
                    is_anonymous: c.is_anonymous,
                })
            }
            cmp
        }

        fn build_arguments(parameter_instances: ParameterContext) -> Vec<Argument> {
            let mut arguments = vec![];
            for (name, data) in parameter_instances {
                let (dim, value) = data.destruct();
                let argument = Argument { name, lengths: dim, values: as_big_int(value) };
                arguments.push(argument);
            }
            arguments
        }

        let header = format!("{}_{}", self.template_name, instances.len());
        let clusters = build_clusters(&self, instances);
        let triggers = build_triggers(instances, self.connexions);
        let components = build_components(self.components);
        let arguments = build_arguments(self.parameter_instances);


        let config = TemplateConfig {
            header,
            clusters,
            triggers,
            arguments,
            components,
            id: instances.len(),
            is_parallel: self.is_parallel,
            has_parallel_sub_cmp: self.has_parallel_sub_cmp,
            code: self.code,
            name: self.template_name,
            number_of_components : self.number_of_components,
            signals_to_tags: self.signal_to_tags_with_value,
            is_extern_c: self.is_extern_c
        };


        let mut instance = TemplateInstance::new(config);

        let mut public = vec![];
        let mut not_public = vec![];
        for s in self.inputs {
            if self.public_inputs.contains(&s.name) {
                public.push(s);
            } else {
                not_public.push(s);
            }
        }
        let mut local_id = 0;
        let mut dag_local_id = 1;
        for s in self.outputs {
            if s.is_bus{
                let bus_node = self.bus_connexions.get(&s.name).unwrap().inspect.goes_to;
                let info_bus = buses_info.get(bus_node).unwrap();
                let size = s.length.iter().fold(info_bus.size, |p, c| p * (*c));
                let bus = Bus{
                    name: s.name,
                    lengths: s.length,
                    local_id,
                    dag_local_id,
                    bus_id: bus_node,
                    size,
                    xtype: Output,
                };
                local_id += bus.size;
                dag_local_id += bus.size;
                instance.add_signal(Wire::TBus(bus));
            } else{
                let size = s.length.iter().fold(1, |p, c| p * (*c));
                let signal = Signal { name: s.name, lengths: s.length, local_id, dag_local_id, xtype: Output, size};
                local_id += signal.size;
                dag_local_id += signal.size;
                instance.add_signal(Wire::TSignal(signal));
            }
        }

        for s in public {
            if s.is_bus{
                let bus_node = self.bus_connexions.get(&s.name).unwrap().inspect.goes_to;
                let info_bus = buses_info.get(bus_node).unwrap();
                let size = s.length.iter().fold(info_bus.size, |p, c| p * (*c));
                let bus = Bus{
                    name: s.name,
                    lengths: s.length,
                    local_id,
                    dag_local_id,
                    bus_id: bus_node,
                    size,
                    xtype: Input,
                };
                local_id += bus.size;
                dag_local_id += bus.size;
                instance.add_signal(Wire::TBus(bus));
            } else{
                let size = s.length.iter().fold(1, |p, c| p * (*c));
                let signal = Signal { name: s.name, lengths: s.length, local_id, dag_local_id, xtype: Input, size};
                local_id += signal.size;
                dag_local_id += signal.size;
                instance.add_signal(Wire::TSignal(signal));
            }
        }
        for s in not_public {
            if s.is_bus{
                let bus_node = self.bus_connexions.get(&s.name).unwrap().inspect.goes_to;
                let info_bus = buses_info.get(bus_node).unwrap();
                let size = s.length.iter().fold(info_bus.size, |p, c| p * (*c));
                let bus = Bus{
                    name: s.name,
                    lengths: s.length,
                    local_id,
                    dag_local_id,
                    bus_id: bus_node,
                    size,
                    xtype: Input,
                };
                local_id += bus.size;
                dag_local_id += bus.size;
                instance.add_signal(Wire::TBus(bus));
            } else{
                let size = s.length.iter().fold(1, |p, c| p * (*c));
                let signal = Signal { name: s.name, lengths: s.length, local_id, dag_local_id, xtype: Input, size};
                local_id += signal.size;
                dag_local_id += signal.size;
                instance.add_signal(Wire::TSignal(signal));
            }
        }
        for s in self.intermediates {
            if s.is_bus{
                let bus_node = self.bus_connexions.get(&s.name).unwrap().inspect.goes_to;
                let info_bus = buses_info.get(bus_node).unwrap();
                let size = s.length.iter().fold(info_bus.size, |p, c| p * (*c));
                let bus = Bus{
                    name: s.name,
                    lengths: s.length,
                    local_id,
                    dag_local_id,
                    bus_id: bus_node,
                    size,
                    xtype: Intermediate,
                };
                local_id += bus.size;
                dag_local_id += bus.size;
                instance.add_signal(Wire::TBus(bus));
            } else{
                let size = s.length.iter().fold(1, |p, c| p * (*c));
                let signal = Signal { name: s.name, lengths: s.length, local_id, dag_local_id, xtype: Intermediate, size};
                local_id += signal.size;
                dag_local_id += signal.size;
                instance.add_signal(Wire::TSignal(signal));
            }
        }

        instance
    }
    
}

struct SignalConfig<'a> {
    is_public: bool,
    signal_type: usize,
    dimensions: &'a [usize],
}
struct State {
    basic_name: String, //Only name without array accesses [].
    name: String, //Full name with array accesses.
    signal_field_names: Vec<String>,
    dim: usize,
}
fn generate_symbols(
    dag: &mut DAG, 
    state: State, 
    config: &SignalConfig, 
    signal_to_tags: &HashMap<Vec<String>, Vec<String>>, 
    signal_to_tags_with_value: &HashMap<Vec<String>, BigInt>,
    spec_context: &SpecificationContext,
) -> LinkedList<Expression>{
    if state.dim == config.dimensions.len() {

        // add the specification of the signal to the dag
        let mut instantiated_specifications = LinkedList::new();
        let tags = signal_to_tags.get(&state.signal_field_names);
        match tags{
            Some(list_tags)=>{
                for tag in list_tags{
                    let tag_specification = spec_context.tag_specifications.get(tag);
                    match tag_specification{
                        Some(spec)=>{
                            let condition = spec.get_condition();
                            // the specification of a plain signal cannot take
                            // parameters, so there is nothing to bind here
                            let instantiated = instantiate_expression(
                                condition,
                                &state.name,
                                &state.signal_field_names,
                                signal_to_tags_with_value,
                                &SpecificationArgs::new(),
                                spec_context,
                            );
                            if !is_trivially_true(&instantiated){
                                instantiated_specifications.push_back(instantiated);
                            }
                        },
                        None =>{
                            // no need to add
                        }
                    }
                }
            },
            None =>{
                // no tags associated
            }
        }


        if config.signal_type == 0 {
            dag.add_input(state.name, config.is_public);
        } else if config.signal_type == 1 {
            dag.add_output(state.name);
        } else if config.signal_type == 2 {
            dag.add_intermediate(state.name);
        }
        instantiated_specifications

    } else {
        let mut index = 0;
        let mut instantiated_specifications = LinkedList::new();

        while index < config.dimensions[state.dim] {
            let new_state =
                State { 
                    basic_name: state.basic_name.clone(), 
                    signal_field_names: state.signal_field_names.clone(),
                    name: format!("{}[{}]", state.name, index), 
                    dim: state.dim + 1 
                };
            instantiated_specifications.append(
                &mut generate_symbols(
                    dag, 
                    new_state, 
                    config,
                    signal_to_tags,
                    signal_to_tags_with_value,
                    spec_context,
                )
            );
            index += 1;
        }
        instantiated_specifications
    }
}

// TODO: move to bus?
fn generate_bus_symbols(
    dag: &mut DAG, 
    state: State, 
    config: &SignalConfig, 
    bus_connexions: &HashMap<String, BusConnexion>, 
    buses: &Vec<ExecutedBus>,
    signal_to_tags: &HashMap<Vec<String>, Vec<String>>, 
    signal_to_tags_with_value: &HashMap<Vec<String>, BigInt>,
    spec_context: &SpecificationContext,
) -> LinkedList<Expression>{
    let bus_connection = bus_connexions.get(&state.basic_name).unwrap();
    let ex_bus2 = buses.get(bus_connection.inspect.goes_to).unwrap();

    let mut instantiated_specifications = LinkedList::new();
    
    if state.dim == config.dimensions.len() {
        for info_field in ex_bus2.fields(){
            let signal_name = format!("{}.{}",state.name, info_field.name);
            let mut signal_field_names = state.signal_field_names.clone();
            signal_field_names.push(info_field.name.clone());
            let state = State { 
                basic_name: info_field.name.clone(), 
                signal_field_names,
                name: signal_name, 
                dim: 0 
            };
            let config = SignalConfig { 
                signal_type: config.signal_type, 
                dimensions: &info_field.length, 
                is_public: config.is_public,
            };
            if info_field.is_bus{
                instantiated_specifications.append(
                    &mut generate_bus_symbols(
                        dag, 
                        state, 
                        &config, 
                        ex_bus2.bus_connexions(), 
                        buses,
                        signal_to_tags,
                        signal_to_tags_with_value,
                        spec_context,
                    )
                );
            } else{
                instantiated_specifications.append(
                    &mut generate_symbols(
                        dag, 
                        state, 
                        &config,
                        signal_to_tags,
                        signal_to_tags_with_value,
                        spec_context,
                    )
                );
            }
        }

        // also generate the specifications for the complete bus
        let tags = signal_to_tags.get(&state.signal_field_names);
        match tags{
            Some(list_tags)=>{
                for tag in list_tags{
                    let tag_specification = spec_context.tag_specifications.get(tag);
                    match tag_specification{
                        Some(spec)=>{
                            let condition = spec.get_condition();
                            // the parameters declared by the specification stand,
                            // positionally, for the ones of this instance of the bus
                            let spec_args = bind_specification_args(spec.get_args(), ex_bus2);
                            let instantiated = instantiate_expression(
                                condition,
                                &state.name,
                                &state.signal_field_names,
                                signal_to_tags_with_value,
                                &spec_args,
                                spec_context,
                            );
                            // a specification guarded by the parameters may not
                            // apply to this instance at all
                            if !is_trivially_true(&instantiated){
                                instantiated_specifications.push_back(instantiated);
                            }
                        },
                        None =>{
                            // no need to add
                        }
                    }
                }
            },
            None =>{
                // no tags associated
            }
        }


    } else {
        let mut index = 0;
        while index < config.dimensions[state.dim] {
            let new_state =
                State { 
                    basic_name: state.basic_name.clone(), 
                    name: format!("{}[{}]", state.name, index), 
                    dim: state.dim + 1,
                    signal_field_names: state.signal_field_names.clone()
                };
            instantiated_specifications.append(
                &mut generate_bus_symbols(
                    dag, 
                    new_state, 
                    config, 
                    bus_connexions, 
                    buses,
                    signal_to_tags,
                    signal_to_tags_with_value,
                    spec_context,
                )
            );
            index += 1;
        }
    }
    instantiated_specifications

}



/// Everything needed to turn the specification of a tag into the proof
/// obligations of a concrete instance: the specifications themselves and what is
/// required to resolve the calls to pure functions that appear in them.
pub struct SpecificationContext<'a> {
    pub tag_specifications: &'a TagSpecificationInfo,
    pub program_archive: &'a ProgramArchive,
    pub prime: &'a String,
    pub flags: FlagsExecution,
}

/// Values bound to the parameters declared by a tag specification, taken from
/// the instance of the bus the specification is being applied to.
pub type SpecificationArgs = HashMap<String, BigInt>;

/// True when, once instantiated, the specification says nothing about this
/// instance: its guard on the parameters of the bus already made it hold. Such
/// a specification generates no proof obligation.
fn is_trivially_true(condition: &Expression) -> bool{
    use num_traits::Zero;
    match condition{
        Expression::Number(_, value) => !value.is_zero(),
        _ => false,
    }
}

/// Binds the parameter names declared by a tag specification to the values that
/// the corresponding parameters take in this instance of the bus. The binding is
/// positional: the i-th parameter of the specification stands for the i-th
/// parameter of the bus, whatever the two are called.
fn bind_specification_args(
    spec_args: &Vec<String>,
    executed_bus: &ExecutedBus,
) -> SpecificationArgs{
    use crate::environment_utils::slice_types::AExpressionSlice;
    use circom_algebra::algebra::ArithmeticExpression;

    let mut args = SpecificationArgs::new();
    // the arity was already checked during the symbol analysis; a specification
    // that declares no parameters simply binds nothing
    for (name, bus_param) in spec_args.iter().zip(executed_bus.parameter_names.iter()){
        let slice = match executed_bus.parameter_instances.get(bus_param){
            Some(slice) => slice,
            None => continue,
        };
        let value = AExpressionSlice::get_reference_to_single_value_by_index(slice, 0);
        if let Ok(ArithmeticExpression::Number { value }) = value{
            args.insert(name.clone(), value.clone());
        }
    }
    args
}

/// Evaluates an expression of a tag specification that must be a compile-time
/// constant: the indices of the array accesses, and the guards that decide
/// which part of a specification applies to a given instance of the bus. The
/// only free symbols allowed are the parameters of the specification, which
/// already have a value in `spec_args`; anything mentioning a signal is not
/// constant and yields None.
///
/// Comparisons and boolean operators follow the convention of the language:
/// false is 0 and true is 1.
fn evaluate_constant_expression(
    expression: &Expression,
    spec_args: &SpecificationArgs,
    spec_context: &SpecificationContext,
) -> Option<BigInt>{
    use program_structure::ast::Expression::{Number, Variable, InfixOp, PrefixOp, Call};
    use program_structure::ast::{ExpressionInfixOpcode, ExpressionPrefixOpcode};
    use num_traits::{One, Pow, ToPrimitive, Zero};

    fn boolean(value: bool) -> Option<BigInt>{
        Some(if value { BigInt::one() } else { BigInt::zero() })
    }

    match expression{
        Number(_, value) => Some(value.clone()),
        Variable { name, access, .. } => {
            if access.is_empty(){
                spec_args.get(name).cloned()
            } else{
                None
            }
        }
        PrefixOp { prefix_op, rhe, .. } => {
            let value = evaluate_constant_expression(rhe, spec_args, spec_context)?;
            match prefix_op{
                ExpressionPrefixOpcode::Sub => Some(-value),
                ExpressionPrefixOpcode::BoolNot => boolean(value.is_zero()),
                _ => None,
            }
        }
        InfixOp { lhe, infix_op, rhe, .. } => {
            let l = evaluate_constant_expression(lhe, spec_args, spec_context)?;
            let r = evaluate_constant_expression(rhe, spec_args, spec_context)?;
            match infix_op{
                ExpressionInfixOpcode::Add => Some(l + r),
                ExpressionInfixOpcode::Sub => Some(l - r),
                ExpressionInfixOpcode::Mul => Some(l * r),
                ExpressionInfixOpcode::Div | ExpressionInfixOpcode::IntDiv => {
                    if r.is_zero() { None } else { Some(l / r) }
                }
                ExpressionInfixOpcode::Mod => {
                    if r.is_zero() { None } else { Some(l % r) }
                }
                ExpressionInfixOpcode::Pow => {
                    let exp = r.to_u32()?;
                    Some(Pow::pow(&l, exp))
                }
                ExpressionInfixOpcode::Lesser => boolean(l < r),
                ExpressionInfixOpcode::LesserEq => boolean(l <= r),
                ExpressionInfixOpcode::Greater => boolean(l > r),
                ExpressionInfixOpcode::GreaterEq => boolean(l >= r),
                ExpressionInfixOpcode::Eq => boolean(l == r),
                ExpressionInfixOpcode::NotEq => boolean(l != r),
                ExpressionInfixOpcode::BoolAnd => boolean(!l.is_zero() && !r.is_zero()),
                ExpressionInfixOpcode::BoolOr => boolean(!l.is_zero() || !r.is_zero()),
                _ => None,
            }
        }
        Call { id, args, .. } => {
            // a call to a pure function is resolved here, so that the
            // specification can be written in terms of the constants of the
            // library (maxbits(), for instance) instead of repeating them
            let mut values = Vec::new();
            for arg in args{
                values.push(evaluate_constant_expression(arg, spec_args, spec_context)?);
            }
            crate::execute::execute_constant_function_call(
                id,
                values,
                spec_context.program_archive,
                spec_context.prime,
                spec_context.flags,
            )
        }
        _ => None,
    }
}

fn instantiate_expression(
    expression: &Expression,
    signal_name: &String,
    signal_field_names: &Vec<String>,
    signal_to_tags_values: &HashMap<Vec<String>, BigInt>,
    spec_args: &SpecificationArgs,
    spec_context: &SpecificationContext,
) -> Expression{

    use program_structure::ast::Expression::{Number, Variable, InfixOp, PrefixOp, Call};
    use program_structure::ast::Access;

    match expression{
        Number(_,_) => {
            expression.clone()
        },
        Variable { meta, name, access } => {
            // a bare reference to one of the parameters of the specification is
            // replaced by the value it takes in this instance of the bus
            if access.is_empty(){
                if let Some(value) = spec_args.get(name){
                    return Number(meta.clone(), value.clone());
                }
            }
            // todo -> apply type analysis and get info about if it is tag
            //if meta.get_type_knowledge().is_tag() {
                // in case it is a tag get its value
                let mut complete_signal_name = signal_field_names.clone();
                let mut string_name = signal_name.clone();


                for ac in access{
                    match ac{
                        Access::ComponentAccess(value)=>{
                            complete_signal_name.push(value.clone());
                            string_name = format!("{}.{}", string_name, value);
                        },
                        Access::ArrayAccess(expr)=>{
                            // the index may mention the parameters of the
                            // specification, so it is folded here
                            match evaluate_constant_expression(expr, spec_args, spec_context){
                                Some(value)=>{
                                    string_name = format!("{}[{}]", string_name, value);
                                },
                                None => panic!(
                                    "The index of an array access in the specification of a tag \
                                     is not a compile-time constant. Only numbers and the \
                                     parameters declared by the specification can be used there."
                                ),
                            }

                        }
                    }
                }



                let value = signal_to_tags_values.get(&complete_signal_name);

                match value{
                    // TODO: print pretty error
                    None => //unreachable!("The tag does not have a value"),
                    {
                        // case not tag, dont give value, build the signal name
                        Expression:: Variable{meta: meta.clone(), name: string_name, access: Vec::new()}
                    }
                    Some(value) => {
                        Number(meta.clone(), value.clone())
                    }
                }

            //} else {
                // in other case instantiate
            //    Expression:: Variable{meta: meta.clone(), name: signal_name.clone(), access: access.clone()}
            //}
        }
        InfixOp { meta, lhe, infix_op, rhe, .. } => {
            use program_structure::ast::ExpressionInfixOpcode;
            use program_structure::ast::ExpressionInfixOpcode::{BoolAnd, BoolOr, Mul};
            use num_traits::{One, Zero};

            // Value of one operand that already decides the result of the
            // operation on its own, whatever the other one is.
            let decides = match infix_op{
                BoolAnd | Mul => Option::Some(BigInt::zero()),
                BoolOr => Option::Some(BigInt::one()),
                _ => Option::None,
            };

            // A specification can be guarded by a condition on the parameters,
            // so that it only applies to some instances of the bus, and can zero
            // out the terms of a sum that do not belong to a given instance.
            // When one side already decides the result, the other one is dropped
            // WITHOUT instantiating it: it may well mention signals that do not
            // exist in this instance, which is precisely the point of guarding.
            //
            //   false && X -> false    true || X -> true    0 * X -> 0
            if let Option::Some(decides) = &decides{
                for (side, other) in [(lhe, rhe), (rhe, lhe)]{
                    match evaluate_constant_expression(side, spec_args, spec_context){
                        Some(value) if value == *decides => {
                            return Number(meta.clone(), decides.clone());
                        }
                        Some(_) if *infix_op != Mul => {
                            // constant but not decisive: the result is whatever
                            // the other side says
                            return instantiate_expression(
                                other, signal_name, signal_field_names,
                                signal_to_tags_values, spec_args, spec_context,
                            );
                        }
                        _ => {}
                    }
                }
            }

            let l_value = instantiate_expression(lhe, signal_name, signal_field_names, signal_to_tags_values, spec_args, spec_context);
            let r_value = instantiate_expression(rhe, signal_name, signal_field_names, signal_to_tags_values, spec_args, spec_context);

            // The same absorption once both sides are instantiated: a branch of a
            // guard that collapsed leaves a constant behind, and a truth value is
            // not something the SMT translator can take as a condition.
            if let Option::Some(decides) = &decides{
                for (side, other) in [(&l_value, &r_value), (&r_value, &l_value)]{
                    if let Number(_, value) = side{
                        if value == decides{
                            return Number(meta.clone(), decides.clone());
                        }
                        if *infix_op != Mul{
                            return other.clone();
                        }
                    }
                }
            }

            let rebuilt = Expression::InfixOp {
                meta: meta.clone(),
                lhe: Box::new(l_value),
                infix_op: *infix_op,
                rhe: Box::new(r_value),
            };
            // Connectives and comparisons between constants are folded here too;
            // the arithmetic is left to the translator, which does it with the
            // arithmetic of the field.
            match infix_op{
                BoolAnd | BoolOr
                | ExpressionInfixOpcode::Lesser | ExpressionInfixOpcode::LesserEq
                | ExpressionInfixOpcode::Greater | ExpressionInfixOpcode::GreaterEq
                | ExpressionInfixOpcode::Eq | ExpressionInfixOpcode::NotEq => {
                    match evaluate_constant_expression(&rebuilt, spec_args, spec_context){
                        Some(value) => Number(meta.clone(), value),
                        None => rebuilt,
                    }
                }
                _ => rebuilt,
            }
        }
        PrefixOp {meta,  prefix_op, rhe, .. } => {
            let value = instantiate_expression(rhe, signal_name, signal_field_names, signal_to_tags_values, spec_args, spec_context);
            Expression::PrefixOp { meta: meta.clone(),  prefix_op: *prefix_op, rhe: Box::new(value) }
        }

        Call { id, .. } => {
            // calls are resolved at instantiation time, so they must not depend
            // on any signal
            match evaluate_constant_expression(expression, spec_args, spec_context){
                Some(value) => Number(expression.get_meta().clone(), value),
                None => panic!(
                    "The call to '{}' in the specification of a tag could not be resolved to a \
                     number. Only calls to pure functions whose arguments are numbers or \
                     parameters of the specification are allowed there; a function cannot take \
                     signals as arguments in a specification.", id),
            }
        }

        _ => {unreachable!("The rest of the expressions are not valid."); }
    }
}


struct OrderedSignalConfig<'a> {
    dimensions: &'a [usize],
}
fn generate_ordered_symbols(dag: &mut DAG, state: State, config: &OrderedSignalConfig) {
    if state.dim == config.dimensions.len() {
        dag.add_ordered_signal(state.name);
    } else {
        let mut index = 0;
        while index < config.dimensions[state.dim] {
            let new_state =
                State { 
                    basic_name: state.basic_name.clone(), 
                    name: format!("{}[{}]", state.name, index), 
                    dim: state.dim + 1,
                    signal_field_names: Vec::new(),// no needed in this case
                };
            generate_ordered_symbols(dag, new_state, config);
            index += 1;
        }
    }
}

// TODO: move to bus?
fn generate_ordered_bus_symbols(dag: &mut DAG, state: State, config: &OrderedSignalConfig, bus_connexions: &HashMap<String, BusConnexion>, buses: &Vec<ExecutedBus>) {
    let bus_connection = bus_connexions.get(&state.basic_name).unwrap();
    let ex_bus2 = buses.get(bus_connection.inspect.goes_to).unwrap();
    if state.dim == config.dimensions.len() {
        for info_field in ex_bus2.fields(){
            let signal_name = format!("{}.{}",state.name, info_field.name);
            let state = State { 
                basic_name: info_field.name.clone(), 
                name: signal_name, 
                dim: 0,
                signal_field_names: Vec::new(),// no needed in this case
            };
            let config = OrderedSignalConfig {dimensions: &info_field.length };
            if info_field.is_bus{
                generate_ordered_bus_symbols(dag, state, &config, ex_bus2.bus_connexions(), buses);
            } else{
                generate_ordered_symbols(dag, state, &config);
            }
        }

    } else {
        let mut index = 0;
        while index < config.dimensions[state.dim] {
            let new_state =
                State { 
                    basic_name: state.basic_name.clone(), 
                    name: format!("{}[{}]", state.name, index), 
                    dim: state.dim + 1,
                    signal_field_names: Vec::new(),// no needed in this case
                };
            generate_ordered_bus_symbols(dag, new_state, config, bus_connexions, buses);
            index += 1;
        }
    }
}

fn as_big_int(exprs: Vec<ArithmeticExpression<String>>) -> Vec<BigInt> {
    let mut numbers = Vec::with_capacity(exprs.len());
    for e in exprs {
        if let ArithmeticExpression::Number { value } = e {
            numbers.push(value);
        }
    }
    numbers
}

fn filter_used_components(tmp: &ExecutedTemplate) -> (ComponentCollector, usize) {
    fn compute_number_cmp(lengths: &Vec<usize>) -> usize {
        lengths.iter().fold(1, |p, c| p * (*c))
    }
    let mut used = HashSet::with_capacity(tmp.components.len());
    for cnn in &tmp.connexions {
        used.insert(cnn.inspect.name.clone());
    }
    let mut filtered = Vec::with_capacity(used.len());
    let mut number_of_components = 0;
    for cmp in &tmp.components {
        if used.contains(&cmp.name) {
            let value = ComponentData{
                name: cmp.name.clone(),
                length: cmp.length.clone(),
                is_anonymous: cmp.is_anonymous
            };
            filtered.push(value);
            number_of_components = number_of_components + compute_number_cmp(&cmp.length);
        }
    }
    (filtered, number_of_components)
}

#[derive(Copy, Clone)]
enum POS {
    T,
    K(usize),
    B,
}
impl POS {
    pub fn least_upper_bound(l: POS, r: POS) -> POS {
        use POS::*;
        match (l, r) {
            (K(v0), K(v1)) if v0 == v1 => K(v0),
            (B, p) | (p, B) => p,
            _ => T,
        }
    }
}
fn apply_pos_to_connexions(connexions: &[Connexion]) -> HashMap<String, POS> {
    use POS::*;
    let mut solution = HashMap::with_capacity(connexions.len());
    for cnn in connexions {
        let name = &cnn.inspect.name;
        solution.insert(name.clone(), B);
    }
    for cnn in connexions {
        let data = &cnn.inspect;
        let prev = solution.remove(&data.name).unwrap();
        let new = K(data.goes_to);
        let val = POS::least_upper_bound(prev, new);
        solution.insert(data.name.clone(), val);
    }
    solution
}

fn mixed_components(exec_tmp: &ExecutedTemplate) -> Vec<bool> {
    use POS::*;
    let solution = apply_pos_to_connexions(&exec_tmp.connexions);
    let mut mixed = vec![false; exec_tmp.components.len()];
    for (index, value) in exec_tmp.components.iter().enumerate() {
        let pos_value = solution.get(&value.name).unwrap();
        mixed[index] = mixed[index] || matches!(pos_value, T);
    }
    mixed
}

fn build_clusters(tmp: &ExecutedTemplate, instances: &[TemplateInstance]) -> Vec<TriggerCluster> {
    let components = &tmp.components;
    let connexions = &tmp.connexions;
    let mixed = mixed_components(tmp);
    let mut result = Vec::with_capacity(components.len());

    // Cluster initialization
    let mut cmp_data = HashMap::with_capacity(components.len());
    let mut index = 0;
    while index < connexions.len() {
        let cnn_data = &connexions[index].inspect;
        let offset_jump = connexions[index].dag_jump;
        let component_offset_jump = connexions[index].dag_component_jump;
        let instance_id = connexions[index].inspect.goes_to;
        let sub_cmp_header = instances[instance_id].template_header.clone();
        let start = index;
        let mut end = index;
        let mut defined_positions: Vec<Vec<usize>> = vec![];
        loop {
            if end == connexions.len() {
                break;
            } else if connexions[end].inspect.name != cnn_data.name {
                break;
            } else {
                defined_positions.push(connexions[end].inspect.indexed_with.clone());
                end += 1;
            }
        }
        
        let cluster = TriggerCluster {
            slice: start..end,
            length: end - start,
            defined_positions: defined_positions,
            cmp_name: cnn_data.name.clone(),
            xtype: ClusterType::Uniform { offset_jump, component_offset_jump, instance_id, header: sub_cmp_header },
        };
        cmp_data.insert(cnn_data.name.clone(), cluster);
        index = end;
    }

    // cmp_data and result binding
    let mut index = 0;
    while index < components.len() {
        let cmp_name = &components[index].name;
        let mut cluster = cmp_data.remove(cmp_name).unwrap();
        let start = cluster.slice.start;
        let tmp_id = connexions[start].inspect.goes_to;
        let tmp_name = instances[tmp_id].template_name.clone();
        if mixed[index] {
            cluster.xtype = ClusterType::Mixed { tmp_name };
        }
        result.push(cluster);
        index += 1;
    }
    result
}

pub fn templates_in_mixed_arrays(exec_tmp: &ExecutedTemplate, no_templates: usize) -> Vec<bool> {
    use POS::*;
    let solution = apply_pos_to_connexions(&exec_tmp.connexions);
    let mut mixed = vec![false; no_templates];
    for cnn in &exec_tmp.connexions {
        let data = &cnn.inspect;
        let pos_value = solution.get(&data.name).unwrap();
        mixed[data.goes_to] = mixed[data.goes_to] || matches!(pos_value, T);
    }
    mixed
}
