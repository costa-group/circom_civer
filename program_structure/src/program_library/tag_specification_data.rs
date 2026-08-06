use crate::ast::{Expression, FillMeta};

use super::file_definition::{FileID, FileLocation};
use std::collections::HashMap;

pub type TagSpecificationInfo = HashMap<String, TagSpecificationData>;

#[derive(Clone)]
pub struct TagSpecificationData {
    file_id: FileID,
    tag: String,
    signal_type: Option<String>,
    // names of the bus parameters the specification is written against, in
    // declaration order; empty when the specification is not parameterized
    args: Vec<String>,
    arg_location: FileLocation,
    signal: String,
    condition: Expression,
}


impl TagSpecificationData {
    pub fn new(
        file_id: FileID,
        elem_id: &mut usize,
        tag: String,
        signal_type: Option<String>,
        args: Vec<String>,
        arg_location: FileLocation,
        signal: String,
        mut condition: Expression,
    ) -> TagSpecificationData {
        condition.fill(file_id, elem_id);
        TagSpecificationData {
            file_id, tag, signal_type, args, arg_location, signal, condition
        }
    }

    pub fn get_args(&self) -> &Vec<String> {
        &self.args
    }

    pub fn get_num_of_args(&self) -> usize {
        self.args.len()
    }

    pub fn get_arg_location(&self) -> FileLocation {
        self.arg_location.clone()
    }

    pub fn get_file_id(&self) -> FileID {
        self.file_id
    }

    pub fn get_signal(&self) -> &String {
        &self.signal
    }

    pub fn get_signal_type(&self) -> &Option<String> {
        &self.signal_type
    }

    pub fn get_tag(&self) -> &String {
        &self.tag
    }

    pub fn get_condition(&self) -> &Expression {
        &self.condition
    }
}