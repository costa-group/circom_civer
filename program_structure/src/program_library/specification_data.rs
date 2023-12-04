use crate::ast::{Expression, FillMeta};

use super::file_definition::FileID;
use std::collections::HashMap;

pub type SpecificationInfo = HashMap<String, SpecificationData>;

#[derive(Clone)]
pub struct SpecificationData {
    file_id: FileID,
    tag: String,
    signal: String,
    condition: Expression,
}


impl SpecificationData {
    pub fn new(
        file_id: FileID,
        elem_id: &mut usize,
        tag: String,
        signal: String,
        mut condition: Expression,
    ) -> SpecificationData {
        condition.fill(file_id, elem_id);
        SpecificationData { file_id, tag, signal, condition }
    }
    
    pub fn get_file_id(&self) -> FileID {
        self.file_id
    }

    pub fn get_signal(&self) -> &String {
        &self.signal
    }

    pub fn get_tag(&self) -> &String {
        &self.tag
    }

    pub fn get_condition(&self) -> &Expression {
        &self.condition
    }
}
