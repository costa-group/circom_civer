use crate::ast::{Expression, FillMeta};

use super::file_definition::FileID;
use std::collections::HashMap;

pub type TagSpecificationInfo = HashMap<String, TagSpecificationData>;

#[derive(Clone)]
pub struct TagSpecificationData {
    file_id: FileID,
    tag: String,
    signal_type: Option<String>,
    signal: String,
    condition: Expression,
}


impl TagSpecificationData {
    pub fn new(
        file_id: FileID,
        elem_id: &mut usize,
        tag: String,
        signal_type: Option<String>,
        signal: String,
        mut condition: Expression,
    ) -> TagSpecificationData {
        condition.fill(file_id, elem_id);
        TagSpecificationData { file_id, tag, signal_type, signal, condition }
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