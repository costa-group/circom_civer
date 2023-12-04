use crate::expression_builders::build_anonymous_component;
use std::collections::HashMap;


use super::ast::*;

impl Expression {
    pub fn get_meta(&self) -> &Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | InlineSwitchOp { meta, .. }
            | ParallelOp {meta, .. }
            | Variable { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | AnonymousComp { meta, ..}
            | ArrayInLine { meta, .. } => meta,
            | UniformArray { meta, .. } => meta,
            | Tuple {meta, ..} => meta,
        }
    }
    pub fn get_mut_meta(&mut self) -> &mut Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | InlineSwitchOp { meta, .. }
            | ParallelOp {meta, .. }
            | Variable { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | AnonymousComp {meta, ..}
            | ArrayInLine { meta, .. } => meta,
            | UniformArray { meta, .. } => meta,
            | Tuple {meta, ..} => meta,
        }
    }

    pub fn is_array(&self) -> bool {
        use Expression::*;
        if let ArrayInLine { .. } = self {
            true
        } else if let UniformArray { .. } = self{
            true
        } else {
            false
        }
    }

    pub fn is_infix(&self) -> bool {
        use Expression::*;
        if let InfixOp { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn is_prefix(&self) -> bool {
        use Expression::*;
        if let PrefixOp { .. } = self {
            true
        } else {
            false
        }
    }
    
    pub fn is_tuple(&self) -> bool {
        use Expression::*;
        if let Tuple { .. } = self {
            true
        } else {
            false
        }
    }
    pub fn is_switch(&self) -> bool {
        use Expression::*;
        if let InlineSwitchOp { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn is_parallel(&self) -> bool {
        use Expression::*;
        if let ParallelOp { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn is_variable(&self) -> bool {
        use Expression::*;
        if let Variable { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn is_number(&self) -> bool {
        use Expression::*;
        if let Number(..) = self {
            true
        } else {
            false
        }
    }

    pub fn is_call(&self) -> bool {
        use Expression::*;
        if let Call { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn is_anonymous_comp(&self) -> bool {
        use Expression::*;
        if let AnonymousComp { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn make_anonymous_parallel(self) -> Expression {
        use Expression::*;
        match self {
            AnonymousComp { meta, id, params, signals, names, .. } => {
                build_anonymous_component(meta, id, params, signals, names, true)
            }
            _ => self,
        } 
    } 

    pub fn contains_implication_expression(&self) -> bool {
        match &self {
            Expression::InfixOp { lhe, infix_op, rhe, .. } => 
                return infix_op.eq(&ExpressionInfixOpcode::BoolImplication) || lhe.contains_implication_expression() || rhe.contains_implication_expression(),
            Expression::PrefixOp {  rhe, .. } => return rhe.contains_implication_expression(),
            Expression::InlineSwitchOp { cond, if_true, if_false, .. } => 
                return cond.contains_implication_expression() || if_true.contains_implication_expression() || if_false.contains_implication_expression(),
            Expression::ParallelOp {  rhe, .. } => 
                return rhe.contains_implication_expression(),
            Expression::Variable { access , ..} => {
                for ac in access{
                    match ac {
                        Access::ComponentAccess(_) => {},
                        Access::ArrayAccess( exp ) => if exp.contains_implication_expression() {return true;},
                    }
                }
            },
            Expression::Number(_, _) => return false,
            Expression::Call { args, .. }  | Expression::ArrayInLine { values: args, .. } 
            | Expression::Tuple {  values: args, .. }=> {
                for arg in args{
                    if arg.contains_implication_expression() {  return true;}
                }
            },
            Expression::AnonymousComp { params, signals, .. } => {
                for arg in params{
                    if arg.contains_implication_expression() {  return true;}
                }
                for arg in signals{
                    if arg.contains_implication_expression() {  return true;}
                }
            },
            Expression::UniformArray { value, dimension, .. } => 
                return value.contains_implication_expression() || dimension.contains_implication_expression(),
        }
        false
    }
    
    pub fn contains_anonymous_comp(&self) -> bool {
        use Expression::*;
        match &self {
            InfixOp {  lhe, rhe , ..} |  UniformArray { value : lhe, dimension : rhe, .. } => {
                 lhe.contains_anonymous_comp() || rhe.contains_anonymous_comp()
            },
            PrefixOp {  rhe, .. } => {
                 rhe.contains_anonymous_comp()
            },
            InlineSwitchOp {  cond, if_true, if_false, .. } => {
                 cond.contains_anonymous_comp() || if_true.contains_anonymous_comp() || if_false.contains_anonymous_comp()
            },
            Call { args, .. } | Tuple {values: args, ..} | ArrayInLine {  values : args, .. } => {
                for arg in args{
                    if arg.contains_anonymous_comp() {  return true;}
                }
                false
            },
            AnonymousComp { .. } => { true },
            Variable { access, .. } => {
                for ac in access{
                    match ac {
                        Access::ComponentAccess(_) => {},
                        Access::ArrayAccess( exp ) => if exp.contains_anonymous_comp() {return true;},
                    }
                }
                false
            },
            Number(_, _) => {false }
            ParallelOp { rhe , .. } => { rhe.contains_anonymous_comp() },
         }
    }

    pub fn contains_tuple(&self) -> bool {
        use Expression::*;
        match &self {
            InfixOp {  lhe, rhe , ..} |  UniformArray { value : lhe, dimension : rhe, .. } => {
                 lhe.contains_tuple() || rhe.contains_tuple()
            },
            PrefixOp {  rhe, .. } => {
                 rhe.contains_tuple()
            },
            InlineSwitchOp {  cond, if_true, if_false, .. } => {
                 cond.contains_tuple() || if_true.contains_tuple() || if_false.contains_tuple()
            },
            Call { args, .. } | ArrayInLine {  values : args, .. } => {
                for arg in args{
                    if arg.contains_tuple() {  return true;}
                }
                false
            },
            AnonymousComp { params, signals, .. } => { 
                for ac in params{
                    if ac.contains_tuple() {return true;}
                }
                for ac in signals{
                    if ac.contains_tuple() {return true;}
                }
                false
             },
            Variable { access, .. } => {
                for ac in access{
                    match ac {
                        Access::ComponentAccess(_) => {},
                        Access::ArrayAccess( exp ) => if exp.contains_tuple() {return true;},
                    }
                }
                false
            },
            Number(_, _) => {false },
            Tuple { .. } => {true},
            ParallelOp { rhe, .. } => {rhe.contains_tuple()},
         }
    }

  

    pub fn apply_correspondence(&self, correspondence: &HashMap<String, usize>) -> Expression{
        use Expression::*;
        match self{
            Number(_,_) => {
                self.clone()
            }
            Variable { meta, name, access } => {
                match correspondence.get(name){
                    Some(pos) => Expression:: Variable{meta: meta.clone(), name: format!("{}", pos), access: access.clone()},
                    None => unreachable!(),
    
                }
            }
            InfixOp { meta, lhe, infix_op, rhe, .. } => {
                let l_value = lhe.apply_correspondence(correspondence);
                let r_value = rhe.apply_correspondence(correspondence);
                Expression::InfixOp { meta: meta.clone(), lhe: Box::new(l_value), infix_op: *infix_op, rhe: Box::new(r_value) }
        
            }
            PrefixOp {meta,  prefix_op, rhe, .. } => {
                let value = rhe.apply_correspondence(correspondence);
                Expression::PrefixOp { meta: meta.clone(),  prefix_op: *prefix_op, rhe: Box::new(value) }
        
            }
            
            _ => {unreachable!("The rest of the expressions are not valid."); }
        }
    }

    pub fn check_condition_io_signals(&self, max_io_value: usize) -> bool{
        use Expression::*;
        match self{
            Number(_,_) => {
                true
            }
            Variable { name, ..  } => {
                let value_pos = name.parse::<usize>();
                match value_pos{
                    Ok(v) => v <= max_io_value,
                    Err(_) => unreachable!("Should be a usize, not a string"),
                }   
            }
            InfixOp { lhe, rhe, .. } => {
                lhe.check_condition_io_signals(max_io_value) && rhe.check_condition_io_signals(max_io_value)


            }
            PrefixOp {rhe, .. } => {
                rhe.check_condition_io_signals(max_io_value)

            }

            _ => {unreachable!("The rest of the expressions are not valid."); }
        }
    }



    pub fn apply_offset(&self, offset: usize) -> Expression{
        use Expression::*;
        match self{
            Number(_,_) => {
                self.clone()
            }
            Variable { meta, name, access } => {
                let value_pos = name.parse::<usize>();
                match value_pos{
                    Ok(v) => Expression:: Variable{meta: meta.clone(), name: format!("{}", v + offset), access: access.clone()},
                    Err(_) => unreachable!("Should be a usize, not a string"),
                }    
                
            }
            InfixOp { meta, lhe, infix_op, rhe, .. } => {
                let l_value = lhe.apply_offset(offset);
                let r_value = rhe.apply_offset(offset);
                Expression::InfixOp { meta: meta.clone(), lhe: Box::new(l_value), infix_op: *infix_op, rhe: Box::new(r_value) }
        
            }
            PrefixOp {meta,  prefix_op, rhe, .. } => {
                let value = rhe.apply_offset(offset);
                Expression::PrefixOp { meta: meta.clone(),  prefix_op: *prefix_op, rhe: Box::new(value) }
        
            }
            
            _ => {unreachable!("The rest of the expressions are not valid."); }
        }
    }


}

impl FillMeta for Expression {
    fn fill(&mut self, file_id: usize, element_id: &mut usize) {
        use Expression::*;
        self.get_mut_meta().elem_id = *element_id;
        *element_id += 1;
        match self {
            Number(meta, _) => fill_number(meta, file_id, element_id),
            Variable { meta, access, .. } => fill_variable(meta, access, file_id, element_id),
            InfixOp { meta, lhe, rhe, .. } => fill_infix(meta, lhe, rhe, file_id, element_id),
            PrefixOp { meta, rhe, .. } => fill_prefix(meta, rhe, file_id, element_id),
            ParallelOp{ meta, rhe, ..} => fill_parallel(meta, rhe, file_id, element_id),
            InlineSwitchOp { meta, cond, if_false, if_true, .. } => {
                fill_inline_switch_op(meta, cond, if_true, if_false, file_id, element_id)
            }
            Call { meta, args, .. } => fill_call(meta, args, file_id, element_id),
            ArrayInLine { meta, values, .. } => {
                fill_array_inline(meta, values, file_id, element_id)
            }
            UniformArray { meta, value, dimension, .. } => {
                fill_uniform_array(meta, value, dimension, file_id, element_id)
            }
            AnonymousComp { meta,  params, signals, .. } => {
                    fill_anonymous_comp(meta, params, signals, file_id, element_id)
            },
            Tuple { meta, values} => {fill_tuple(meta,values,file_id,element_id)}
        }
    }
}

fn fill_number(meta: &mut Meta, file_id: usize, _element_id: &mut usize) {
    meta.set_file_id(file_id);
}

fn fill_variable(meta: &mut Meta, access: &mut [Access], file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    for acc in access {
        if let Access::ArrayAccess(e) = acc {
            e.fill(file_id, element_id)
        }
    }
}

fn fill_infix(
    meta: &mut Meta,
    lhe: &mut Expression,
    rhe: &mut Expression,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    lhe.fill(file_id, element_id);
    rhe.fill(file_id, element_id);
}

fn fill_prefix(meta: &mut Meta, rhe: &mut Expression, file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    rhe.fill(file_id, element_id);
}

fn fill_parallel(meta: &mut Meta, rhe: &mut Expression, file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    rhe.fill(file_id, element_id);
}

fn fill_inline_switch_op(
    meta: &mut Meta,
    cond: &mut Expression,
    if_true: &mut Expression,
    if_false: &mut Expression,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    cond.fill(file_id, element_id);
    if_true.fill(file_id, element_id);
    if_false.fill(file_id, element_id);
}

fn fill_call(meta: &mut Meta, args: &mut [Expression], file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    for a in args {
        a.fill(file_id, element_id);
    }
}

fn fill_anonymous_comp(meta: &mut Meta, params: &mut [Expression],signals: &mut [Expression], file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    for a in params {
        a.fill(file_id, element_id);
    }
    for a in signals {
        a.fill(file_id, element_id);
    }
}
fn fill_array_inline(
    meta: &mut Meta,
    values: &mut [Expression],
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    for v in values {
        v.fill(file_id, element_id);
    }
}

fn fill_tuple(
    meta: &mut Meta,
    values: &mut [Expression],
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    for v in values {
        v.fill(file_id, element_id);
    }
}

fn fill_uniform_array(
    meta: &mut Meta,
    value: &mut Expression,
    dimensions: &mut Expression,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    value.fill(file_id, element_id);
    dimensions.fill(file_id, element_id);
}
