use crate::{Expression, ExpressionInfixOpcode};
use crate::civer::civer_verification::Bounds;
use circom_algebra::num_bigint::BigInt;
use crate::civer::civer_verification::Signal2Bounds;
use std::cmp::{max, min};
enum PossibleBounds{
    Signal(usize),
    Number(BigInt),
    NoBound,
}

fn get_bounds_expression_int(expr: &Expression) -> PossibleBounds{
    use Expression::*;


        match expr{
            Number(_,v) => {
                PossibleBounds::Number(v.clone())
            }
            Variable {name, ..} => {
                PossibleBounds::Signal(name.parse::<usize>().unwrap())
            } 
            
            _ => { PossibleBounds::NoBound}
        }
}



pub fn get_bounds_expression_bool(expr: &Expression, field: &BigInt) -> Signal2Bounds{
    use Expression::*;

    let mut map = Signal2Bounds::new();

    match expr{
            InfixOp { lhe, infix_op, rhe, .. } => {
                match infix_op{
                    ExpressionInfixOpcode::LesserEq => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, Bounds{
                                    min:v,
                                    max:  field - 1
                                });
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, Bounds{
                                    min: BigInt::from(0),
                                    max:  v
                                });
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::GreaterEq => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, Bounds{
                                    min: BigInt::from(0),
                                    max:  v
                                });
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, Bounds{
                                    min:v,
                                    max:  field - 1
                                });
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::Lesser => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, Bounds{
                                    min:v+1,
                                    max:  field - 1
                                });
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, Bounds{
                                    min: BigInt::from(0),
                                    max:  v-1
                                });
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::Greater => {
                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, Bounds{
                                    min: BigInt::from(0),
                                    max:  v-1
                                });
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, Bounds{
                                    min:v+1,
                                    max:  field - 1
                                });
                            },
                            _ =>{},
                        }
                    },
                    ExpressionInfixOpcode::Eq => {

                        let l_bound = get_bounds_expression_int(&lhe);
                        let r_bound = get_bounds_expression_int(&rhe);
                        match (l_bound, r_bound){
                            (PossibleBounds::Number(v), PossibleBounds::Signal(s)) =>{
                                map.insert(s, Bounds{
                                    min: v.clone(),
                                    max: v
                                });
                            },
                            (PossibleBounds::Signal(s), PossibleBounds::Number(v))=>{
                                map.insert(s, Bounds{
                                    min: v.clone(),
                                    max: v
                                });
                            },
                            _ =>{},
                        }
                    },  
                    ExpressionInfixOpcode::BoolOr => {
                        let bounds_l = get_bounds_expression_bool(lhe, field);
                        let bounds_r = get_bounds_expression_bool(rhe, field);
                        update_bounds_or(&mut map, bounds_l, bounds_r)
                    },  
                    ExpressionInfixOpcode::BoolAnd => {
                        let bounds_l = get_bounds_expression_bool(lhe, field);
                        let bounds_r = get_bounds_expression_bool(rhe, field);
                        update_bounds_and(&mut map, bounds_l, bounds_r)
                    },  
                    _ => {},
                }
        
            },
            _  => {}
    }
    map
    
}

fn update_bounds_or(map: &mut Signal2Bounds, left: Signal2Bounds, right: Signal2Bounds){
    use std::cmp::min;
    for (s, bounds_left) in left{
        match right.get(&s){
            Some(bounds_right) =>{
                map.insert(s, 
                    Bounds{
                        min: min(bounds_left.min, bounds_right.min.clone()),
                        max: max(bounds_left.max, bounds_right.max.clone()),
                    }
                );
            },
            None =>{

            },
        }
    }
}


fn update_bounds_and(map: &mut Signal2Bounds, left: Signal2Bounds, right: Signal2Bounds){
    *map = left.clone();
    for (s, bounds) in right{
        match map.get_mut(&s){
            Some(prev_bounds) =>{
                prev_bounds.max = min(prev_bounds.max.clone(), bounds.max);
                prev_bounds.min = max(prev_bounds.min.clone(), bounds.min);
            },
            None =>{
                map.insert(s, bounds);
            }
        }
    }


}

