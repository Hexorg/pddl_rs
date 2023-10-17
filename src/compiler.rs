use std::{collections::{HashMap}, hash::Hash};

use enumset::EnumSet;

pub use crate::parser::ast::*;
use crate::{Error, ErrorKind};
#[derive(Debug, PartialEq)]
enum Instruction {
    /// Predicate number and vector of offsets to predicate_types vector
    ReadPredicate(u16, Vec<u16>),
    /// Predicate number and vector of offsets to predicate_types vector
    SetPredicate(u16, Vec<u16>),
    ReadState(usize),
    SetState(usize),
    ReadFunction(usize),
    WriteFunction(usize),
    And(usize),
    Not,
    Or,
    Add, 
    Sub,
    /// Push immediate
    Push(i64),
    /// Pop immediate
    Pop(i64),

}

/// Flatenned problem ready for solving
/// All instrutions use shared memory offsets 
/// no larger than `self.memory_size`
#[derive(Debug, PartialEq)]
pub struct CompiledProblem {
    memory_size: usize,
    actions: Vec<CompiledAction>,
    init: Vec<Instruction>,
    goal: Vec<Instruction>
}

/// Flattened representation of Actions inside CompiledProblems
/// All instruction offsets point to shared memory
#[derive(Debug, PartialEq)]
struct CompiledAction {
    precondition: Vec<Instruction>,
    effect: Vec<Instruction>,
}

/// Intermediate representation of Actions stored in domain
/// All instructions point to parameter indexes instead
/// of full memory indexes
#[derive(Debug, PartialEq)]
struct IntermediateAction {
    parameter_types: Vec<u16>,
    precondition: Vec<Instruction>,
    effect: Vec<Instruction>,
}

pub fn compile_problem<'src>(domain:&Domain<'src>, problem:&Problem<'src>) -> Result<CompiledProblem, Error<'src>> {
    validate_problem(domain, problem)?;
    map_objects(domain, problem)?;
    Ok(CompiledProblem{memory_size:0, actions:vec![], init:vec![], goal:vec![]})
}

fn validate_problem<'src>(domain:&Domain<'src>, problem:&Problem<'src>) -> Result<(), Error<'src>> {
    use ErrorKind::*;
    if problem.domain.1 != domain.name.1 {
        return Err(Error{ input:None, kind:MissmatchedDomain(domain.name.1), chain: None, range:problem.domain.0.clone() })
    }


    Ok(())

}


fn map_objects<'src>(domain:&Domain<'src>, problem:&Problem<'src>) -> Result<(), Error<'src>> {
    let mut type_map = HashMap::new();
    let mut type_src_pos = HashMap::new();
    for List{items, kind} in &domain.types {
        if let Type::Exact(kind) = kind {
            for item in items{
                type_src_pos.insert(item.1, item.0.clone());
                type_map.insert(item.1, kind);
            }
        } else {
            todo!()
        }

    }
    println!("Type map: {:?}", type_map);
    for List{items, kind} in &problem.objects {

    }
    Ok(())
}

    // /// If a predicate uses one parameter - then it will crate as many actions as there are objects of that parameter type
    // /// but if a predicate uses more than one parameter it will create (n choose k) actions, where n is count of objects that match 
    // /// types, and k is parameter count. This is the same case for one parameter, but (n choose 1) == n
    // fn create_permutated_actions(&mut self, parameter_objects:&[usize], parameter_index: usize, action_index: usize) {
    //     let action = self.actions.get(action_index).unwrap();
    //     // action.parameters.len() is k
    //     if parameter_index == action.parameter_types.len() {
    //         if let CompilerContext::Problem { memory_map, actions } = &mut self.context {
    //             let c_prec = Compiler::substitude(memory_map, parameter_objects, &action.precondition);
    //             let c_eff = Compiler::substitude(memory_map, parameter_objects, &action.effect);
    //             actions.push(CompiledAction { precondition: c_prec, effect: c_eff });
    //         } else {
    //             panic!("Expected to have Problem build context.");
    //         }
    //     } else {
    //         let param_type = *action.parameter_types.get(parameter_index).unwrap();
    //         // this loop iterates n times
    //         let mut parameter_objects = parameter_objects.to_vec();
    //         // Need to allocate new vector to avoid mutable borrow checker complaining.
    //         let action_objects:Vec<usize> = self.objects.iter().enumerate().filter_map(|(pos, kind)| if (*kind) as u16 == param_type { Some(pos) } else { None }).collect();
    //         for object_pos in action_objects {
    //             if parameter_objects.iter().find(|t| **t == object_pos).is_none() {
    //                 if parameter_objects.len() == parameter_index {
    //                     parameter_objects.push(object_pos);
    //                 } else {
    //                     parameter_objects[parameter_index] = object_pos;
    //                 }
    //                 self.create_permutated_actions(&parameter_objects, parameter_index+1, action_index);
    //             }
    //         }
    //     }
    // }



#[cfg(test)]
pub mod tests {
    use std::{fs, collections::HashMap};

    use crate::parser::{parse_domain, parse_problem};

    use super::map_objects;

    #[test]
    fn test_type_map() {
        let filename = "domain.pddl";
        let domain_src = fs::read_to_string(filename).unwrap();
        let domain = match parse_domain(&domain_src) {
            Err(e) => {e.report(filename).eprint((filename, ariadne::Source::from(&domain_src))); panic!() },
            Ok(d) => d,
        };
        let filename = "problem_5_10_7.pddl";
        let problem_src = fs::read_to_string(filename).unwrap();
        let problem = match parse_problem(&problem_src, domain.requirements) {
            Err(e) => {e.report(filename).eprint((filename, ariadne::Source::from(&problem_src))); panic!() },
            Ok(p) => p
        };
        match map_objects(&domain, &problem) {
            Err(e) => {e.report(filename).eprint((filename, ariadne::Source::from(&problem_src))); panic!() },
            Ok(()) => (),
        }
    }


    // #[test]
    // fn test_domain() {
    //     let mut parser = Parser::new("(define (domain barman) (:requirements :strips :typing) 
    //     (:types container hand beverage - object) 
    //     (:predicates (ontable ?c - container) (holding ?h - hand ?c - container) (handempty ?h - hand))
    //     (:action grasp :parameters (?c - container ?h - hand) 
    //         :precondition (and (ontable ?c) (handempty ?h)) 
    //         :effect (and (not (ontable ?c)) (not (handempty ?h)) (holding ?h ?c))
    //     ))", None);
    // }

    // #[test]
    // fn test_problem() {
    //     let mut parser = Parser::new("(define (domain barman) (:requirements :strips :typing) 
    //     (:types container hand beverage - object) 
    //     (:predicates (ontable ?c - container) (holding ?h - hand ?c - container) (handempty ?h - hand))
    //     (:action grasp :parameters (?c - container ?h - hand) 
    //         :precondition (and (ontable ?c) (handempty ?h)) 
    //         :effect (and (not (ontable ?c)) (not (handempty ?h)) (holding ?h ?c))
    //     ))", None);
    //     let domain = parser.next().unwrap().unwrap().unwrap_domain();

    //     let mut parser = Parser::new("(define (problem prob) (:domain barman) 
    //     (:objects container1 - container hand1 hand2 - hand shot1 shot2 - beverage)
    //     (:init (ontable container1)) (:goal (holding hand1 container1)))", None);
    //     let problem = parser.next().unwrap().unwrap().unwrap_problem();
    //     let problem = match compiler.compile_problem(&problem) {
    //         Ok(p) => p,
    //         Err(e) => { println!("{}", e); return; },
    //     };
    // }
}