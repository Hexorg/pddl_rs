use std::collections::{HashMap};

use enumset::EnumSet;

use crate::parser::{Error, ast::*};

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

/// Structure used to build objects that span multiple AST nodes and
/// require knowing build context
#[derive(Debug, PartialEq)]
enum CompilerContext {
    None,
    Action {
        /// Map of parameter names to position in parameter_types vector
        parameters_map:HashMap<String, usize>
    },
    Problem{
        /// Map of \[predicate, param1, param2, ..., paramN\] vectors to memory offsets that 
        /// that combination of params represents 
        memory_map:HashMap<Vec<u16>, usize>, 
        actions:Vec<CompiledAction>}
}

impl Default for CompilerContext {
    fn default() -> Self {
        Self::None
    }
}

/// Compiles parsed Domain and Problem to efficient representations
/// that can be planned over.
/// 
/// Example:
/// ```rust
///     use std::fs;
///     use pddl_rs::{parser::Parser, compiler::Compiler};
///     let domain = fs::read_to_string("domain.pddl").unwrap();
///     let mut parser = Parser::new(domain.as_str(), Some("domain.pddl"));
///     let domain = parser.next().unwrap().unwrap().unwrap_domain();
///     let compiler = match Compiler::new(domain) {
///         Ok(c) => c, 
///         Err(e) => { println!("{}", e); return },
///     };
///     println!("{:?}", compiler);
/// ```
#[derive(Debug, PartialEq)]
pub struct Compiler {
    context: CompilerContext,
    domain_name: String,
    requirements: EnumSet<Requirements>,
    /// List of all types in the domain
    types: Vec<String>, 
    /// Map of type name to offset of its parent type in the `self.types` vec.
    type_parents: HashMap<String, u16>, 
    /// Each predicate definition just needs to know how many variables it takes
    /// Each variable is defined only by the type this variable takes. 
    /// Filled with 0s if typing is not enabled.
    predicates: Vec<Vec<u16>>, 
    /// Map of predicate name to offset in `self.predicates`
    predicates_map: HashMap<String, usize>,
    /// List of flatenned actions in the domain
    actions: Vec<IntermediateAction>,
    /// Map of action named to the offset in `self.actions`
    action_map: HashMap<String, usize>,
    /// Map of function named to memory offsets during problem planning
    function_map: HashMap<String, usize>,
}


impl<'a> Compiler {
    pub fn new(domain:Domain<'a>) -> Result<Self, Error<'a>> {
        let mut compiler = Self{
            domain_name: domain.name.to_string(),
            requirements: domain.requirements,
            context: CompilerContext::None,
            types:vec!["object".to_string()],
            type_parents:HashMap::from([("object".to_string(), 0 as u16)]),
            predicates:Vec::new(),
            predicates_map:HashMap::new(),
            actions: Vec::new(),
            action_map: HashMap::new(),
            function_map: HashMap::new(),
        };
        compiler.visit_domain_type_map(&domain);
        compiler.visit_domain_predicates(&domain);
        compiler.visit_domain_functions(&domain);
        compiler.visit_domain_actions(&domain);
        Ok(compiler)
    }

    pub fn compile_problem(&mut self, problem:&Problem<'a>) -> Result<CompiledProblem, Error<'a>> {
        assert_eq!(self.domain_name, problem.domain);
        if !problem.requirements.is_empty() {
            assert_eq!(self.requirements, problem.requirements);
        }
        let mut objects: Vec<usize> = Vec::new(); // each object is offset, value is type in `self.types`
        for obj in &problem.objects {
            match obj {
                List::Basic(obj) => objects.extend([0 as usize].repeat(obj.len()).iter()),
                List::Typed(obj, kind) =>{
                    let (kind_id, _) = self.types.iter().enumerate().find(|t| t.1 == kind).unwrap();
                    objects.extend([kind_id as usize].repeat(obj.len()).iter())
                },
            }
        }
        self.context = CompilerContext::Problem { memory_map:HashMap::new(), actions: Vec::new() };
        for action_index in 0..self.actions.len() {
            self.create_permutated_actions(&objects, &[], 0, action_index);
        }
        if let CompilerContext::Problem { memory_map, actions } = std::mem::take(&mut self.context) {
            println!("Memory map: {:?}", memory_map);
            Ok(CompiledProblem { memory_size:memory_map.len(), actions, init: Vec::new(), goal: Vec::new() })
        } else {
            todo!("Create error here.")
        }
    }

    /// Replace Predicate(n, params) instructions with read/writing states at offsets
    /// Used in going from [IntermediateAction] to [CompiledAction]
    fn substitude(memory_map:&mut HashMap<Vec<u16>, usize>, parameter_objects:&[usize], instructions:&[Instruction]) -> Vec<Instruction> {
        // TODO: optimize for cache locality by making instruction sets read from nearby memory regions where possible
        let mut new_instructions = Vec::new();
        for instr in instructions {
            new_instructions.push(match instr {
                Instruction::ReadPredicate(pid, param_offsets) => {
                    let mut  map_vector = vec![*pid];
                    map_vector.extend(param_offsets.iter().map(|t| parameter_objects[*t as usize] as u16));
                    if let Some(offset) = memory_map.get(&map_vector) {
                        Instruction::ReadState(*offset)
                    } else {
                        let offset = memory_map.len();
                        memory_map.insert(map_vector, offset);
                        Instruction::ReadState(offset)

                    }
                },
                Instruction::SetPredicate(pid, param_offsets) => {
                    let mut  map_vector = vec![*pid];
                    map_vector.extend(param_offsets.iter().map(|t| parameter_objects[*t as usize] as u16));
                    if let Some(offset) = memory_map.get(&map_vector) {
                        Instruction::SetState(*offset)
                    } else {
                        let offset = memory_map.len();
                        memory_map.insert(map_vector, offset);
                        Instruction::SetState(offset)

                    }
                },
                Instruction::ReadState(_) => panic!("Unexpected instruction."),
                Instruction::SetState(_) => panic!("Unexpected instruction."),
                Instruction::ReadFunction(i) => Instruction::ReadFunction(*i),
                Instruction::WriteFunction(i) => Instruction::WriteFunction(*i),
                Instruction::And(i) => Instruction::And(*i), 
                Instruction::Not => Instruction::Not,
                Instruction::Or => Instruction::Or,
                Instruction::Add => Instruction::Add,
                Instruction::Sub => Instruction::Sub,
                Instruction::Push(i) => Instruction::Push(*i),
                Instruction::Pop(i) => Instruction::Pop(*i), 
            });
        }
        new_instructions
    }

    /// If a predicate uses one parameter - then it will crate as many actions as there are objects of that parameter type
    /// but if a predicate uses more than one parameter it will create (n choose k) actions, where n is count of objects that match 
    /// types, and k is parameter count. This is the same case for one parameter, but (n choose 1) == n
    fn create_permutated_actions(&mut self, objects:&Vec<usize>, parameter_objects:&[usize], parameter_index: usize, action_index: usize) {
        let action = self.actions.get(action_index).unwrap();
        // action.parameters.len() is k
        if parameter_index == action.parameter_types.len() {
            if let CompilerContext::Problem { memory_map, actions } = &mut self.context {
                let c_prec = Compiler::substitude(memory_map, parameter_objects, &action.precondition);
                let c_eff = Compiler::substitude(memory_map, parameter_objects, &action.effect);
                actions.push(CompiledAction { precondition: c_prec, effect: c_eff });
            } else {
                panic!("Expected to have Problem build context.");
            }
        } else {
            let param_type = *action.parameter_types.get(parameter_index).unwrap();
            // this loop iterates n times
            let mut parameter_objects = parameter_objects.to_vec();
            parameter_objects.push(0);
            for object_pos in objects.iter().enumerate().filter_map(|(pos, kind)| if (*kind) as u16 == param_type { Some(pos) } else { None }) {
                if parameter_objects.iter().find(|t| **t == object_pos).is_none() {
                    parameter_objects[parameter_index] = object_pos;
                    self.create_permutated_actions(objects, &parameter_objects, parameter_index+1, action_index);
                }
            }
        }
    }



    fn visit_domain_type_map(&mut self, domain:&Domain) {
        if domain.requirements.contains(crate::parser::ast::Requirements::Typing) {
            for r#type in &domain.types {
                match r#type {
                    List::Typed(identifiers, kind) => {
                        // TODO: Better search in type mapping
                        //    Currently using O(n) where n is amount of types.
                        let (kind_id, _) = self.types.iter().enumerate().find(|t| t.1 == kind).unwrap();
                        for subtype in identifiers {
                            if !self.type_parents.contains_key(*subtype) {
                                let size = self.types.len() as u16;
                                self.types.push((*subtype).to_owned());
                                self.type_parents.insert((*subtype).to_owned(), kind_id as u16);
                                size
                            } else {
                                panic!("Redeclared subtype")
                            };
                        }
                    },
                    _ => panic!("Unexpected AST in domain.types"),
                    
                }
                
            }
        }
    }

    fn visit_domain_predicates(&mut self, domain:&Domain) {
        for AtomicFSkeleton{name, variables} in &domain.predicates {
            let name = name.to_string();
            let mut out_variables = Vec::new();
            for variable in variables {
                match variable {
                    List::Basic(vars) => out_variables.extend([0].repeat(vars.len()).iter()),
                    List::Typed(vars, kind) => {
                        assert!(domain.requirements.contains(crate::parser::ast::Requirements::Typing));
                        let (kind_id, _) = self.types.iter().enumerate().find(|t| t.1 == kind).unwrap();
                        out_variables.extend([kind_id as u16].repeat(vars.len()).iter())
                    },
                }
            }
            self.predicates_map.insert(name, self.predicates.len());
            self.predicates.push(out_variables);

        }
    }

    fn visit_domain_functions(&mut self, domain:&Domain) {
        for TypedFunction{function, kind} in &domain.functions {
            if domain.requirements.contains(Requirements::ActionCosts) {
                assert_eq!(function.name, "total-cost");
                assert_eq!(function.variables.len(), 0);
                assert_eq!(kind, &FunctionTypeKind::Typed(vec!["number"]));
                self.function_map.insert(function.name.to_string(), 0);
            } else {
                todo!();
            }
        }
    }

    /// Convert predicate AST to [Instruction]
    fn predicate(&mut self, is_read:bool, name:&str, params:&Vec<Term>) -> Instruction {
        let id = *self.predicates_map.get(name).unwrap() as u16;
        let mut vars = Vec::new();
        for param in params {
            match param {
                Term::Name(_) => todo!(),
                Term::Function(_) => todo!(),
                Term::Variable(var) => match &self.context {
                    CompilerContext::None => todo!(),
                    CompilerContext::Problem { .. } => panic!("Unexpected compiler context while building predicates."),
                    CompilerContext::Action { parameters_map } => vars.push(*parameters_map.get(*var).unwrap() as u16),
                },
            }
        }
        if is_read {
            Instruction::ReadPredicate(id, vars)
        } else {
            Instruction::SetPredicate(id, vars)
        }
    }


    fn visit_gd(&mut self, instructions:&mut Vec<Instruction>, gd:&GD) {
        match gd {
            GD::AtomicFormula(name, params) => instructions.push(self.predicate(true, name, params)),
            GD::AtomicEquality(_, _) => todo!(),
            GD::NotAtomicFormula(_, _) => todo!(),
            GD::NotAtomicEquality(_, _) => todo!(),
            GD::And(_) => todo!(),
            GD::Or(_) => todo!(),
            GD::Not(_) => todo!(),
            GD::Imply(_) => todo!(),
            GD::Exists(_, _) => todo!(),
            GD::Forall(_, _) => todo!(),
            GD::LessThan(_, _) => todo!(),
            GD::LessThanOrEqual(_, _) => todo!(),
            GD::Equal(_, _) => todo!(),
            GD::GreatherThanOrEqual(_, _) => todo!(),
            GD::GreaterThan(_, _) => todo!(),
        }
    }

    fn visit_precondition_expr(&mut self, instructions:&mut Vec<Instruction>, expr:&PreconditionExpr) {
        match expr {
            PreconditionExpr::And(v) => { for p in v { self.visit_precondition_expr(instructions, p); } instructions.push(Instruction::And(v.len())); },
            PreconditionExpr::Forall(_, _) => todo!(),
            PreconditionExpr::Preference(_, _) => todo!(),
            PreconditionExpr::GD(gd) => self.visit_gd(instructions, gd),
        }

    }

    fn visit_effect_expr(&mut self, instructions:&mut Vec<Instruction>, expr:&Effect) {
        match expr {
            Effect::And(v) => { for e in v { self.visit_effect_expr(instructions, e); }},
            Effect::Forall(_, _) => todo!(),
            Effect::When(_, _) => todo!(),
            Effect::AtomicFormula(name, params) => instructions.push(self.predicate(false, name, params)),
            Effect::NotAtomicFormula(name, params) => {
                instructions.push(Instruction::Not);
                instructions.push(self.predicate(false, name, params));
            }
            Effect::Assign(_, _) => todo!(),
            Effect::AssignUndefined(_) => todo!(),
            Effect::ScaleUp(_, _) => todo!(),
            Effect::ScaleDown(_, _) => todo!(),
            Effect::Increase(function, fluent) => {
                let function_id = *self.function_map.get(function.name).unwrap();
                let value = self.visit_fluent_expression(fluent);
                instructions.push(Instruction::Push(value));
                instructions.push(Instruction::ReadFunction(function_id));
                instructions.push(Instruction::Add);
                instructions.push(Instruction::WriteFunction(function_id))
            },
            Effect::Decrease(_, _) => todo!(),
        }
    }

    fn visit_fluent_expression(&mut self, fluent:&FluentExpression) -> i64 {
        match fluent {
            FluentExpression::Number(l) => match l {
                crate::parser::tokens::Literal::I(i) => *i,
                crate::parser::tokens::Literal::F(_) => todo!(),
                crate::parser::tokens::Literal::B(_) => todo!(),
                crate::parser::tokens::Literal::S(_) => todo!(),
            },
            FluentExpression::Subtract(_) => todo!(),
            FluentExpression::Divide(_) => todo!(),
            FluentExpression::Add(_) => todo!(),
            FluentExpression::Multiply(_) => todo!(),
            FluentExpression::Function(_) => todo!(),
        }
    }

    fn visit_basic_action(&mut self, action:&BasicAction) {
        self.action_map.insert(action.name.to_string(), self.actions.len());
        let mut parameter_types = Vec::new();
        let mut parameters_map = HashMap::new();
        for param in &action.parameters {
            match param {
                List::Basic(params) => for p in params {
                    parameters_map.insert(p.to_string(), parameter_types.len());
                    parameter_types.push(0);
                }
                List::Typed(params, kind) => {
                    let (kind_id, _) = self.types.iter().enumerate().find(|t| t.1 == kind).unwrap();
                    for p in params {
                        parameters_map.insert(p.to_string(), parameter_types.len());
                        parameter_types.push(kind_id as u16);
                    }
                },
            }
        }
        self.context = CompilerContext::Action{parameters_map};
        let mut precondition = Vec::new();
        if let Some(p) = &action.precondition {
            self.visit_precondition_expr(&mut precondition, p)
        }
        let mut effect = Vec::new();
        if let Some(e) = &action.effect {
            self.visit_effect_expr(&mut effect, e);
        }
        // TODO: Filter unused parameters
        self.context = CompilerContext::None;
        self.actions.push(IntermediateAction { parameter_types, precondition, effect })
    }

    fn visit_domain_actions(&mut self, domain:&Domain) {
        for action in &domain.actions {
            match action {
                Action::Basic(ba) => self.visit_basic_action(ba),
                Action::Durative(_) => todo!(),
                Action::Derived(_, _) => todo!(),
            }
        }
    }

}

#[cfg(test)]
pub mod tests {
    use std::{fs, collections::HashMap};

    use crate::{parser::{Parser, ast::Requirements}, compiler::{CompilerContext, IntermediateAction, Instruction}};

    use super::Compiler;

    #[test]
    fn test_from_file() {
        let domain = fs::read_to_string("domain.pddl").unwrap();
        let problem = fs::read_to_string("problem_5_10_7.pddl").unwrap();
        let mut parser = Parser::new(domain.as_str(), Some("domain.pddl"));
        let domain = parser.next().unwrap().unwrap().unwrap_domain();
        let mut parser = Parser::new(problem.as_str(), Some("problem_5_10_7.pddl"));
        let problem = parser.next().unwrap().unwrap().unwrap_problem();
        let mut compiler = match Compiler::new(domain) {
            Ok(c) => c, 
            Err(e) => { println!("{}", e); return },
        };
        println!("{:?}", compiler);
        let problem = match compiler.compile_problem(&problem) {
            Ok(p) => p,
            Err(e) => { println!("{}", e); return },
        };
        println!("Memory size: {}", problem.memory_size);
        println!("First action: {:?}", problem.actions.get(0).unwrap());
        println!("Total actions: {}", problem.actions.len());
    }

    #[test]
    fn test_domain() {
        let mut parser = Parser::new("(define (domain barman) (:requirements :strips :typing) 
        (:types container hand beverage - object) 
        (:predicates (ontable ?c - container) (holding ?h - hand ?c - container) (handempty ?h - hand))
        (:action grasp :parameters (?c - container ?h - hand) 
            :precondition (and (ontable ?c) (handempty ?h)) 
            :effect (and (not (ontable ?c)) (not (handempty ?h)) (holding ?h ?c))
        ))", None);
        let domain = parser.next().unwrap().unwrap().unwrap_domain();
        let compiler = match Compiler::new(domain) {
            Ok(c) => c,
            Err(e) => { println!("{}", e); return; },
        };
        assert_eq!(Compiler{ context: CompilerContext::None, 
            domain_name: String::from("barman"), 
            requirements: Requirements::Strips | Requirements::Typing, 
            types: vec![String::from("object"), String::from("container"), String::from("hand"), String::from("beverage")], 
            type_parents: HashMap::from_iter(vec![(String::from("object"), 0 as u16), (String::from("container"), 0 as u16), (String::from("hand"), 0 as u16), (String::from("beverage"), 0 as u16)]), 
            predicates: vec![vec![1], vec![2, 1], vec![2]], 
            predicates_map: HashMap::from_iter(vec![(String::from("ontable"), 0), (String::from("holding"), 1), (String::from("handempty"), 2)]), 
            actions: vec![IntermediateAction{ parameter_types: vec![1, 2],
                precondition: vec![Instruction::ReadPredicate(0, vec![0]), Instruction::ReadPredicate(2, vec![1]), Instruction::And(2)], 
                effect: vec![Instruction::Not, Instruction::SetPredicate(0, vec![0]), Instruction::Not, Instruction::SetPredicate(2, vec![1]), Instruction::SetPredicate(1, vec![1, 0])] }], 
            action_map: HashMap::from_iter(vec![(String::from("grasp"), 0)]), 
            function_map: HashMap::new() }, compiler);
    }
}