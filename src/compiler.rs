use std::{collections::{HashMap, HashSet}, env::Vars, hash::Hash};

use crate::parser::{Error, ast::*};

#[derive(Debug)]
enum Instruction {
    ReadPredicate(u16, Vec<u16>),
    SetPredicate(u16, Vec<u16>),
    ReadFunction(usize),
    WriteFunction(usize),
    And,
    Not,
    Or,
    Add, 
    Sub,
    Push(i64),
    Pop(i64),

}

#[derive(Debug)]
struct CompiledAction {
    parameters: Vec<u16>,
    precondition: Vec<Instruction>,
    effect: Vec<Instruction>,
}

#[derive(Debug)]
enum CompilerContext {
    None,
    Action{parameters_map:HashMap<String, usize>},
}

/// Compiles parsed Domain and Problem to efficient representations
/// that can be planned over.
/// 
/// Example:
/// ```rust
///     let domain = fs::read_to_string("domain.pddl").unwrap();
///     let problem = fs::read_to_string("problem_5_10_7.pddl").unwrap();
///     let mut parser = Parser::new(domain.as_str(), Some("domain.pddl"));
///     let domain = parser.next().unwrap().unwrap().unwrap_domain();
///     let mut parser = Parser::new(problem.as_str(), Some("problem_5_10_7.pddl"));
///     let problem = parser.next().unwrap().unwrap().unwrap_problem();
///     let compiler = match Compiler::new(domain, problem) {
///         Ok(c) => c, 
///         Err(e) => { println!("{}", e); return },
///     };
///     println!("{:?}", compiler);
/// ```
#[derive(Debug)]
pub struct Compiler {
    context: CompilerContext,
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
    actions: Vec<CompiledAction>,
    /// Map of action named to the offset in `self.actions`
    action_map: HashMap<String, usize>,
    /// Map of function named to memory offsets during problem planning
    function_map: HashMap<String, usize>

}

impl<'a> Compiler {
    pub fn new(domain:Domain<'a>, problem:Problem<'a>) -> Result<Self, Error<'a>> {
        let mut compiler = Self{
            context: CompilerContext::None,
            types:vec!["object".to_string()],
            type_parents:HashMap::from([("object".to_string(), 0 as u16)]),
            predicates:Vec::new(),
            predicates_map:HashMap::new(),
            actions: Vec::new(),
            action_map: HashMap::new(),
            function_map: HashMap::new(),
        };
        compiler.build_type_map(&domain);
        compiler.build_predicates(&domain);
        compiler.build_functions(&domain);
        compiler.build_actions(&domain);
        
        Ok(compiler)
    }

    fn build_type_map(&mut self, domain:&Domain) {
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

    fn build_predicates(&mut self, domain:&Domain) {
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

    fn build_functions(&mut self, domain:&Domain) {
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

    fn predicate(&mut self, is_read:bool, name:&str, params:&Vec<Term>) -> Instruction {
        let id = *self.predicates_map.get(name).unwrap() as u16;
        let mut vars = Vec::new();
        for param in params {
            match param {
                Term::Name(_) => todo!(),
                Term::Function(_) => todo!(),
                Term::Variable(var) => match &self.context {
                    CompilerContext::None => todo!(),
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
            PreconditionExpr::And(v) => for p in v { self.visit_precondition_expr(instructions, p)},
            PreconditionExpr::Forall(_, _) => todo!(),
            PreconditionExpr::Preference(_, _) => todo!(),
            PreconditionExpr::GD(gd) => self.visit_gd(instructions, gd),
        }

    }

    fn visit_effect_expr(&mut self, instructions:&mut Vec<Instruction>, expr:&Effect) {
        match expr {
            Effect::And(v) => for e in v { self.visit_effect_expr(instructions, e)},
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
                let value = self.fluent_expression(fluent);
                instructions.push(Instruction::Push(value));
                instructions.push(Instruction::ReadFunction(function_id));
                instructions.push(Instruction::Add);
                instructions.push(Instruction::WriteFunction(function_id))
            },
            Effect::Decrease(_, _) => todo!(),
        }
    }

    fn fluent_expression(&mut self, fluent:&FluentExpression) -> i64 {
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

    fn add_basic_action(&mut self, action:&BasicAction) {
        self.action_map.insert(action.name.to_string(), self.actions.len());
        let mut parameters = Vec::new();
        let mut parameters_map = HashMap::new();
        for param in &action.parameters {
            match param {
                List::Basic(params) => for p in params {
                    parameters_map.insert(p.to_string(), parameters.len());
                    parameters.push(0);
                }
                List::Typed(params, kind) => {
                    let (kind_id, _) = self.types.iter().enumerate().find(|t| t.1 == kind).unwrap();
                    for p in params {
                        parameters_map.insert(p.to_string(), parameters.len());
                        parameters.push(kind_id as u16);
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
        self.context = CompilerContext::None;
        self.actions.push(CompiledAction { parameters, precondition, effect })
    }

    fn build_actions(&mut self, domain:&Domain) {
        for action in &domain.actions {
            match action {
                Action::Basic(ba) => self.add_basic_action(ba),
                Action::Durative(_) => todo!(),
                Action::Derived(_, _) => todo!(),
            }
        }
    }

}

#[cfg(test)]
pub mod tests {
    use std::fs;

    use crate::parser::Parser;

    use super::Compiler;

    #[test]
    fn test_basic() {
        let domain = fs::read_to_string("domain.pddl").unwrap();
        let problem = fs::read_to_string("problem_5_10_7.pddl").unwrap();
        let mut parser = Parser::new(domain.as_str(), Some("domain.pddl"));
        let domain = parser.next().unwrap().unwrap().unwrap_domain();
        let mut parser = Parser::new(problem.as_str(), Some("problem_5_10_7.pddl"));
        let problem = parser.next().unwrap().unwrap().unwrap_problem();
        let compiler = match Compiler::new(domain, problem) {
            Ok(c) => c, 
            Err(e) => { println!("{}", e); return },
        };
        println!("{:?}", compiler);
    }
}