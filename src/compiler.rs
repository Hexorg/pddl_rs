
use std::{collections::HashMap, ops::Range, slice::Iter};

use enumset::EnumSet;

pub use crate::parser::ast::*;
use crate::{Error, ErrorKind};
#[derive(Debug, PartialEq)]
pub enum Instruction {
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

pub trait Runnable {
    fn run(&self, state: &mut[bool]) -> bool;
}

impl Runnable for Vec<Instruction> {
    fn run(&self, state: &mut[bool]) -> bool {
        let mut stack = Vec::with_capacity(512);
        for instruction in self {
            match instruction {
                Instruction::ReadState(addr) => stack.push(state[*addr]),
                Instruction::SetState(addr) => state[*addr] = stack.pop().unwrap(),
                Instruction::ReadFunction(_) => todo!(),
                Instruction::WriteFunction(_) => todo!(),
                Instruction::And(count) => {
                    let mut result = true;
                    let mut count = *count;
                    while count > 0 {
                        result &= stack.pop().unwrap();
                        count -= 1;
                    }
                    stack.push(result);
                }
                Instruction::Not => {let s = !stack.pop().unwrap(); stack.push(s); }
                Instruction::Or => todo!(),
                Instruction::Add => todo!(),
                Instruction::Sub => todo!(),
                Instruction::Push(_) => todo!(),
                Instruction::Pop(_) => todo!(),
            }
        }
        stack.pop().unwrap_or_default()
    }
}

/// Flatenned problem ready for solving
/// All instrutions use shared memory offsets 
/// no larger than `self.memory_size`
#[derive(Debug, PartialEq)]
pub struct CompiledProblem<'src> {
    pub memory_size: usize,
    pub actions: Vec<CompiledAction<'src>>,
    pub init: Vec<Instruction>,
    pub goal: Vec<Instruction>
}

/// Flattened representation of Actions inside CompiledProblems
/// All instruction offsets point to shared memory
#[derive(Debug, PartialEq)]
pub struct CompiledAction<'src> {
    pub name: Name<'src>,
    pub precondition: Vec<Instruction>,
    pub effect: Vec<Instruction>,
}

#[derive(Debug)]
struct CompilerData<'src> {
    requirements: EnumSet<Requirement>,
    /// Type inheritance tree. Everything should end up being an object.
    type_tree: HashMap<&'src str, Name<'src>>,
    /// Source code position mapping of where types are declared.
    type_src_pos: HashMap<&'src str, Range<usize>>,
    /// Problem object map to Domain type.
    object_to_type_map: HashMap<&'src str, Name<'src>>,
    /// Domain type map to vector of objects. Note: `"object"` type must list all 
    /// problem objects.
    type_to_objects_map: HashMap<&'src str, Vec<Name<'src>>>,
    /// Source code position mapping of where problem objects are declared. 
    object_src_pos: HashMap<&'src str, Range<usize>>,
    /// Mapping a vector of `[predicate, arg1, arg2, .., argN]` to a memory bit offset.
    pub predicate_memory_map: HashMap<Vec<&'src str>, usize>,
}

pub fn compile_problem<'src>(domain:&Domain<'src>, problem:&Problem<'src>) -> Result<CompiledProblem<'src>, Error<'src>> {
    validate_problem(domain, problem)?;
    let compiler = map_objects(domain, problem)?;
    let actions = create_concrete_actions(&compiler, domain)?;
    let init = compile_init(&compiler, &problem.init)?;
    let mut goal = Vec::with_capacity(32);

    compile_precondition(&compiler, &problem.goal, None, &mut goal)?;
    Ok(CompiledProblem{memory_size:compiler.predicate_memory_map.len(), actions, init, goal})
}

fn validate_problem<'src>(domain:&Domain<'src>, problem:&Problem<'src>) -> Result<(), Error<'src>> {
    use ErrorKind::*;
    if problem.domain.1 != domain.name.1 {
        return Err(Error{ input:None, kind:MissmatchedDomain(domain.name.1), chain: None, range:problem.domain.0.clone() })
    }


    Ok(())
}

/// Given a list of types, use a type to object map and generate all possible
/// permutations of the objects fitting the list. 
/// 
/// # Arguments
/// * `type_to_objects` - a map of type names to vector of all world objects of that type.
/// * `list` - the argument list that needs to be populated with world objects.
/// * `f` - closure that gets all permutations of objects populated the `list` in a form of a slice
///     mapping `list`'s items to world object names - `&[(ListItemName, ObjectName)]`
fn for_all_type_object_permutations<'src, F, O>(type_to_objects:&HashMap<&'src str, Vec<Name<'src>>>, list:&[List<'src>], mut f:F) -> Result<Vec<O>, Error<'src>>
where F: FnMut(&[(&Name<'src>, &Name<'src>)]) -> Result<O, Error<'src>> {
    use ErrorKind::UndefinedType;
    /// Call the next iterator at the right position. 
    /// If you think about converting binary to decimal:
    /// Position == 0 is the least significant iterator
    /// Position == iterators.len()-1 is the most significant iterator.
    /// Except binary bit can only be 1 or 0, and our iterator bits
    /// can go for however many objects of that type there are.
    /// # Arguments:
    /// * `type_to_objects` - map of type names to vector of world objects of that type
    /// * `iterators` - iterators over object vectors in `type_to_objects` map.
    /// * `args` - "output" vector that's populated by world object permutations each 
    /// time this function is called.
    fn _args_iter<'parent, 'src>(type_to_objects:&'parent HashMap<&'src str, Vec<Name<'src>>>, iterators:&mut [(&Name<'src>, Iter<'parent, Name<'src>>)], args: &mut [(&'parent Name<'src>, &'parent Name<'src>)], pos:usize) -> bool {
        if let Some(kind) = iterators[pos].1.next() {
            args[pos].1 = kind;
            true
        } else if pos + 1 < iterators.len() {
            let kind = iterators[pos].0.1;
            if let Some(vec) = type_to_objects.get(kind) {
                iterators[pos].1 = vec.iter();
            }
            _args_iter(type_to_objects, iterators, args, pos+1)
        } else {
            // We're done permutating
            false
        }
    }

    let mut iterators = Vec::new();
    let mut args = Vec::new();
    // We need to create `objects_vec.len()`` many args - one per object of this type.
    // First, create an iterator per argument type
    for List{items, kind} in list {
        if let Type::Exact(kind) = kind {
            if let Some(objects_vec) = type_to_objects.get(kind.1) {
                for item in items {
                    iterators.push((kind, objects_vec.iter()));
                    if let Some(next) = iterators.last_mut().unwrap().1.next() {
                        args.push((item, next));
                    } else {
                        // Not enough objects to populate this list
                        todo!()
                    }
                }
            } else {
                return Err(Error{input:None, kind:UndefinedType, chain:None, range:kind.0.clone()})
            }
        } else {
            todo!()
        }
    }
    // println!("{:#?}", iterators);
    // Itereate until the most significant iterator is done, calling closure over populated args
    let mut result = vec![f(args.as_slice())?];
    while _args_iter(type_to_objects, iterators.as_mut_slice(), args.as_mut_slice(), 0) {
        result.push(f(args.as_slice())?);
    }
    Ok(result)
}

fn compile_init<'src>(compiler:&CompilerData<'src>, init:&[Init<'src>]) -> Result<Vec<Instruction>, Error<'src>> {
    let mut instructions = Vec::with_capacity(32);
    for exp in init {
        match exp {
            Init::AtomicFormula(formula) => compile_name_negative_formula(compiler, formula, &mut instructions)?,
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(instructions)
}

fn compile_term_atomic_formula<'src>(compiler:&CompilerData<'src>, af:&AtomicFormula<'src, Term<'src>>, args:Option<&[(&Name<'src>, &Name<'src>)]>, instructions: &mut Vec<Instruction>) -> Result<(), Error<'src>> {
    use Term::*;
    use ErrorKind::{ExpectedVariable, ExpectedName, UndeclaredVariable};
    match af {
        AtomicFormula::Predicate(name, params) =>  {
            let mut call_vec = Vec::with_capacity(params.len()+1);
            call_vec.push(name.1);
            for param in params {
                match param {
                    Variable(var) => {
                        if args.is_none() {
                            return Err(Error{input:None, kind:ExpectedName, chain:None, range:param.range()});
                        }
                        let args = args.unwrap();
                        let mut is_found = false;
                        for arg in args {
                            if var.1 == arg.0.1 {
                                call_vec.push(arg.1.1);
                                is_found = true;
                                break;
                            }
                        }
                        if !is_found {
                            return Err(Error{input:None, kind:UndeclaredVariable, chain:None, range:var.0.clone()})
                        }
                    },
                    Name(name) => {
                        if args.is_some() {
                            return Err(Error{input:None, kind:ExpectedVariable, chain:None, range:param.range()});
                        }
                        call_vec.push(name.1);
                    },
                    Function(func) => todo!()
                }
            }
            if let Some(offset) = compiler.predicate_memory_map.get(&call_vec) {
                instructions.push(Instruction::ReadState(*offset))
            } else {
                panic!("All variables matched, and predicate exists, but can't find this call vec memory offset")
            }
            Ok(())
        }
        AtomicFormula::Equality(_, _) => todo!(),
    }
}

fn compile_name_atomic_formula<'src>(compiler:&CompilerData<'src>, af:&AtomicFormula<'src, Name<'src>>, instructions: &mut Vec<Instruction>) -> Result<(), Error<'src>> {
    match af {
        AtomicFormula::Predicate(name, args) => {
            let mut call_vec = vec![name.1];
            call_vec.extend(args.iter().map(|a| a.1));
            if let Some(offset) = compiler.predicate_memory_map.get(&call_vec) {
                instructions.push(Instruction::ReadState(*offset));
                Ok(())
            } else {
                // Check if predicate is defined, check of object is defined.
                todo!()
            } 
        }
        AtomicFormula::Equality(_, _) => todo!(),
    }
    
}

fn compile_gd<'src>(compiler:&CompilerData<'src>, gd:&GD<'src>, args:Option<&[(&Name<'src>, &Name<'src>)]>, instructions: &mut Vec<Instruction>) -> Result<(), Error<'src>> {
    match gd {
        GD::AtomicFormula(af) => compile_term_atomic_formula(compiler, af, args, instructions),
        GD::And(vec) => {for gd in vec { compile_gd(compiler, gd, args, instructions)?} Ok(())},
        GD::Or(_) => todo!(),
        GD::Not(_) => todo!(),
        GD::Imply(_) => todo!(),
        GD::Exists(_) => todo!(),
        GD::Forall(_) => todo!(),
        GD::LessThan(_, _) => todo!(),
        GD::LessThanOrEqual(_, _) => todo!(),
        GD::Equal(_, _) => todo!(),
        GD::GreatherThanOrEqual(_, _) => todo!(),
        GD::GreaterThan(_, _) => todo!(),
    }
}

fn compile_precondition<'src>(compiler:&CompilerData<'src>, precondition:&PreconditionExpr<'src>, args:Option<&[(&Name<'src>, &Name<'src>)]>, instructions: &mut Vec<Instruction>) -> Result<(), Error<'src>> {
    match precondition {
        PreconditionExpr::And(vec) => { 
            for preconditions in vec { 
                compile_precondition(compiler, preconditions, args, instructions)? 
            } 
            instructions.push(Instruction::And(vec.len()));
            Ok(())}
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => compile_gd(compiler, gd, args, instructions),
    }
}

fn compile_term_negative_formula<'src>(compiler:&CompilerData<'src>, formula:&NegativeFormula<'src, Term<'src>>, args:Option<&[(&Name<'src>, &Name<'src>)]>, instructions:&mut Vec<Instruction>) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => compile_term_atomic_formula(compiler, af, args, instructions),
        NegativeFormula::Not(af) => {instructions.push(Instruction::Not); compile_term_atomic_formula(compiler, af, args, instructions)},
    }
}

fn compile_name_negative_formula<'src>(compiler:&CompilerData<'src>, formula:&NegativeFormula<'src, Name<'src>>, instructions:&mut Vec<Instruction>) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => compile_name_atomic_formula(compiler, af, instructions),
        NegativeFormula::Not(af) => {instructions.push(Instruction::Not); compile_name_atomic_formula(compiler, af, instructions)},
    }
}

fn compile_fexp<'src>(compiler:&CompilerData<'src>, fexp:&FluentExpression<'src>, instructions: &mut Vec<Instruction>) -> Result<(), Error<'src>> {
    match fexp {
        FluentExpression::Number(n) => instructions.push(Instruction::Push(*n)),
        FluentExpression::Subtract(_) => todo!(),
        FluentExpression::Negate(_) => todo!(),
        FluentExpression::Divide(_) => todo!(),
        FluentExpression::Add(_) => todo!(),
        FluentExpression::Multiply(_) => todo!(),
        FluentExpression::Function(_) => todo!(),
    }
    Ok(())
}

enum SupportedFunctionOp {
    INC,
    DEC
}
fn function_op<'src>(compiler:&CompilerData<'src>, function:&FunctionTerm<'src>, fexp:&FluentExpression<'src>, op:SupportedFunctionOp, instructions: &mut Vec<Instruction>) -> Result<(), Error<'src>> {
    compile_fexp(compiler, fexp, instructions)?;
    if function.terms.len() == 0 && function.name.1 == "total-cost" && compiler.requirements.contains(Requirement::ActionCosts) {
        use SupportedFunctionOp::*;
        match op {
            INC => instructions.push(Instruction::Add),
            DEC => instructions.push(Instruction::Sub),
        }
        instructions.push(Instruction::SetState(9999));
        Ok(())
    } else {
        Err(Error{input:None, kind:ErrorKind::UnsetRequirement(Requirement::ActionCosts.into()), chain:None, range:function.range()})
    }
}

fn compile_effect<'src>(compiler:&CompilerData<'src>, effect:&Effect<'src>, args:Option<&[(&Name<'src>, &Name<'src>)]>, instructions:&mut Vec<Instruction>) -> Result<(), Error<'src>> {
    match effect {
        Effect::And(vec) => {for effect in vec { compile_effect(compiler, effect, args, instructions)?} Ok(())},
        Effect::Forall(_) => todo!(),
        Effect::When(_) => todo!(),
        Effect::NegativeFormula(f) => compile_term_negative_formula(compiler, f, args, instructions),
        Effect::Assign(_, _) => todo!(),
        Effect::AssignTerm(_, _) => todo!(),
        Effect::AssignUndefined(_) => todo!(),
        Effect::ScaleUp(_, _) => todo!(),
        Effect::ScaleDown(_, _) => todo!(),
        Effect::Increase(function, fexp) => function_op(compiler, function, &fexp.1, SupportedFunctionOp::INC, instructions),
        Effect::Decrease(_, _) => todo!(),
    }
}

fn compile_basic_action<'src>(compiler:&CompilerData<'src>, args:Option<&[(&Name<'src>, &Name<'src>)]>, action:&BasicAction<'src>) -> Result<CompiledAction<'src>, Error<'src>> {
    let mut precondition = Vec::new();
    action.precondition.as_ref().and_then(|p| Some(compile_precondition(compiler, p, args, &mut precondition))).unwrap_or(Ok(()))?;
    let mut effect = Vec::new();
    action.effect.as_ref().and_then(|e| Some(compile_effect(compiler, e, args, &mut effect))).unwrap_or(Ok(()))?;
    Ok(CompiledAction {name:action.name.clone(), precondition, effect})
}


/// Action parameters type to object map results in permutations
/// of objects that match given type. When checking if action can 
/// be accomplished we need to choose over which actions to perform it.
/// Having one action per concrete object tuple allows us to use the same 
/// heuristic to decide if actions over some objects are more likely to 
/// accomplish goal than other actions over some objects. Alternative is
/// to have heuristic function advise both order of actions and order of 
/// objects.
/// # Arguments
/// * `compiler` - all pre-computed maps maintained by the compiler
/// * `domain` - PDDL Domain that defines all the actions needed to create.
fn create_concrete_actions<'src>(compiler:&CompilerData<'src>, domain:&Domain<'src>) -> Result<Vec<CompiledAction<'src>>, Error<'src>> {
    let mut all_actions = Vec::with_capacity(compiler.predicate_memory_map.len()*domain.actions.len()/5);
    for action in &domain.actions {
        if let Action::Basic(action @ BasicAction{parameters,..}) = action {
            // Create action for all type-object permutations.
            let actions = for_all_type_object_permutations(&compiler.type_to_objects_map, parameters.as_slice(), |args| compile_basic_action(compiler, Some(args), action))?;
            all_actions.extend(actions)
        } else {
            todo!()
        }
    }
    Ok(all_actions)
}

/// Iterate through proper domain and problem structs to build type tree,
/// object type map, and mapping of predicate calls to memory offsets.
/// # Arguments
/// * `domain` - PDDL Domain
/// * `problem` - PDDL Problem
fn map_objects<'src>(domain:&Domain<'src>, problem:&Problem<'src>) -> Result<CompilerData<'src>, Error<'src>> {
    let requirements = domain.requirements | problem.requirements;
    let mut type_tree = HashMap::new();
    let mut type_src_pos = HashMap::new();
    // Iterate over types and build the type tree
    for List{items, kind} in &domain.types {
        if let Type::Exact(kind) = kind {
            for item in items{
                type_src_pos.insert(item.1, item.0.clone());
                type_tree.insert(item.1, kind.to_owned());
            }
        } else {
            todo!()
        }

    }
    let mut object_to_type_map = HashMap::new();
    let mut type_to_objects_map = HashMap::new();
    let mut object_src_pos = HashMap::new();
    type_to_objects_map.insert("object", Vec::new());
    // Iterate over objects and build a Object to Type and Type to Object maps
    for List{items, kind} in &problem.objects {
        if let Type::Exact(kind) = kind {
            for item in items {
                object_src_pos.insert(item.1, item.0.clone());
                object_to_type_map.insert(item.1, kind.to_owned());
                let mut type_name = kind.1;
                while let Some(parent_type) = type_tree.get(type_name) {
                    if type_to_objects_map.get_mut(type_name).and_then(|vec:&mut Vec<Name>| Some(vec.push(item.to_owned()))).is_none() {
                        type_to_objects_map.insert(type_name, vec![item.to_owned()]);
                    }
                    type_name = parent_type.1;
                }
            }
        } else {
            todo!()
        }
        type_to_objects_map.get_mut("object").and_then(|vec:&mut Vec<Name>| Some(vec.extend(items.iter().cloned())));
    }
    let mut predicate_memory_map = HashMap::new();
    //Iterate over predicates and its objects and build a memory map
    for AtomicFSkeleton{name, variables} in &domain.predicates {
        for_all_type_object_permutations(&type_to_objects_map, &variables, |args| {
            let mut call_vec = vec![name.1];
            call_vec.extend(args.iter().map(|i| i.1.1));
            // if name.1 == "ontable" { println!("Memory mapping {:?}", args);}
            predicate_memory_map.insert(call_vec, predicate_memory_map.len());
            Ok(())
        })?;
    }
    // println!("Type map: {:?}", type_to_objects_map.get("container"));
    // println!("Memory use: {} bits.", predicate_memory_map.len());
    Ok(CompilerData{requirements, type_tree, type_src_pos, object_to_type_map, type_to_objects_map, object_src_pos, predicate_memory_map})
}

#[cfg(test)]
pub mod tests {
    use std::fs;
    use crate::{parser::{parse_domain, parse_problem}, compiler::compile_problem};

    #[test]
    fn test_barman_domain() {
        let filename = "sample_problems/simple_domain.pddl";
        let domain_src = fs::read_to_string(filename).unwrap();
        let domain = match parse_domain(&domain_src) {
            Err(e) => {e.report(filename).eprint((filename, ariadne::Source::from(&domain_src))); panic!() },
            Ok(d) => d,
        };
        let filename = "sample_problems/simple_problem.pddl";
        let problem_src = fs::read_to_string(filename).unwrap();
        let problem = match parse_problem(&problem_src, domain.requirements) {
            Err(e) => {e.report(filename).eprint((filename, ariadne::Source::from(&problem_src))); panic!() },
            Ok(p) => p
        };
        let c_problem = match compile_problem(&domain, &problem) {
            Err(e) => {e.report(filename).eprint((filename, ariadne::Source::from(&problem_src))); panic!() },
            Ok(cd) => cd,
        };
        println!("Compiled problem needs {} bits of memory and uses {} actions.", c_problem.memory_size, c_problem.actions.len());
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