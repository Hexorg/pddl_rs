use std::{collections::HashMap, slice::Iter};

mod preprocess;
use preprocess::{preprocess, PreprocessData};
mod first_pass;
use first_pass::first_pass;
mod final_pass;
use final_pass::final_pass;

pub use crate::parser::{ast::*, *};
use crate::{Error, ErrorKind};


/// Primitive bytecode needed to check action preconditions and apply effects to a "state"(memory).
#[derive(Debug, PartialEq)]
pub enum Instruction {
    ReadState(usize),
    SetState(usize),
    ReadFunction(usize),
    SetFunction(usize),
    And(usize),
    Not,
    Or,
    Add,
    Sub,
    /// Push immediate
    Push(i64),
}

/// [`Instruction`] interpreter has stack of this type to help safety of different storage types.
enum Value {
    Bool(bool),
    Int(i64),
}

impl Default for Value {
    fn default() -> Self {
        Self::Bool(false)
    }
}

impl Value {
    pub fn unwrap_bool(&self) -> bool {
        match self {
            Self::Bool(b) => *b,
            _ => panic!("Expected bool stack item."),
        }
    }
    pub fn unwrap_int(&self) -> i64 {
        match self {
            Self::Int(i) => *i,
            _ => panic!("Expected int stack item."),
        }
    }
}

/// Helper trait to easier manage `Vec<Instruction>` fields of actions.
pub trait Runnable {
    fn run(&self, state: &[bool], functions: &[i64]) -> bool;
    fn run_mut(&self, state: &mut [bool], functions: &mut [i64]);
}

impl Runnable for Vec<Instruction> {
    fn run(&self, state: &[bool], _: &[i64]) -> bool {
        let mut stack = Vec::<Value>::with_capacity(512);
        for instruction in self {
            match instruction {
                Instruction::ReadState(addr) => stack.push(Value::Bool(state[*addr])),
                Instruction::SetState(_) => panic!("Instructions try to chane immutable state."),
                Instruction::ReadFunction(_) => todo!(),
                Instruction::SetFunction(_) => todo!(),
                Instruction::And(count) => {
                    let mut result = true;
                    let mut count = *count;
                    while count > 0 {
                        result &= stack.pop().unwrap().unwrap_bool();
                        count -= 1;
                    }
                    stack.push(Value::Bool(result));
                }
                Instruction::Not => {
                    let s = !stack.pop().unwrap().unwrap_bool();
                    stack.push(Value::Bool(s));
                }
                Instruction::Or => todo!(),
                Instruction::Add => todo!(),
                Instruction::Sub => todo!(),
                Instruction::Push(n) => stack.push(Value::Int(*n)),
            }
        }
        stack.pop().unwrap_or_default().unwrap_bool()
    }

    fn run_mut(&self, state: &mut [bool], functions: &mut [i64]) {
        let mut stack = Vec::<Value>::with_capacity(512);
        for instruction in self {
            match instruction {
                Instruction::SetState(addr) => state[*addr] = stack.pop().unwrap().unwrap_bool(),
                Instruction::ReadState(addr) => stack.push(Value::Bool(state[*addr])),
                Instruction::ReadFunction(addr) => stack.push(Value::Int(functions[*addr])), // todo
                Instruction::SetFunction(addr) => {
                    functions[*addr] = stack.pop().unwrap().unwrap_int();
                } // todo
                Instruction::And(count) => {
                    let mut result = true;
                    let mut count = *count;
                    while count > 0 {
                        result &= stack.pop().unwrap().unwrap_bool();
                        count -= 1;
                    }
                    stack.push(Value::Bool(result));
                }
                Instruction::Not => {
                    let s = !stack.pop().unwrap().unwrap_bool();
                    stack.push(Value::Bool(s));
                }
                Instruction::Or => todo!(),
                Instruction::Add => {
                    let s = stack.pop().unwrap().unwrap_int() + stack.pop().unwrap().unwrap_int();
                    stack.push(Value::Int(s));
                }
                Instruction::Sub => todo!(),
                Instruction::Push(n) => stack.push(Value::Int(*n)),
            }
        }
    }
}

/// Flatenned problem ready for solving
/// All instrutions use shared memory offsets
/// no larger than `self.memory_size`
#[derive(Debug, PartialEq)]
pub struct CompiledProblem<'src> {
    /// How many bits needed to fully represent this problem's state
    /// (Actual memory used depends on type used to represent state.
    /// A Vec<bool> will use `memory_size` bytes.)
    pub memory_size: usize,
    /// All compiled actions for this problem. Each domain action compiles into
    /// multiple [`CompiledAction`]s due to object permutations for various predicates and types.
    pub actions: Vec<CompiledAction<'src>>,
    /// Executable bytecode to set initial conditions
    pub init: Vec<Instruction>,
    /// Executable bytecode to check if the goal is met
    pub goal: Vec<Instruction>,
}

/// Flatenned representation of Actions inside [`CompiledProblem`]s
/// All instruction offsets point to shared memory
#[derive(Debug, PartialEq)]
pub struct CompiledAction<'src> {
    /// Name of the domain action (along with range of that name in the source code,
    /// in case you need to display a message pointing to that PDDL code location).
    pub name: Name<'src>,
    /// Exect object arguments bound to this action. PDDL actions use types to permutate themselves
    /// over various objects. CompiledActions are bound to exact objcts.
    pub args: Vec<Name<'src>>,
    /// Executable bytecode to check if action's preconditions are met.
    pub precondition: Vec<Instruction>,
    /// Executable bytecode to apply action effects.
    pub effect: Vec<Instruction>,
}

/// Compile and optimize parsed [`Domain`] and [`Problem`] structures into a compiled problem ready for using in search methods.
/// Load them from a file using [`parse_domain`] and [`parse_problem`] functions.
pub fn compile_problem<'src>(
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<CompiledProblem<'src>, Error<'src>> {
    let preprocess_data = preprocess(domain, problem)?;
    let first_pass_data = first_pass(preprocess_data, domain, problem)?;
    final_pass(&first_pass_data, domain, problem)
}

/// Given a list of types, use a type to object map and generate all possible
/// permutations of the objects fitting the list.
///
/// # Arguments
/// * `type_to_objects` - a map of type names to vector of all world objects of that type.
/// * `list` - the argument list that needs to be populated with world objects.
/// * `f` - closure that gets all permutations of objects populated the `list` in a form of a slice
///     mapping `list`'s items to world object names - `&[(ListItemName, ObjectName)]`
fn for_all_type_object_permutations<'src, F, O>(
    type_to_objects: &HashMap<&'src str, Vec<Name<'src>>>,
    list: &[List<'src>],
    mut f: F,
) -> Result<Vec<O>, Error<'src>>
where
    F: FnMut(&[(&Name<'src>, &Name<'src>)]) -> Result<O, Error<'src>>,
{
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
    fn _args_iter<'parent, 'src>(
        type_to_objects: &'parent HashMap<&'src str, Vec<Name<'src>>>,
        iterators: &mut [(&'src str, Iter<'parent, Name<'src>>)],
        args: &mut [(&'parent Name<'src>, &'parent Name<'src>)],
        pos: usize,
    ) -> bool {
        if let Some(arg) = iterators[pos].1.next() {
            args[pos].1 = arg;
            true
        } else if pos + 1 < iterators.len() {
            let kind = iterators[pos].0;
            if let Some(vec) = type_to_objects.get(kind) {
                iterators[pos].1 = vec.iter();
                if let Some(arg) = iterators[pos].1.next() {
                    args[pos].1 = arg;
                }
            }
            _args_iter(type_to_objects, iterators, args, pos + 1)
        } else {
            // We're done permutating
            false
        }
    }

    let mut iterators = Vec::new();
    let mut args = Vec::new();
    // We need to create `objects_vec.len()`` many args - one per object of this type.
    // First, create an iterator per argument type
    for List { items, kind } in list {
        match kind {
            Type::Exact(kind) => {
                if let Some(objects_vec) = type_to_objects.get(kind.1) {
                    for item in items {
                        iterators.push((kind.1, objects_vec.iter()));
                        if let Some(next) = iterators.last_mut().unwrap().1.next() {
                            args.push((item, next));
                        } else {
                            // Not enough objects to populate this list
                            todo!()
                        }
                    }
                } else {
                    return Err(Error {
                        input: None,
                        kind: UndefinedType,
                        chain: None,
                        range: kind.0.clone(),
                    });
                }
            }
            Type::None => {
                let objects_vec = type_to_objects.get("object").unwrap();
                for item in items {
                    iterators.push(("object", objects_vec.iter()));
                    if let Some(next) = iterators.last_mut().unwrap().1.next() {
                        args.push((item, next));
                    } else {
                        // Not enough objects to populate this list
                        todo!()
                    }
                }
            }
            Type::Either(_) => todo!(),
        }
    }
    // Itereate until the most significant iterator is done, calling closure over populated args
    let mut result = vec![f(args.as_slice())?];
    while _args_iter(
        type_to_objects,
        iterators.as_mut_slice(),
        args.as_mut_slice(),
        0,
    ) {
        result.push(f(args.as_slice())?);
    }
    Ok(result)
}



#[cfg(test)]
pub mod tests {
    use crate::{
        compiler::{compile_problem, CompiledAction, Instruction},
        parser::{parse_domain, parse_problem},
    };

    use super::*;

    fn get_tiny_domain() -> (Domain<'static>, Problem<'static>) {
        let domain = parse_domain(
            "(define (domain unit-test)
                (:predicates (a ?one) (b ?one ?two))
                (:action aOne :parameters(?one ?two) 
                    :precondition(and (a ?one) (b ?one ?two) (a ?two))
                    :effect (and (not (a ?one)) (not (a ?two)))
                ))",
        )
        .unwrap();
        let problem = parse_problem(
            "(define (problem unit-test)
                (:domain unit-test)
                (:objects a b c)
                (:init (a a) (b a b))
                (:goal (not (a a)))
                )",
            enumset::EnumSet::EMPTY,
        )
        .unwrap();
        (domain, problem)
    }

    
    #[test]
    fn test_action() {
        use Instruction::*;
        let (domain, problem) = get_tiny_domain();
        let problem = compile_problem(&domain, &problem).unwrap();
        assert_eq!(problem.memory_size, 12);
        assert_eq!(problem.init, vec![And(0), SetState(0), And(0), SetState(6)]);
        assert_eq!(problem.goal, vec![ReadState(0), Not]);
        assert_eq!(problem.actions.len(), 9);
        assert_eq!(
            problem.actions,
            vec![
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(90..91, "a"), (90..91, "a")], // a a
                    precondition: vec![ReadState(0), ReadState(3), ReadState(0), And(3)],
                    effect: vec![And(0), Not, SetState(0), And(0), Not, SetState(0)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(92..93, "b"), (90..91, "a")], // b a
                    precondition: vec![ReadState(1), ReadState(4), ReadState(0), And(3)],
                    effect: vec![And(0), Not, SetState(1), And(0), Not, SetState(0)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(94..95, "c"), (90..91, "a")], // c a
                    precondition: vec![ReadState(2), ReadState(5), ReadState(0), And(3)],
                    effect: vec![And(0), Not, SetState(2), And(0), Not, SetState(0)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(90..91, "a"), (92..93, "b")], // a b
                    precondition: vec![ReadState(0), ReadState(6), ReadState(1), And(3)],
                    effect: vec![And(0), Not, SetState(0), And(0), Not, SetState(1)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(92..93, "b"), (92..93, "b")], // b b
                    precondition: vec![ReadState(1), ReadState(7), ReadState(1), And(3)],
                    effect: vec![And(0), Not, SetState(1), And(0), Not, SetState(1)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(94..95, "c"), (92..93, "b")], // c b
                    precondition: vec![ReadState(2), ReadState(8), ReadState(1), And(3)],
                    effect: vec![And(0), Not, SetState(2), And(0), Not, SetState(1)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(90..91, "a"), (94..95, "c")], // a c
                    precondition: vec![ReadState(0), ReadState(9), ReadState(2), And(3)],
                    effect: vec![And(0), Not, SetState(0), And(0), Not, SetState(2)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(92..93, "b"), (94..95, "c")], // b c
                    precondition: vec![ReadState(1), ReadState(10), ReadState(2), And(3)],
                    effect: vec![And(0), Not, SetState(1), And(0), Not, SetState(2)]
                },
                CompiledAction {
                    name: (105..109, "aOne"),
                    args: vec![(94..95, "c"), (94..95, "c")], // c c
                    precondition: vec![ReadState(2), ReadState(11), ReadState(2), And(3)],
                    effect: vec![And(0), Not, SetState(2), And(0), Not, SetState(2)]
                }
            ]
        );
    }

    #[test]
    fn test_basic_execution() {
        use Instruction::*;
        let instructions = vec![ReadState(0), Not, ReadState(1), And(2)];
        let mut state = vec![false, true];
        let mut functions = vec![0];
        assert_eq!(instructions.run(&state, &functions), true);
        let instructions = vec![ReadState(0), ReadState(1), And(2)];
        assert_eq!(instructions.run(&state, &functions), false);
        let instructions = vec![ReadState(0), SetState(1)];
        instructions.run_mut(&mut state, &mut functions);
        assert_eq!(state[0], false);
        assert_eq!(state[1], false);
    }
}
