use std::{collections::HashMap, slice::Iter};

mod maps;
use maps::Maps;
use enumset::{EnumSet, EnumSetType};
mod passes;

// optimization mods
pub mod action_graph;
mod inertia;

pub use crate::parser::{ast::{*, name::Name}, *};
use crate::{Error, ErrorKind};

use self::{action_graph::ActionGraph, maps::{validate_problem, map_objects}, passes::Compiler};

pub type PredicateUsize = u16;
pub type ASTActionUsize = u16;
pub type CompiledActionUsize = u32;
pub type StateUsize = u16;
pub type IntValue = i64;

/// Primitive bytecode needed to check action preconditions and apply effects to a "state"(memory).
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Instruction {
    ReadState(StateUsize),
    SetState(StateUsize),
    ReadFunction(StateUsize),
    SetFunction(StateUsize),
    And(PredicateUsize),
    Not,
    Or,
    Add,
    Sub,
    /// Push immediate
    Push(IntValue),
}

/// [`Instruction`] interpreter has stack of this type to help safety of different storage types.
enum Value {
    Bool(bool),
    Int(IntValue),
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
    pub fn unwrap_int(&self) -> IntValue {
        match self {
            Self::Int(i) => *i,
            _ => panic!("Expected int stack item."),
        }
    }
}

/// Helper trait to easier manage `Vec<Instruction>` fields of actions.
pub trait Runnable {
    fn run(self, state: &[bool], functions: &[IntValue]) -> bool;
    fn run_mut(self, state: &mut [bool], functions: &mut [IntValue]);
    fn state_miss_count(self, state: &[bool]) -> IntValue;
    fn disasm(self) -> String;
    fn decomp(self, memory_map:&Vec<AtomicFormula<Name>>) -> String;
}

impl Runnable for &[Instruction] {
    fn run(self, state: &[bool], _: &[IntValue]) -> bool {
        let mut stack = Vec::<Value>::with_capacity(512);
        for instruction in self {
            match instruction {
                Instruction::ReadState(addr) => stack.push(Value::Bool(state[*addr as usize])),
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
                    if let Some(v) = stack.pop() {
                        stack.push(Value::Bool(!v.unwrap_bool()));
                    } else {
                        stack.push(Value::Bool(false))
                    }
                }
                Instruction::Or => todo!(),
                Instruction::Add => todo!(),
                Instruction::Sub => todo!(),
                Instruction::Push(n) => stack.push(Value::Int(*n)),
            }
        }
        stack.pop().unwrap_or_default().unwrap_bool()
    }

    fn run_mut(self, state: &mut [bool], functions: &mut [i64]) {
        let mut stack = Vec::<Value>::with_capacity(512);
        for instruction in self {
            match instruction {
                Instruction::SetState(addr) => {
                    if let Some(v) = stack.pop() {
                        state[*addr as usize] = v.unwrap_bool()
                    } else {
                        state[*addr as usize] = true
                    }
                }
                Instruction::ReadState(addr) => stack.push(Value::Bool(state[*addr as usize])),
                Instruction::ReadFunction(addr) => {
                    stack.push(Value::Int(functions[*addr as usize]))
                } // todo
                Instruction::SetFunction(addr) => {
                    functions[*addr as usize] = stack.pop().unwrap().unwrap_int();
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
                    if let Some(v) = stack.pop() {
                        stack.push(Value::Bool(!v.unwrap_bool()));
                    } else {
                        stack.push(Value::Bool(false))
                    }
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

    fn state_miss_count(self, state: &[bool]) -> i64 {
        let mut stack = Vec::<Value>::with_capacity(512);
        let mut state_miss_count = 0;
        for instruction in self {
            match instruction {
                Instruction::ReadState(addr) => stack.push(Value::Bool(state[*addr as usize])),
                Instruction::SetState(_) => todo!(),
                Instruction::ReadFunction(_) => todo!(),
                Instruction::SetFunction(_) => todo!(),
                Instruction::And(count) => {
                    let mut result = true;
                    let mut count = *count;
                    while count > 0 {
                        let sv = stack.pop().unwrap().unwrap_bool();
                        if !sv {
                            state_miss_count += 1
                        }
                        result &= sv;
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
                Instruction::Push(_) => todo!(),
            }
        }
        if state_miss_count == 0 && !stack.pop().unwrap_or_default().unwrap_bool() {
            state_miss_count += 1;
        }
        state_miss_count
    }

    fn disasm(self) -> String {
        let mut result = String::with_capacity(self.len() * 6);
        for instruction in self {
            if result.len() > 0 {
                result.push_str(", ");
            }
            match instruction {
                Instruction::ReadState(addr) => result.push_str(&format!("RS({})", *addr)),
                Instruction::SetState(addr) => result.push_str(&format!("WS({})", *addr)),
                Instruction::ReadFunction(addr) => result.push_str(&format!("RF({})", *addr)),
                Instruction::SetFunction(addr) => result.push_str(&format!("WF({})", *addr)),
                Instruction::And(count) => result.push_str(&format!("AND_{}", *count)),
                Instruction::Not => result.push_str("NOT"),
                Instruction::Or => result.push_str("OR"),
                Instruction::Add => result.push_str("ADD"),
                Instruction::Sub => result.push_str("SUB"),
                Instruction::Push(value) => result.push_str(&format!("PUSH({})", *value)),
            }
        }
        result
    }

    fn decomp(self, memory_map:&Vec<AtomicFormula<Name>>) -> String {
        let mut result = String::with_capacity(self.len() * 6);
        for instruction in self {
            if result.len() > 0 {
                result.push_str(", ");
            }
            match instruction {
                Instruction::ReadState(addr) => result.push_str(&format!("RS({})", memory_map[*addr as usize])),
                Instruction::SetState(addr) => result.push_str(&format!("WS({})", memory_map[*addr as usize])),
                Instruction::ReadFunction(addr) => result.push_str(&format!("RF({})", *addr)),
                Instruction::SetFunction(addr) => result.push_str(&format!("WF({})", *addr)),
                Instruction::And(count) => result.push_str(&format!("AND_{}", *count)),
                Instruction::Not => result.push_str("NOT"),
                Instruction::Or => result.push_str("OR"),
                Instruction::Add => result.push_str("ADD"),
                Instruction::Sub => result.push_str("SUB"),
                Instruction::Push(value) => result.push_str(&format!("PUSH({})", *value)),
            }
        }
        result
    }
}

/// Flatenned problem ready for solving
/// All instrutions use shared memory offsets
/// no larger than `self.memory_size`
#[derive(Debug, PartialEq)]
pub struct CompiledProblem {
    /// How many bits needed to fully represent this problem's state
    /// (Actual memory used depends on type used to represent state.
    /// A Vec<bool> will use `memory_size` bytes.)
    pub memory_size: StateUsize,
    /// Out of `memory_size` memory used, `constants_size` will never change during the search.
    pub constants_size: StateUsize,
    /// All compiled actions for this problem. Each domain action compiles into
    /// multiple [`CompiledAction`]s due to object permutations for various predicates and types.
    pub actions: Vec<CompiledAction>,
    /// Executable bytecode to set initial conditions
    pub init: Vec<Instruction>,
    /// Executable bytecode to check if the goal is met
    pub goal: Vec<Instruction>,
    /// Priority list of compiled actions to try
    pub action_graph: ActionGraph,
}

/// Flatenned representation of Actions inside [`CompiledProblem`]s
/// All instruction offsets point to shared memory
#[derive(Debug, PartialEq)]
pub struct CompiledAction {
    /// Offset into [`Domain`].actions vector pointing to source of this action,
    /// in case you need to display a message pointing to that PDDL code location).
    pub domain_action_idx: ASTActionUsize,
    /// Exact object arguments bound to this action. PDDL actions use types to permutate themselves
    /// over various objects. CompiledActions are bound to exact objcts. First u16 is the offset in
    /// problem.objects list. Second u16 is the offset in that list's variables.
    pub args: Vec<(PredicateUsize, PredicateUsize)>,
    /// Executable bytecode to check if action's preconditions are met.
    pub precondition: Vec<Instruction>,
    /// Executable bytecode to apply action effects.
    pub effect: Vec<Instruction>,
}

impl CompiledAction {
    pub fn new() -> Self {
        Self {
            domain_action_idx: 0,
            args: Vec::new(),
            precondition: Vec::new(),
            effect: Vec::new(),
        }
    }
}

/// Enumeration of various optimizations implemented in the compiler
/// to allow for automatic swithching of them on and off.
#[derive(EnumSetType, Debug)]
pub enum Optimization {
    // /// Following the Koehler, Jana, and Jörg Hoffmann. "On the Instantiation of ADL Operators Involving Arbitrary First-Order Formulas." PuK. 2000. [paper](https://www.researchgate.net/profile/Jana-Koehler-2/publication/220916196_On_the_Instantiation_of_ADL_Operators_Involving_Arbitrary_First-Order_Formulas/links/53f5c12c0cf2fceacc6f65e0/On-the-Instantiation-of-ADL-Operators-Involving-Arbitrary-First-Order-Formulas.pdf),
    // /// Inertia allows us to start pruning unused states, actions, and instatiate basic action-graphs allowing us to skip many dead-end states.
    // Inertia,
}

impl Optimization {
    pub const NONE: EnumSet<Self> = EnumSet::EMPTY;
    pub const ALL: EnumSet<Self> = EnumSet::ALL;
}

/// Compile and optimize parsed [`Domain`] and [`Problem`] structures into a compiled problem ready for using in search methods.
/// Load them from a file using [`parse_domain`] and [`parse_problem`] functions.
pub fn compile_problem<'src, 'ast>(
    domain: &'ast Domain<'src>,
    problem: &'ast Problem<'src>,
) -> Result<CompiledProblem, Vec<Error>> {
    validate_problem(domain, problem)?;
    let mut maps = map_objects(domain, problem)?;
    let mut compiler = Compiler::new(domain, problem, maps);
    compiler.compile()
}


/// Given a list of types, use a type to object map and generate all possible
/// permutations of the objects fitting the list.
///
/// # Arguments
/// * `type_to_objects` - a map of type names to vector of all world objects of that type.
/// * `list` - the argument list that needs to be populated with world objects.
/// * `f` - closure that gets all permutations of objects populated the `list` in a form of a slice
///     mapping `list`'s items to world object indexes - `&[(ListItemName, (row, col))]`
fn for_all_type_object_permutations<'src, F, O>(
    type_to_objects: &HashMap<&'src str, Vec<(PredicateUsize, PredicateUsize)>>,
    list: &[List<'src>],
    mut f: F,
) -> Result<Vec<O>, Error>
where
    F: FnMut(&[(Name<'src>, (PredicateUsize, PredicateUsize))]) -> Result<Option<O>, Error>,
{
    use ErrorKind::UndefinedType;

    fn _has_collition<'parent, 'src>(
        args: &[(
            Name<'src>,
            (PredicateUsize, PredicateUsize),
        )],
        iterators: &[(&'src str, Iter<'parent, (PredicateUsize, PredicateUsize)>)],
    ) -> bool {
        for i in 0..iterators.len() {
            for j in 0..iterators.len() {
                if args[i].1 .1 == args[j].1 .1 && i != j && iterators[i].0 == iterators[j].0 {
                    return true;
                }
            }
        }
        false
    }
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
    /// # Return:
    /// Returns false when it's impossible to iterate more, true when we can keep going.
    fn _args_iter<'parent, 'src>(
        type_to_objects: &'parent HashMap<&'src str, Vec<(PredicateUsize, PredicateUsize)>>,
        iterators: &mut [(&'src str, Iter<'parent, (PredicateUsize, PredicateUsize)>)],
        args: &mut [(
            Name<'src>,
            (PredicateUsize, PredicateUsize),
        )],
        pos: usize,
    ) -> bool {
        if let Some(arg) = iterators[pos].1.next() {
            args[pos].1 = *arg;
            if pos == 0 && _has_collition(args, iterators) {
                _args_iter(type_to_objects, iterators, args, pos)
            } else {
                true
            }
            // _no_collisions(type_to_objects, args, iterators, pos)
        } else if pos + 1 < iterators.len() {
            let kind = iterators[pos].0;
            if let Some(vec) = type_to_objects.get(kind) {
                iterators[pos].1 = vec.iter();
                if let Some(arg) = iterators[pos].1.next() {
                    args[pos].1 = *arg;
                }
            }
            let r = _args_iter(type_to_objects, iterators, args, pos + 1);
            if r && pos == 0 && _has_collition(args, iterators) {
                _args_iter(type_to_objects, iterators, args, pos)
            } else {
                r
            }
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
                            args.push((*item, *next));
                        } else {
                            // Not enough objects to populate this list
                            todo!()
                        }
                    }
                } else {
                    return Err(Error {
                        // input: None,
                        kind: UndefinedType,
                        chain: None,
                        span: kind.0,
                    });
                }
            }
            Type::None => {
                let objects_vec = type_to_objects.get("object").unwrap();
                for item in items {
                    iterators.push(("object", objects_vec.iter()));
                    if let Some(next) = iterators.last_mut().unwrap().1.next() {
                        args.push((*item, *next));
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
    let r = if _has_collition(&args, &iterators) {
        _args_iter(
            type_to_objects,
            iterators.as_mut_slice(),
            args.as_mut_slice(),
            0,
        )
    } else {
        true
    };
    let mut result = if let Some(v) = f(args.as_slice())? {
        vec![v]
    } else {
        Vec::new()
    };

    if !r {
        return Ok(result);
    }
    while _args_iter(
        type_to_objects,
        iterators.as_mut_slice(),
        args.as_mut_slice(),
        0,
    ) {
        if let Some(v) = f(args.as_slice())? {
            result.push(v);
        }
    }
    Ok(result)
}

#[cfg(test)]
pub mod tests {
    use lazy_static::lazy_static;

    use crate::{
        compiler::{CompiledAction, Instruction},
        Sources,
    };

    use super::*;

    pub const TINY_DOMAIN_SRC: &str = "(define (domain unit-test)
    (:predicates (a ?one) (b ?one ?two))
    (:action aOne :parameters(?one ?two) 
        :precondition(and (a ?one) (b ?one ?two) (a ?two))
        :effect (and (not (a ?one)) (not (a ?two)))
    ))";
    pub const TINY_PROBLEM_SRC: &str = "(define (problem unit-test)
    (:domain unit-test)
    (:objects a b c)
    (:init (a a) (a b) (b a b))
    (:goal (not (a a)))
    )";

    lazy_static! {
        pub static ref TINY_SOURCES: Sources = Sources {
            domain_path: "stdin_domain".into(),
            problem_path: "stdin_problem".into(),
            domain_ad: ariadne::Source::from(TINY_DOMAIN_SRC),
            problem_ad: ariadne::Source::from(TINY_PROBLEM_SRC),
            domain_src: TINY_DOMAIN_SRC.into(),
            problem_src: TINY_PROBLEM_SRC.into()
        };
    }

    #[test]
    fn test_permutations() {
        let type_to_objects = HashMap::from([("object", vec![(0, 0), (0, 1), (0, 2), (0, 3)])]);
        let list = vec![List {
            items: vec![
                Name::new(0..0, "var1"),
                Name::new(0..0, "var2"),
                Name::new(0..0, "var3"),
            ],
            kind: Type::None,
        }];
        let result = for_all_type_object_permutations(&type_to_objects, &list, |args| {
            assert_eq!(args.len(), 3);
            Ok(Some((args[0].1 .1, args[1].1 .1, args[2].1 .1)))
        })
        .unwrap();
        assert_eq!(
            result,
            vec![
                // (0, 0, 0),
                // (1, 0, 0),
                // (2, 0, 0),
                // (3, 0, 0),
                // (0, 1, 0),
                // (1, 1, 0),
                (2, 1, 0),
                (3, 1, 0),
                // (0, 2, 0),
                (1, 2, 0),
                // (2, 2, 0),
                (3, 2, 0),
                // (0, 3, 0),
                (1, 3, 0),
                (2, 3, 0),
                // (3, 3, 0),
                // (0, 0, 1),
                // (1, 0, 1),
                (2, 0, 1),
                (3, 0, 1),
                // (0, 1, 1),
                // (1, 1, 1),
                // (2, 1, 1),
                // (3, 1, 1),
                (0, 2, 1),
                // (1, 2, 1),
                // (2, 2, 1),
                (3, 2, 1),
                (0, 3, 1),
                // (1, 3, 1),
                (2, 3, 1),
                // (3, 3, 1),
                // (0, 0, 2),
                (1, 0, 2),
                // (2, 0, 2),
                (3, 0, 2),
                (0, 1, 2),
                // (1, 1, 2),
                // (2, 1, 2),
                (3, 1, 2),
                // (0, 2, 2),
                // (1, 2, 2),
                // (2, 2, 2),
                // (3, 2, 2),
                (0, 3, 2),
                (1, 3, 2),
                // (2, 3, 2),
                // (3, 3, 2),
                // (0, 0, 3),
                (1, 0, 3),
                (2, 0, 3),
                // (3, 0, 3),
                (0, 1, 3),
                // (1, 1, 3),
                (2, 1, 3),
                // (3, 1, 3),
                (0, 2, 3),
                (1, 2, 3),
                // (2, 2, 3),
                // (3, 2, 3),
                // (0, 3, 3),
                // (1, 3, 3),
                // (2, 3, 3),
                // (3, 3, 3),
            ]
        );
    }

    #[test]
    #[ignore = "New compiler has undeterministic memory mapping. This test fails half-the time."]
    fn test_action() {
        use Instruction::*;
        let (domain, problem) = TINY_SOURCES.parse();
        let problem = TINY_SOURCES.compile(&domain, &problem);
        assert_eq!(problem.memory_size, 2);
        assert_eq!(problem.init, vec![SetState(0), SetState(1)]);
        assert_eq!(problem.goal, vec![ReadState(0), Not]);
        assert_eq!(problem.actions.len(), 1);
        assert_eq!(
            problem.actions[0],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![(0, 0), (0, 1)], // b a
                precondition: vec![ReadState(1), ReadState(0), And(2)],
                effect: vec![Not, SetState(1), Not, SetState(1)],
                // action_graph: ActionGraph { priority: vec![] },
            }
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
