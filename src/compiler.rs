use std::{collections::{HashMap, HashSet}, ops::Range, slice::Iter, path::PathBuf};

pub mod maps;
use enumset::{EnumSet, EnumSetType};
mod passes;
mod domain;

pub mod action_plotter;
// optimization mods
pub mod action_graph;
pub mod inertia;
pub mod atomic_formula_map;
mod solution_estimation;

use crate::parser::{
    ast::{name::Name, *, r#type::Type, atomic_formula::AtomicFormula, list::{TypedList, List}},
    *,
};
use crate::{Error, ErrorKind};

use self::{
    action_graph::ActionGraph,
    maps::{validate_problem, Maps},
    inertia::Inertia,
    passes::Compiler,
};

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


/// Helper trait to easier manage `Vec<Instruction>` fields of actions.
pub trait Runnable {
    fn run(self, state: &[bool], functions: &[IntValue], state_stack: &mut Vec<bool>, function_stack: &mut Vec<IntValue>) -> bool;
    fn run_mut(self, state: &mut [bool], functions: &mut [IntValue], state_stack: &mut Vec<bool>, function_stack: &mut Vec<IntValue>);
    fn state_miss_count(self, state: &[bool], state_stack: &mut Vec<bool>) -> IntValue;
    fn disasm(self) -> String;
    fn decomp(self, memory_map: &Vec<AtomicFormula<Name>>) -> String;
}

impl Runnable for &[Instruction] {
    // #[inline]
    fn run(self, state: &[bool], _: &[IntValue], state_stack: &mut Vec<bool>, function_stack: &mut Vec<IntValue>) -> bool {
        // let mut bool_stack = Vec::<bool>::with_capacity(512);
        for instruction in self {
            match instruction {
                Instruction::ReadState(addr) => state_stack.push(state[*addr as usize]),
                Instruction::SetState(_) => panic!("Instructions try to chane immutable state."),
                Instruction::ReadFunction(_) => todo!(),
                Instruction::SetFunction(_) => todo!(),
                Instruction::And(count) => {
                    let mut result = true;
                    let mut count = *count;
                    while count > 0 {
                        result &= state_stack.pop().unwrap();
                        count -= 1;
                    }
                    state_stack.push(result);
                }
                Instruction::Not => {
                    if let Some(v) = state_stack.pop() {
                        state_stack.push(!v);
                    } else {
                        state_stack.push(false);
                    }
                }
                Instruction::Or => todo!(),
                Instruction::Add => todo!(),
                Instruction::Sub => todo!(),
                Instruction::Push(_) => todo!(),
            }
        }
        state_stack.pop().unwrap_or_default()
    }

    fn run_mut(self, state: &mut [bool], functions: &mut [i64], state_stack: &mut Vec<bool>, function_stack: &mut Vec<IntValue>) {
        for instruction in self {
            match instruction {
                Instruction::SetState(addr) => {
                    if let Some(v) = state_stack.pop() {
                        state[*addr as usize] = v
                    } else {
                        state[*addr as usize] = true
                    }
                }
                Instruction::ReadState(addr) => state_stack.push(state[*addr as usize]),
                Instruction::ReadFunction(addr) => {
                    function_stack.push(functions[*addr as usize])
                } // todo
                Instruction::SetFunction(addr) => {
                    functions[*addr as usize] = function_stack.pop().unwrap();
                } // todo
                Instruction::And(count) => {
                    let mut result = true;
                    let mut count = *count;
                    while count > 0 {
                        result &= state_stack.pop().unwrap();
                        count -= 1;
                    }
                    state_stack.push(result);
                }
                Instruction::Not => {
                    if let Some(v) = state_stack.pop() {
                        state_stack.push(!v);
                    } else {
                        state_stack.push(false);
                    }
                }
                Instruction::Or => todo!(),
                Instruction::Add => {
                    let s = function_stack.pop().unwrap() + function_stack.pop().unwrap();
                    function_stack.push(s);
                }
                Instruction::Sub => todo!(),
                Instruction::Push(n) => function_stack.push(*n),
            }
        }
    }

    fn state_miss_count(self, state: &[bool], state_stack: &mut Vec<bool>) -> i64 {
        let mut state_miss_count = 0;
        for instruction in self {
            match instruction {
                Instruction::ReadState(addr) => state_stack.push(state[*addr as usize]),
                Instruction::SetState(_) => todo!(),
                Instruction::ReadFunction(_) => todo!(),
                Instruction::SetFunction(_) => todo!(),
                Instruction::And(count) => {
                    let mut result = true;
                    let mut count = *count;
                    while count > 0 {
                        let sv = state_stack.pop().unwrap();
                        if !sv {
                            state_miss_count += 1
                        }
                        result &= sv;
                        count -= 1;
                    }
                    state_stack.push(result);
                }
                Instruction::Not => {
                    let s = !state_stack.pop().unwrap();
                    state_stack.push(s);
                }
                Instruction::Or => todo!(),
                Instruction::Add => todo!(),
                Instruction::Sub => todo!(),
                Instruction::Push(_) => todo!(),
            }
        }
        if state_miss_count == 0 && !state_stack.pop().unwrap_or_default() {
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

    fn decomp(self, memory_map: &Vec<AtomicFormula<Name>>) -> String {
        let mut result = String::with_capacity(self.len() * 6);
        for instruction in self {
            if result.len() > 0 {
                result.push_str(", ");
            }
            match instruction {
                Instruction::ReadState(addr) => {
                    result.push_str(&format!("RS({})", memory_map[*addr as usize]))
                }
                Instruction::SetState(addr) => {
                    result.push_str(&format!("WS({})", memory_map[*addr as usize]))
                }
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
// #[derive(Debug, PartialEq)]
pub struct CompiledProblem<'ast, 'src> {
    /// How many bits needed to fully represent this problem's state
    /// (Actual memory used depends on type used to represent state.
    /// A Vec<bool> will use `memory_size` bytes.)
    pub memory_size: StateUsize,
    /// Out of `memory_size` memory used, `constants_size` will never change during the search.
    pub constants_size: StateUsize,
    /// All compiled actions for this problem. Each domain action compiles into
    /// multiple [`CompiledAction`]s due to object permutations for various predicates and types.
    pub actions: Vec<CompiledAction>,
    /// Mapping of domain action index to a range of compiled actions representing those actions for all used problem objects
    pub domain_action_ranges: Vec<Range<CompiledActionUsize>>,
    /// Executable bytecode to set initial conditions
    pub init: Vec<Instruction>,
    /// Executable bytecode to check if the goal is met
    pub goal: Vec<Instruction>,
    /// Priority list of compiled actions to try
    pub action_graph: ActionGraph,
    /// Summary of what actions can and can not run after each other
    pub inertia:Inertia,
    /// Set of predicate identifiers that represent constant predicates throughout problem solving 
    pub constant_predicate_ids: HashSet<PredicateUsize>,
    /// AST Domain of this problem
    pub domain: &'ast Domain<'src>,
    /// AST Problem of this Compiled Problem
    pub problem: &'ast Problem<'src>,
    /// Maps between AST names and Compiled indexes/numbers
    pub maps: Maps<'src>,
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
    pub args: Vec<PredicateUsize>,
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

impl<'ast, 'src> CompiledProblem<'ast, 'src> {
    /// Get the AST action that this action was compiled from.
    pub fn get_domain_action(&self, action_idx:CompiledActionUsize) -> &'ast Action<'src> {
        &self.domain.actions[self.actions[action_idx as usize].domain_action_idx as usize]
    }
    pub fn get_action_name(&self, action_idx:CompiledActionUsize) -> Name<'src> {
        self.get_domain_action(action_idx).name()
    }

    pub fn get_action_objects<'me>(&'me self, action_idx:CompiledActionUsize) -> impl Iterator<Item = &'src str> + 'me {
        self.actions[action_idx as usize].args.iter()
        .map(move |object_idx| self.maps.id_object_map[*object_idx as usize].1)
    }

    pub fn get_action_string(&self, action_idx:CompiledActionUsize) -> String {
        format!(
            "{}({})",
            self.get_action_name(action_idx),
            self.get_action_objects(action_idx).collect::<Vec<_>>().join(",")
        )
    }

    // pub fn action_path_to_string(&self, path:&Vec<CompiledActionUsize>, sep:&str) -> String {
    //     path.iter().map(|idx| self.get_action_string(*idx)).collect::<Vec<_>>().join(sep)
    // }
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
pub fn compile_problem<'ast, 'src>(
    domain: &'ast Domain<'src>,
    problem: &'ast Problem<'src>,
    domain_file_path: PathBuf,
    problem_file_path: PathBuf,
) -> Result<CompiledProblem<'ast, 'src>, Vec<Error>>
where
    'ast: 'src,
{
    validate_problem(domain, problem)?;
    let mut compiler = Compiler::new(domain, problem, domain_file_path, problem_file_path);
    compiler.compile()
}

/// Permutates over all possible states given a closure to generate an iterator at a given position
/// as well as a closure to generate optional value or error.
/// The function will terminate if an error is generated, or collect all Some(values) into a vector. 
pub fn permutate<G, F, I, O, II>(pos_size:usize, pos_to_iter:G, mut f:F) -> Result<Vec<O>, Error>
where 
    G:Fn(usize) -> II,
    F:for <'b> FnMut(&'b [I]) -> Result<Option<O>, Error>,
    I: PartialEq,
    II: IntoIterator<Item = I> {
    fn _has_collition<I, II>(
        state: &[I],
        _iterators: &[II],
    ) -> bool where I:PartialEq, II:IntoIterator<Item = I>  {
        for i in 0..state.len() {
            for j in 0..state.len() {
                if state[i] == state[j] && i != j { //&& iterators[i] == iterators[j] {
                    return true;
                }
            }
        }
        false
    }
    fn _permutate_recurse<'a, I, II, IT, G>(iterators:&'a mut[IT], state:&'a mut [I], pos:usize, pos_to_iter:&'a G) -> bool 
    where G:Fn(usize) -> II, 
    I:PartialEq, 
    IT: Iterator<Item = I>,
    II:IntoIterator<Item = I, IntoIter = IT> {
        if let Some(value) = iterators[pos].next() {
            state[pos] = value;
            if pos == 0 && _has_collition(state, iterators) {
                _permutate_recurse(iterators, state, pos, pos_to_iter)
            } else {
                true
            }
            // _no_collisions(type_to_objects, args, iterators, pos)
        } else if pos + 1 < iterators.len() {
            iterators[pos] = pos_to_iter(pos).into_iter();
            if let Some(value) = iterators[pos].next() {
                state[pos] = value;
            }
            let r = _permutate_recurse(iterators, state, pos + 1, pos_to_iter);
            if r && pos == 0 && _has_collition(state, iterators) {
                _permutate_recurse(iterators, state, pos, pos_to_iter)
            } else {
                r
            }
        } else {
            // We're done permutating
            false
        }
    }
    let mut iterators = Vec::with_capacity(pos_size);
    let mut state:Vec<I> = Vec::with_capacity(pos_size);
    for pos in 0..pos_size {
        iterators.push(pos_to_iter(pos).into_iter());
        if let Some(next) = iterators.last_mut().unwrap().next() {
            state.push(next);
        } // else - not enough objects to fill the state.
    }
    let r = if _has_collition(&state, &iterators) {
        _permutate_recurse(&mut iterators, &mut state, 0, &pos_to_iter)
    } else {
        true
    };
    let mut result = if let Some(v) = f(state.as_slice())? {
        vec![v]
    } else {
        Vec::new()
    };

    if !r { return Ok(result) }

    while _permutate_recurse(
        &mut iterators,
        &mut state,
        0,
        &pos_to_iter
    ) {
        if let Some(v) = f(state.as_slice())? {
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
        let type_to_objects = HashMap::from([(0, vec![0, 1, 2, 3])]); 
        let type_id_map = HashMap::new();
        let mut maps = Maps::new();
        maps.type_to_objects_map = type_to_objects;
        maps.type_id_map = type_id_map;
        let list: TypedList = vec![List {
            items: vec![
                Name::new(0..0, "var1"),
                Name::new(0..0, "var2"),
                Name::new(0..0, "var3"),
            ],
            kind: Type::None,
        }].into();
        let pos_size = list.len();
        let result = permutate(pos_size, 
        |pos:usize| {
            // let name = list.get_name(pos);
            let kind:u16 = list.get_type(pos).to_id(&maps);
            maps.type_to_objects_map.get(&kind).unwrap().iter().copied()
            // iter.map(move |id| (name, *id))
        }, 
        |args| {
            assert_eq!(args.len(), 3);
            Ok(Some((args[0], args[1], args[2])))
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
    fn test_constrained_permutation() {
        let n = vec![1, 2];
        assert_eq!(permutate(3, |_| n.iter().copied(), |args| {
            Ok(Some(args.to_owned()))
        }), Ok(vec![vec![1, 1, 2]]))
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
                args: vec![0, 1], // b a
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
        let mut state_stack = Vec::with_capacity(10);
        let mut function_stack = Vec::with_capacity(10);
        assert_eq!(instructions.run(&state, &functions, &mut state_stack, &mut function_stack), true);
        let instructions = vec![ReadState(0), ReadState(1), And(2)];
        assert_eq!(instructions.run(&state, &functions, &mut state_stack, &mut function_stack), false);
        let instructions = vec![ReadState(0), SetState(1)];
        instructions.run_mut(&mut state, &mut functions, &mut state_stack, &mut function_stack);
        assert_eq!(state[0], false);
        assert_eq!(state[1], false);
    }
}
