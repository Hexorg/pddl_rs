use std::{collections::HashMap, ops::Range, slice::Iter};

use enumset::EnumSet;
mod optimizations;

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

/// Compile and optimize parsed [`Domain`] and [`Problem`] structures into a compiled problem ready for using in search methods.
/// Load them from a file using [`parse_domain`] and [`parse_problem`] functions.
pub fn compile_problem<'src>(
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<CompiledProblem<'src>, Error<'src>> {
    validate_problem(domain, problem)?;
    let compiler = map_objects(domain, problem)?;
    let actions = create_concrete_actions(&compiler, domain)?;
    let init = compile_init(&compiler, &problem.init)?;
    let mut goal = Vec::with_capacity(32);

    compile_precondition(&compiler, &problem.goal, None, &mut goal)?;
    Ok(CompiledProblem {
        memory_size: compiler.predicate_memory_map.len(),
        actions,
        init,
        goal,
    })
}

fn validate_problem<'src>(
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<(), Error<'src>> {
    use ErrorKind::*;
    if problem.domain.1 != domain.name.1 {
        return Err(Error {
            input: None,
            kind: MissmatchedDomain(domain.name.1),
            chain: None,
            range: problem.domain.0.clone(),
        });
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

fn compile_init<'src>(
    compiler: &CompilerData<'src>,
    init: &[Init<'src>],
) -> Result<Vec<Instruction>, Error<'src>> {
    let mut instructions = Vec::with_capacity(32);
    for exp in init {
        match exp {
            Init::AtomicFormula(formula) => {
                instructions.push(Instruction::And(0));
                compile_name_negative_formula(compiler, formula, &mut instructions)?;
            }
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(instructions)
}

fn compile_term_atomic_formula<'src>(
    compiler: &CompilerData<'src>,
    af: &AtomicFormula<'src, Term<'src>>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
    is_effect: bool,
) -> Result<(), Error<'src>> {
    use ErrorKind::{ExpectedName, ExpectedVariable, UndeclaredVariable};
    use Term::*;
    match af {
        AtomicFormula::Predicate(name, params) => {
            let mut call_vec = Vec::with_capacity(params.len() + 1);
            call_vec.push(name.1);
            for param in params {
                match param {
                    Variable(var) => {
                        if args.is_none() {
                            return Err(Error {
                                input: None,
                                kind: ExpectedName,
                                chain: None,
                                range: param.range(),
                            });
                        }
                        let args = args.unwrap();
                        let mut is_found = false;
                        for arg in args {
                            if var.1 == arg.0 .1 {
                                call_vec.push(arg.1 .1);
                                is_found = true;
                                break;
                            }
                        }
                        if !is_found {
                            return Err(Error {
                                input: None,
                                kind: UndeclaredVariable,
                                chain: None,
                                range: var.0.clone(),
                            });
                        }
                    }
                    Name(name) => {
                        if args.is_some() {
                            return Err(Error {
                                input: None,
                                kind: ExpectedVariable,
                                chain: None,
                                range: param.range(),
                            });
                        }
                        call_vec.push(name.1);
                    }
                    Function(_) => todo!(),
                }
            }
            if let Some(offset) = compiler.predicate_memory_map.get(&call_vec) {
                instructions.push(if is_effect {
                    Instruction::SetState(*offset)
                } else {
                    Instruction::ReadState(*offset)
                })
            } else {
                panic!("All variables matched, and predicate exists, but can't find this call vec memory offset")
            }
            Ok(())
        }
        AtomicFormula::Equality(_, _) => todo!(),
    }
}

fn compile_name_atomic_formula<'src>(
    compiler: &CompilerData<'src>,
    af: &AtomicFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match af {
        AtomicFormula::Predicate(name, args) => {
            let mut call_vec = vec![name.1];
            call_vec.extend(args.iter().map(|a| a.1));
            if let Some(offset) = compiler.predicate_memory_map.get(&call_vec) {
                instructions.push(Instruction::SetState(*offset));
                Ok(())
            } else {
                // Check if predicate is defined, check of object is defined.
                todo!()
            }
        }
        AtomicFormula::Equality(_, _) => todo!(),
    }
}

fn compile_gd<'src>(
    compiler: &CompilerData<'src>,
    gd: &GD<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match gd {
        GD::AtomicFormula(af) => {
            compile_term_atomic_formula(compiler, af, args, instructions, false)
        }
        GD::And(vec) => {
            for gd in vec {
                compile_gd(compiler, gd, args, instructions)?
            }
            Ok(())
        }
        GD::Or(_) => todo!(),
        GD::Not(gd) => {
            compile_gd(compiler, gd, args, instructions)?;
            instructions.push(Instruction::Not);
            Ok(())
        }
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

fn compile_precondition<'src>(
    compiler: &CompilerData<'src>,
    precondition: &PreconditionExpr<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match precondition {
        PreconditionExpr::And(vec) => {
            for preconditions in vec {
                compile_precondition(compiler, preconditions, args, instructions)?
            }
            instructions.push(Instruction::And(vec.len()));
            Ok(())
        }
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => compile_gd(compiler, gd, args, instructions),
    }
}

fn compile_term_negative_formula<'src>(
    compiler: &CompilerData<'src>,
    formula: &NegativeFormula<'src, Term<'src>>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
    is_effect: bool,
) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => {
            compile_term_atomic_formula(compiler, af, args, instructions, is_effect)
        }
        NegativeFormula::Not(af) => {
            if is_effect {
                instructions.push(Instruction::Not);
            }
            compile_term_atomic_formula(compiler, af, args, instructions, is_effect)?;
            if !is_effect {
                instructions.push(Instruction::Not);
            }
            Ok(())
        }
    }
}

fn compile_name_negative_formula<'src>(
    compiler: &CompilerData<'src>,
    formula: &NegativeFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => compile_name_atomic_formula(compiler, af, instructions),
        NegativeFormula::Not(af) => {
            instructions.push(Instruction::Not);
            compile_name_atomic_formula(compiler, af, instructions)
        }
    }
}

fn compile_fexp<'src>(
    _: &CompilerData<'src>,
    fexp: &FluentExpression<'src>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
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
}
fn function_op<'src>(
    compiler: &CompilerData<'src>,
    function: &FunctionTerm<'src>,
    fexp: &FluentExpression<'src>,
    op: SupportedFunctionOp,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    compile_fexp(compiler, fexp, instructions)?;
    if function.terms.len() == 0
        && function.name.1 == "total-cost"
        && compiler.requirements.contains(Requirement::ActionCosts)
    {
        use SupportedFunctionOp::*;
        instructions.push(Instruction::ReadFunction(0)); // todo! map functions
        match op {
            INC => instructions.push(Instruction::Add),
        }
        instructions.push(Instruction::SetFunction(0));
        Ok(())
    } else {
        Err(Error {
            input: None,
            kind: ErrorKind::UnsetRequirement(Requirement::ActionCosts.into()),
            chain: None,
            range: function.range(),
        })
    }
}

fn compile_effect<'src>(
    compiler: &CompilerData<'src>,
    effect: &Effect<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match effect {
        Effect::And(vec) => {
            for effect in vec {
                compile_effect(compiler, effect, args, instructions)?
            }
            Ok(())
        }
        Effect::Forall(_) => todo!(),
        Effect::When(_) => todo!(),
        Effect::NegativeFormula(f) => {
            instructions.push(Instruction::And(0));
            compile_term_negative_formula(compiler, f, args, instructions, true)
        }
        Effect::Assign(_, _) => todo!(),
        Effect::AssignTerm(_, _) => todo!(),
        Effect::AssignUndefined(_) => todo!(),
        Effect::ScaleUp(_, _) => todo!(),
        Effect::ScaleDown(_, _) => todo!(),
        Effect::Increase(function, fexp) => function_op(
            compiler,
            function,
            &fexp.1,
            SupportedFunctionOp::INC,
            instructions,
        ),
        Effect::Decrease(_, _) => todo!(),
    }
}

fn compile_basic_action<'src>(
    compiler: &CompilerData<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    action: &BasicAction<'src>,
) -> Result<CompiledAction<'src>, Error<'src>> {
    let mut precondition = Vec::new();
    action
        .precondition
        .as_ref()
        .and_then(|p| Some(compile_precondition(compiler, p, args, &mut precondition)))
        .unwrap_or(Ok(()))?;
    let mut effect = Vec::new();
    action
        .effect
        .as_ref()
        .and_then(|e| Some(compile_effect(compiler, e, args, &mut effect)))
        .unwrap_or(Ok(()))?;
    let args: Vec<Name> = if let Some(args) = args {
        args.iter().map(|(_, o)| (**o).clone()).collect()
    } else {
        Vec::new()
    };
    Ok(CompiledAction {
        name: action.name.clone(),
        args,
        precondition,
        effect,
    })
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
fn create_concrete_actions<'src>(
    compiler: &CompilerData<'src>,
    domain: &Domain<'src>,
) -> Result<Vec<CompiledAction<'src>>, Error<'src>> {
    let mut all_actions =
        Vec::with_capacity(compiler.predicate_memory_map.len() * domain.actions.len() / 5);
    for action in &domain.actions {
        if let Action::Basic(action @ BasicAction { parameters, .. }) = action {
            // Create action for all type-object permutations.
            let actions = for_all_type_object_permutations(
                &compiler.type_to_objects_map,
                parameters.as_slice(),
                |args| compile_basic_action(compiler, Some(args), action),
            )?;
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
fn map_objects<'src>(
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<CompilerData<'src>, Error<'src>> {
    let requirements = domain.requirements | problem.requirements;
    let mut type_tree = HashMap::new();
    let mut type_src_pos = HashMap::new();
    // Iterate over types and build the type tree
    for List { items, kind } in &domain.types {
        if let Type::Exact(kind) = kind {
            for item in items {
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
    for List { items, kind } in &problem.objects {
        match kind {
            Type::Exact(kind) => {
                for item in items {
                    object_src_pos.insert(item.1, item.0.clone());
                    object_to_type_map.insert(item.1, kind.to_owned());
                    let mut type_name = kind.1;
                    while let Some(parent_type) = type_tree.get(type_name) {
                        if type_to_objects_map
                            .get_mut(type_name)
                            .and_then(|vec: &mut Vec<Name>| Some(vec.push(item.to_owned())))
                            .is_none()
                        {
                            type_to_objects_map.insert(type_name, vec![item.to_owned()]);
                        }
                        type_name = parent_type.1;
                    }
                    type_to_objects_map
                        .get_mut("object")
                        .and_then(|vec: &mut Vec<Name>| Some(vec.extend(items.iter().cloned())));
                }
            }
            Type::None => {
                object_src_pos.extend(items.iter().map(|i| (i.1, i.0.clone())));
                type_to_objects_map
                    .get_mut("object")
                    .and_then(|vec: &mut Vec<Name>| Some(vec.extend(items.iter().cloned())));
            }
            Type::Either(_) => todo!(),
        }
    }
    let mut predicate_memory_map = HashMap::new();
    //Iterate over predicates and its objects and build a memory map
    for AtomicFSkeleton { name, variables } in &domain.predicates {
        for_all_type_object_permutations(&type_to_objects_map, &variables, |args| {
            let mut call_vec = vec![name.1];
            call_vec.extend(args.iter().map(|i| i.1 .1));
            if !predicate_memory_map.contains_key(&call_vec) {
                predicate_memory_map.insert(call_vec, predicate_memory_map.len());
            }
            Ok(())
        })?;
    }
    Ok(CompilerData {
        requirements,
        type_tree,
        type_src_pos,
        object_to_type_map,
        type_to_objects_map,
        object_src_pos,
        predicate_memory_map,
    })
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
    fn test_mapping() {
        let (domain, problem) = get_tiny_domain();
        let compiler = map_objects(&domain, &problem).unwrap();
        assert_eq!(
            compiler.predicate_memory_map,
            HashMap::<Vec<&str>, usize>::from([
                (vec!["a", "a"], 0),
                (vec!["a", "b"], 1),
                (vec!["a", "c"], 2),
                (vec!["b", "a", "a"], 3),
                (vec!["b", "b", "a"], 4),
                (vec!["b", "c", "a"], 5),
                (vec!["b", "a", "b"], 6),
                (vec!["b", "b", "b"], 7),
                (vec!["b", "c", "b"], 8),
                (vec!["b", "a", "c"], 9),
                (vec!["b", "b", "c"], 10),
                (vec!["b", "c", "c"], 11),
            ])
        )
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
