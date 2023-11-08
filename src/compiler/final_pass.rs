use crate::{Error, ErrorKind};

use super::{inertia::Inertia, *};

#[derive(PartialEq, Eq)]
enum ContextKind {
    Goal,
    Action(ASTActionUsize),
    Precondition,
    Effect,
}

struct Context<'src, 'ast, 'pass> {
    pub kind: ContextKind,
    pub instructions: Vec<Instruction>,
    pub problem: &'ast Problem<'src>,
    pub is_negative: bool,
    pub skipped_instructions: PredicateUsize,
    pub variable_to_object:
        Option<&'pass [(&'ast Name<'src>, &'ast (PredicateUsize, PredicateUsize))]>,
    pub inertia: &'pass mut Inertia<StateUsize>,
}

impl<'src, 'ast, 'pass> Context<'src, 'ast, 'pass> {
    pub fn new(
        kind: ContextKind,
        problem: &'ast Problem<'src>,
        variable_to_object: Option<
            &'pass [(&'ast Name<'src>, &'ast (PredicateUsize, PredicateUsize))],
        >,
        inertia: &'pass mut Inertia<StateUsize>,
    ) -> Self {
        Self {
            kind,
            inertia,
            problem,
            is_negative: false,
            skipped_instructions: 0,
            instructions: Vec::new(),
            variable_to_object,
        }
    }
    pub fn goal(
        instruction_capacity: usize,
        problem: &'ast Problem<'src>,
        inertia: &'pass mut Inertia<StateUsize>,
    ) -> Self {
        Self {
            kind: ContextKind::Goal,
            inertia,
            problem,
            is_negative: false,
            skipped_instructions: 0,
            instructions: Vec::with_capacity(instruction_capacity),
            variable_to_object: None,
        }
    }
}

pub fn final_pass<'src>(
    mut domain_data: DomainData<'src>,
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<CompiledProblem, Error> {
    let (actions, action_inertia) = create_concrete_actions(&mut domain_data, domain, problem)?;

    let mut action_graph = ActionGraph::new();
    action_graph.set_size(actions.len());
    action_graph.apply_inertia(&action_inertia);
    let init = visit_init(&domain_data, &problem.init)?;
    let mut problem_inertia = Inertia::new();
    let mut goal_context = Context::goal(32, problem, &mut problem_inertia);
    visit_precondition(&domain_data, &problem.goal, &mut goal_context)?;
    Ok(CompiledProblem {
        memory_size: domain_data.predicate_memory_map.len() as StateUsize,
        constants_size: domain_data.constant_predicates.len() as StateUsize,
        actions,
        init,
        goal: goal_context.instructions,
        action_graph,
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
pub fn create_concrete_actions<'src>(
    domain_data: &mut DomainData<'src>,
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<(Vec<CompiledAction>, Vec<Inertia<StateUsize>>), Error> {
    let mut all_actions =
        Vec::with_capacity(domain_data.predicate_memory_map.len() * domain.actions.len() / 5);
    let mut all_inertia: Vec<Inertia<StateUsize>> = Vec::new();
    // let mut state_inertia = Vec::new();
    for (domain_action_idx, action) in domain.actions.iter().enumerate() {
        let mut compiled_action_range = all_actions.len()..all_actions.len();
        if let Action::Basic(action @ BasicAction { parameters, .. }) = action {
            // Create action for all type-object permutations.
            let actions = for_all_type_object_permutations(
                &domain_data.type_to_objects_map,
                parameters.as_slice(),
                |args| {
                    all_inertia.push(Inertia::new());
                    let inertia = all_inertia.last_mut().unwrap();
                    let mut context = Context::new(
                        ContextKind::Action(domain_action_idx as ASTActionUsize),
                        problem,
                        Some(args),
                        inertia,
                    );
                    if let Some(a) = visit_basic_action(domain_data, action, &mut context)? {
                        Ok(Some(a))
                    } else {
                        all_inertia.pop();
                        Ok(None)
                    }
                },
            )?;
            compiled_action_range.end += actions.len();
            domain_data
                .compiled_action_ranges
                .push(compiled_action_range);
            all_actions.extend(actions)
        } else {
            todo!()
        }
    }
    Ok((all_actions, all_inertia))
}

fn visit_basic_action<'src>(
    domain_data: &DomainData<'src>,
    action: &BasicAction<'src>,
    context: &mut Context<'src, '_, '_>,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // domain_action_idx: usize,
    // compiled_action_count: usize,
    // state_inertia: &mut Vec<Inertia>,
) -> Result<Option<CompiledAction>, Error> {
    let (args, domain_action_idx) = match context.kind {
        ContextKind::Action(domain_action_idx) => {
            let args = context
                .variable_to_object
                .unwrap()
                .iter()
                .map(|(_, o)| (**o).clone())
                .collect();
            (args, domain_action_idx)
        }
        _ => panic!("Unexpected state."),
    };
    let mut precondition_context = Context::new(
        ContextKind::Precondition,
        context.problem,
        context.variable_to_object,
        context.inertia,
    );
    let is_used = action
        .precondition
        .as_ref()
        .and_then(|precondition| {
            Some(visit_precondition(
                domain_data,
                precondition,
                &mut precondition_context,
            ))
        })
        .unwrap_or(Ok(true))?;
    if !is_used {
        return Ok(None);
    }
    let precondition = precondition_context.instructions;
    let mut effect_context = Context::new(
        ContextKind::Effect,
        context.problem,
        context.variable_to_object,
        context.inertia,
    );
    let is_used = action
        .effect
        .as_ref()
        .and_then(|effect| Some(visit_effect(domain_data, effect, &mut effect_context)))
        .unwrap_or(Ok(true))?;
    if !is_used {
        return Ok(None);
    }
    Ok(Some(CompiledAction {
        domain_action_idx,
        args,
        precondition,
        effect: effect_context.instructions,
        // try_next: Vec::with_capacity(domain_data.action_graph.priority.len() * 10),
    }))
}

fn visit_init<'src>(
    domain_data: &DomainData<'src>,
    init: &[Init<'src>],
) -> Result<Vec<Instruction>, Error> {
    let mut instructions = Vec::with_capacity(32);
    for exp in init {
        match exp {
            Init::AtomicFormula(formula) => {
                visit_name_negative_formula(domain_data, formula, &mut instructions)?;
            }
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(instructions)
}

fn visit_term_atomic_formula<'src>(
    domain_data: &DomainData<'src>,
    af: &AtomicFormula<'src, Term<'src>>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<Inertia>,
    // is_effect: bool,
) -> Result<bool, Error> {
    let call_vec = if context.kind == ContextKind::Goal {
        // Goal formulas use objects already anyway
        af.try_into()?
    } else {
        // All other formulas use variable terms which need to be mapped to objects.
        af.concrete(context.problem, context.variable_to_object.unwrap())
    };
    if let Some(offset) = domain_data.predicate_memory_map.get(&call_vec) {
        match context.kind {
            ContextKind::Effect => {
                context.instructions.push(Instruction::SetState(*offset));
                if context.is_negative {
                    context.inertia.provides_negative.insert(*offset);
                } else {
                    context.inertia.provides_positive.insert(*offset);
                }
            }
            ContextKind::Precondition | ContextKind::Goal => {
                context.instructions.push(Instruction::ReadState(*offset));
                if context.is_negative {
                    context.inertia.wants_negative.insert(*offset);
                } else {
                    context.inertia.wants_positive.insert(*offset);
                }
            }
            _ => panic!("Unexpected Context"),
        }
    } else {
        if context.kind == ContextKind::Effect {
            panic!("Unmapped predicate location in effect.")
        }
        if domain_data.const_true_predicates.contains(&call_vec) {
            // this instruction is always going to put true on the stack
            if context.is_negative {
                // this action is never posible
                return Ok(false);
            }
            // noop
            context.skipped_instructions += 1;
        } else if domain_data.const_false_predicates.contains(&call_vec) {
            // this instruction is always going to put false on the stack
            if !context.is_negative {
                // this action is never possible
                return Ok(false);
            }
            if let Some(Instruction::Not) = context.instructions.pop() {
                // noop
                context.skipped_instructions += 1;
            } else {
                panic!("Negative constant predicate is read not immediately after NOT")
            }
        } else if let AtomicFormula::Predicate(name, _) = &call_vec {
            if domain_data.constant_predicates.contains(name) {
                // This predicate is a constant set by the problem and this variable combination is not
                // set by the problem -> this action is impossible.
                return Ok(false);
            }
        } else {
            panic!("All variables matched, and predicate exists, but can't find this call vec memory offset")
        }
    }
    Ok(true)
}

/// Visited by problem but not domain
fn visit_name_atomic_formula<'src>(
    domain_data: &DomainData<'src>,
    af: &AtomicFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error> {
    if let Some(offset) = domain_data.predicate_memory_map.get(af) {
        instructions.push(Instruction::SetState(*offset));
        Ok(())
    } else {
        // Check if predicate is defined, check of object is defined.
        if domain_data.const_true_predicates.contains(af)
            || domain_data.const_false_predicates.contains(af)
        {
            // no op
            Ok(())
        } else {
            panic!("Non-memory mapped, non-constant atomic formula.")
        }
    }
}

fn visit_gd<'src>(
    domain_data: &DomainData<'src>,
    gd: &GD<'src>,
    context: &mut Context,
) -> Result<bool, Error> {
    match gd {
        GD::AtomicFormula(af) => visit_term_atomic_formula(domain_data, af, context),
        GD::And(vec) => {
            for gd in vec {
                let is_negative = context.is_negative;
                if !visit_gd(domain_data, gd, context)? {
                    return Ok(false);
                }
                context.is_negative = is_negative;
            }
            Ok(true)
        }
        GD::Or(_) => todo!(),
        GD::Not(gd) => {
            let r = visit_gd(domain_data, gd, context)?;
            context.is_negative = true;
            context.instructions.push(Instruction::Not);
            Ok(r)
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

fn visit_precondition<'src>(
    domain_data: &DomainData<'src>,
    precondition: &PreconditionExpr<'src>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<Inertia>,
) -> Result<bool, Error> {
    match precondition {
        PreconditionExpr::And(vec) => {
            context.skipped_instructions = 0;
            for precondition in vec {
                let is_negative = context.is_negative;
                if !visit_precondition(domain_data, precondition, context)? {
                    return Ok(false);
                }
                context.is_negative = is_negative;
            }
            let and_size = vec.len() as PredicateUsize - context.skipped_instructions;
            if and_size > 1 {
                context.instructions.push(Instruction::And(and_size));
            }
            Ok(true)
        }
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => visit_gd(domain_data, gd, context),
    }
}

fn visit_term_negative_formula<'src>(
    domain_data: &DomainData<'src>,
    formula: &NegativeFormula<'src, Term<'src>>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<Inertia>,
    // is_effect: bool,
) -> Result<bool, Error> {
    match formula {
        NegativeFormula::Direct(af) => visit_term_atomic_formula(domain_data, af, context),
        NegativeFormula::Not(af) => {
            match context.kind {
                ContextKind::Effect => {
                    // Effect sets state, so we need to invert stack value first, then set it
                    context.instructions.push(Instruction::Not);
                    context.is_negative = true;
                    visit_term_atomic_formula(domain_data, af, context)
                }
                ContextKind::Goal | ContextKind::Precondition => {
                    // Precondition and goal reads state, so we need to read it first, then invert it on the stack
                    let r = visit_term_atomic_formula(domain_data, af, context);
                    context.is_negative = true;
                    context.instructions.push(Instruction::Not);
                    r
                }
                _ => panic!("Unexpected context"),
            }
        }
    }
}

fn visit_name_negative_formula<'src>(
    domain_data: &DomainData<'src>,
    formula: &NegativeFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error> {
    match formula {
        NegativeFormula::Direct(af) => visit_name_atomic_formula(domain_data, af, instructions),
        NegativeFormula::Not(af) => {
            instructions.push(Instruction::Not);
            visit_name_atomic_formula(domain_data, af, instructions)
        }
    }
}

fn visit_fexp<'src>(fexp: &FluentExpression<'src>, context: &mut Context) -> Result<(), Error> {
    match fexp {
        FluentExpression::Number(n) => context.instructions.push(Instruction::Push(*n)),
        FluentExpression::Subtract(_) => todo!(),
        FluentExpression::Negate(_) => todo!(),
        FluentExpression::Divide(_) => todo!(),
        FluentExpression::Add(_) => todo!(),
        FluentExpression::Multiply(_) => todo!(),
        FluentExpression::Function(_) => todo!(),
    }
    Ok(())
}

fn read_function<'src>(
    domain_data: &DomainData<'src>,
    function: &FunctionTerm<'src>,
    context: &mut Context,
) -> Result<(), Error> {
    if function.terms.len() == 0
        && function.name.1 == "total-cost"
        && domain_data.requirements.contains(Requirement::ActionCosts)
    {
        context.instructions.push(Instruction::ReadFunction(0)); // todo! map functions
        Ok(())
    } else {
        Err(Error {
            // input: None,
            kind: ErrorKind::UnsetRequirement(Requirement::ActionCosts.into()),
            chain: None,
            span: function.span(),
        })
    }
}

fn set_function<'src>(
    domain_data: &DomainData<'src>,
    function: &FunctionTerm<'src>,
    context: &mut Context,
) -> Result<(), Error> {
    if function.terms.len() == 0
        && function.name.1 == "total-cost"
        && domain_data.requirements.contains(Requirement::ActionCosts)
    {
        context.instructions.push(Instruction::SetFunction(0)); // todo! map functions
        Ok(())
    } else {
        Err(Error {
            // input: None,
            kind: ErrorKind::UnsetRequirement(Requirement::ActionCosts.into()),
            chain: None,
            span: function.span(),
        })
    }
}

fn visit_effect<'src>(
    domain_data: &DomainData<'src>,
    effect: &Effect<'src>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<Inertia>,
) -> Result<bool, Error> {
    match effect {
        Effect::And(vec) => {
            for effect in vec {
                let is_negative = context.is_negative;
                if !visit_effect(domain_data, effect, context)? {
                    return Ok(false);
                }
                context.is_negative = is_negative;
            }
            Ok(true)
        }
        Effect::Forall(_) => todo!(),
        Effect::When(_) => todo!(),
        Effect::NegativeFormula(formula) => {
            visit_term_negative_formula(domain_data, formula, context)
        }
        Effect::Assign(_, _) => todo!(),
        Effect::AssignTerm(_, _) => todo!(),
        Effect::AssignUndefined(_) => todo!(),
        Effect::ScaleUp(_, _) => todo!(),
        Effect::ScaleDown(_, _) => todo!(),
        Effect::Increase(function, fexp) => {
            visit_fexp(&fexp.1, context)?;
            read_function(domain_data, function, context)?;
            context.instructions.push(Instruction::Push(1));
            context.instructions.push(Instruction::Add);
            set_function(domain_data, function, context)?;
            Ok(true)
        }
        Effect::Decrease(_, _) => todo!(),
    }
}
