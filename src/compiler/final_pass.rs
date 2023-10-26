use std::ops::Range;

use crate::{Error, ErrorKind};

use super::{
    action_graph::{TryNode, TryNodeList},
    inertia::StateInertia,
    *,
};

enum Context<'src, 'ast, 'pass> {
    Basic {
        instructions: Vec<Instruction>,
    },
    Action {
        domain_action_idx: usize,
        compiled_action_idx: usize,
        variable_to_object: &'pass [(&'ast Name<'src>, &'ast Name<'src>)],
        state_inertia: &'pass mut Vec<StateInertia>,
    },
    Precondition {
        variable_to_object: &'pass [(&'ast Name<'src>, &'ast Name<'src>)],
        compiled_action_idx: usize,
        instructions: Vec<Instruction>,
        state_inertia: &'pass mut Vec<StateInertia>,
        is_positive: bool,
    },
    Effect {
        variable_to_object: &'pass [(&'ast Name<'src>, &'ast Name<'src>)],
        compiled_action_idx: usize,
        instructions: Vec<Instruction>,
        state_inertia: &'pass mut Vec<StateInertia>,
        is_positive: bool,
    },
}

impl<'src, 'ast, 'pass> Context<'src, 'ast, 'pass> {
    pub fn instructions(self) -> Vec<Instruction> {
        match self {
            Self::Basic { instructions } => instructions,
            Self::Precondition { instructions, .. } => instructions,
            Self::Effect { instructions, .. } => instructions,
            _ => panic!("Unexpected context"),
        }
    }
    pub fn state_inertia_mut(&mut self) -> &mut Vec<StateInertia> {
        match self {
            Context::Action { state_inertia, .. } => state_inertia,
            Context::Precondition { state_inertia, .. } => state_inertia,
            Context::Effect { state_inertia, .. } => state_inertia,
            _ => panic!("Unexpected context"),
        }
    }
    pub fn instructions_mut(&mut self) -> &mut Vec<Instruction> {
        match self {
            Self::Basic { instructions } => instructions,
            Self::Precondition { instructions, .. } => instructions,
            Self::Effect { instructions, .. } => instructions,
            _ => panic!("Unexpected context"),
        }
    }
    pub fn variable_to_object(&self) -> &'pass [(&'ast Name<'src>, &'ast Name<'src>)] {
        match self {
            Self::Precondition {
                variable_to_object, ..
            } => variable_to_object,
            Self::Effect {
                variable_to_object, ..
            } => variable_to_object,
            Self::Action {
                variable_to_object, ..
            } => variable_to_object,
            _ => panic!("Unexpected context"),
        }
    }
    pub fn is_effect(&self) -> bool {
        match self {
            Self::Effect { .. } => true,
            _ => false,
        }
    }
    pub fn set_negative(&mut self) {
        match self {
            Self::Effect { is_positive, .. } | Self::Precondition { is_positive, .. } => {
                *is_positive = false
            }
            _ => (),
        }
    }
    pub fn get_compiled_action_idx(&self) -> usize {
        match self {
            Self::Action {
                compiled_action_idx,
                ..
            } => *compiled_action_idx,
            Self::Effect {
                compiled_action_idx,
                ..
            } => *compiled_action_idx,
            Self::Precondition {
                compiled_action_idx,
                ..
            } => *compiled_action_idx,
            _ => panic!("Unexpected context"),
        }
    }
}

pub fn final_pass<'src>(
    mut pass_data: DomainData<'src>,
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<CompiledProblem<'src>, Error<'src>> {
    let (actions, state_inertia) = create_concrete_actions(&mut pass_data, domain)?;
    let init = visit_init(&pass_data, &problem.init)?;
    let mut goal_context = Context::Basic {
        instructions: Vec::with_capacity(32),
    };

    visit_precondition(&pass_data, &problem.goal, &mut goal_context)?;
    match goal_context {
        Context::Basic { instructions } => Ok(CompiledProblem {
            memory_size: pass_data.predicate_memory_map.len(),
            actions,
            init,
            goal: instructions,
            action_graph: pass_data.action_graph,
        }),
        _ => panic!("Context changed while compiling goals."),
    }
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
    pass_data: &mut DomainData<'src>,
    domain: &Domain<'src>,
) -> Result<(Vec<CompiledAction<'src>>, Vec<StateInertia>), Error<'src>> {
    let mut all_actions =
        Vec::with_capacity(pass_data.predicate_memory_map.len() * domain.actions.len() / 5);

    // let mut state_inertia = Vec::new();
    let mut compiled_action_idx = 0;
    let mut state_inertia = vec![StateInertia::new(); pass_data.predicate_memory_map.len()];
    for (domain_action_idx, action) in domain.actions.iter().enumerate() {
        if let Action::Basic(action @ BasicAction { parameters, .. }) = action {
            // Create action for all type-object permutations.
            let actions = for_all_type_object_permutations(
                &pass_data.type_to_objects_map,
                parameters.as_slice(),
                |args| {
                    let mut context = Context::Action {
                        variable_to_object: args,
                        domain_action_idx,
                        compiled_action_idx,
                        state_inertia: &mut state_inertia,
                    };
                    let result = visit_basic_action(pass_data, action, &mut context);
                    compiled_action_idx = context.get_compiled_action_idx();
                    result
                },
            )?;
            all_actions.extend(actions)
        } else {
            todo!()
        }
    }
    Ok((all_actions, state_inertia))
}

fn visit_basic_action<'src>(
    pass_data: &DomainData<'src>,
    action: &BasicAction<'src>,
    context: &mut Context<'src, '_, '_>,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // domain_action_idx: usize,
    // compiled_action_count: usize,
    // state_inertia: &mut Vec<StateInertia>,
) -> Result<CompiledAction<'src>, Error<'src>> {
    let (variable_to_object, args, compiled_action_idx, domain_action_idx, state_inertia) =
        match context {
            Context::Action {
                variable_to_object,
                domain_action_idx,
                compiled_action_idx,
                state_inertia,
            } => {
                let args = variable_to_object
                    .iter()
                    .map(|(_, o)| (**o).clone())
                    .collect();
                let domain_action_idx = *domain_action_idx;
                let compiled_action_idx2 = *compiled_action_idx;
                *compiled_action_idx += 1;
                (
                    variable_to_object,
                    args,
                    compiled_action_idx2,
                    domain_action_idx,
                    state_inertia,
                )
            }
            _ => panic!("Unexpected state."),
        };
    let mut precondition_context = Context::Precondition {
        variable_to_object,
        instructions: Vec::new(),
        compiled_action_idx,
        state_inertia,
        is_positive: true,
    };
    action
        .precondition
        .as_ref()
        .and_then(|precondition| {
            Some(visit_precondition(
                pass_data,
                precondition,
                &mut precondition_context,
            ))
        })
        .unwrap_or(Ok(()))?;
    let precondition = precondition_context.instructions();
    let mut effect_context = Context::Effect {
        variable_to_object,
        instructions: Vec::new(),
        compiled_action_idx,
        state_inertia,
        is_positive: true,
    };
    action
        .effect
        .as_ref()
        .and_then(|effect| Some(visit_effect(pass_data, effect, &mut effect_context)))
        .unwrap_or(Ok(()))?;
    let effect = effect_context.instructions();
    Ok(CompiledAction {
        domain_action_idx,
        args,
        precondition,
        effect,
    })
}

fn visit_init<'src>(
    pass_data: &DomainData<'src>,
    init: &[Init<'src>],
) -> Result<Vec<Instruction>, Error<'src>> {
    let mut instructions = Vec::with_capacity(32);
    for exp in init {
        match exp {
            Init::AtomicFormula(formula) => {
                instructions.push(Instruction::And(0));
                visit_name_negative_formula(pass_data, formula, &mut instructions)?;
            }
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(instructions)
}

fn visit_term_atomic_formula<'src>(
    pass_data: &DomainData<'src>,
    af: &AtomicFormula<'src, Term<'src>>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<StateInertia>,
    // is_effect: bool,
) -> Result<(), Error<'src>> {
    use super::Term::*;
    use ErrorKind::{ExpectedName, ExpectedVariable, UndeclaredVariable};
    match af {
        AtomicFormula::Predicate(name, params) => {
            let mut call_vec = Vec::with_capacity(params.len() + 1);
            call_vec.push(name.1);
            for param in params {
                match param {
                    Variable(var) => {
                        let mut is_found = false;
                        for arg in context.variable_to_object() {
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
                        call_vec.push(name.1);
                    }
                    Function(_) => todo!(),
                }
            }
            if let Some(offset) = pass_data.predicate_memory_map.get(&call_vec) {
                match context {
                    Context::Effect {
                        instructions,
                        state_inertia,
                        compiled_action_idx,
                        is_positive,
                        ..
                    } => {
                        instructions.push(Instruction::SetState(*offset));
                        if *is_positive {
                            state_inertia[*offset]
                                .provides_positive
                                .push(*compiled_action_idx);
                        } else {
                            state_inertia[*offset]
                                .provides_negative
                                .push(*compiled_action_idx);
                        }
                    }
                    Context::Precondition {
                        instructions,
                        state_inertia,
                        compiled_action_idx,
                        is_positive,
                        ..
                    } => {
                        instructions.push(Instruction::ReadState(*offset));
                        if *is_positive {
                            state_inertia[*offset]
                                .wants_positive
                                .push(*compiled_action_idx);
                        } else {
                            state_inertia[*offset]
                                .wants_negative
                                .push(*compiled_action_idx);
                        }
                    }
                    Context::Basic { instructions } => {
                        instructions.push(Instruction::ReadState(*offset))
                    }
                    _ => panic!("Unexpected Context"),
                }
            } else {
                panic!("All variables matched, and predicate exists, but can't find this call vec memory offset")
            }
            Ok(())
        }
        AtomicFormula::Equality(_, _) => todo!(),
    }
}

/// Visited by problem but not domain
fn visit_name_atomic_formula<'src>(
    pass_data: &DomainData<'src>,
    af: &AtomicFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match af {
        AtomicFormula::Predicate(name, args) => {
            let mut call_vec = vec![name.1];
            call_vec.extend(args.iter().map(|a| a.1));
            if let Some(offset) = pass_data.predicate_memory_map.get(&call_vec) {
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

fn visit_gd<'src>(
    pass_data: &DomainData<'src>,
    gd: &GD<'src>,
    context: &mut Context,
) -> Result<(), Error<'src>> {
    match gd {
        GD::AtomicFormula(af) => visit_term_atomic_formula(pass_data, af, context),
        GD::And(vec) => {
            for gd in vec {
                visit_gd(pass_data, gd, context)?
            }
            Ok(())
        }
        GD::Or(_) => todo!(),
        GD::Not(gd) => {
            context.set_negative();
            visit_gd(pass_data, gd, context)?;
            context.instructions_mut().push(Instruction::Not);
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

fn visit_precondition<'src>(
    pass_data: &DomainData<'src>,
    precondition: &PreconditionExpr<'src>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<StateInertia>,
) -> Result<(), Error<'src>> {
    match precondition {
        PreconditionExpr::And(vec) => {
            for precondition in vec {
                visit_precondition(pass_data, precondition, context)?
            }
            context.instructions_mut().push(Instruction::And(vec.len()));
            Ok(())
        }
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => visit_gd(pass_data, gd, context),
    }
}

fn visit_term_negative_formula<'src>(
    pass_data: &DomainData<'src>,
    formula: &NegativeFormula<'src, Term<'src>>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<StateInertia>,
    // is_effect: bool,
) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => visit_term_atomic_formula(pass_data, af, context),
        NegativeFormula::Not(af) => {
            context.set_negative();
            if context.is_effect() {
                // Effect sets state, so we need to invert stack value first, then set it
                context.instructions_mut().push(Instruction::Not);
                visit_term_atomic_formula(pass_data, af, context)
            } else {
                // Precondition reads state, so we need to read it first, then invert it on the stack
                visit_term_atomic_formula(pass_data, af, context)?;
                context.instructions_mut().push(Instruction::Not);
                Ok(())
            }
        }
    }
}

fn visit_name_negative_formula<'src>(
    pass_data: &DomainData<'src>,
    formula: &NegativeFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => visit_name_atomic_formula(pass_data, af, instructions),
        NegativeFormula::Not(af) => {
            instructions.push(Instruction::Not);
            visit_name_atomic_formula(pass_data, af, instructions)
        }
    }
}

fn visit_fexp<'src>(
    fexp: &FluentExpression<'src>,
    context: &mut Context,
) -> Result<(), Error<'src>> {
    match fexp {
        FluentExpression::Number(n) => context.instructions_mut().push(Instruction::Push(*n)),
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
    pass_data: &DomainData<'src>,
    function: &FunctionTerm<'src>,
    context: &mut Context,
) -> Result<(), Error<'src>> {
    if function.terms.len() == 0
        && function.name.1 == "total-cost"
        && pass_data.requirements.contains(Requirement::ActionCosts)
    {
        context
            .instructions_mut()
            .push(Instruction::ReadFunction(0)); // todo! map functions
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

fn set_function<'src>(
    pass_data: &DomainData<'src>,
    function: &FunctionTerm<'src>,
    context: &mut Context,
) -> Result<(), Error<'src>> {
    if function.terms.len() == 0
        && function.name.1 == "total-cost"
        && pass_data.requirements.contains(Requirement::ActionCosts)
    {
        context.instructions_mut().push(Instruction::SetFunction(0)); // todo! map functions
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

fn visit_effect<'src>(
    pass_data: &DomainData<'src>,
    effect: &Effect<'src>,
    context: &mut Context,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // compiled_action_count: usize,
    // instructions: &mut Vec<Instruction>,
    // state_inertia: &mut Vec<StateInertia>,
) -> Result<(), Error<'src>> {
    match effect {
        Effect::And(vec) => {
            for effect in vec {
                visit_effect(pass_data, effect, context)?
            }
            Ok(())
        }
        Effect::Forall(_) => todo!(),
        Effect::When(_) => todo!(),
        Effect::NegativeFormula(formula) => {
            context.instructions_mut().push(Instruction::And(0));
            visit_term_negative_formula(pass_data, formula, context)
        }
        Effect::Assign(_, _) => todo!(),
        Effect::AssignTerm(_, _) => todo!(),
        Effect::AssignUndefined(_) => todo!(),
        Effect::ScaleUp(_, _) => todo!(),
        Effect::ScaleDown(_, _) => todo!(),
        Effect::Increase(function, fexp) => {
            visit_fexp(&fexp.1, context)?;
            read_function(pass_data, function, context)?;
            context.instructions_mut().push(Instruction::Push(1));
            context.instructions_mut().push(Instruction::Add);
            set_function(pass_data, function, context)
        }
        Effect::Decrease(_, _) => todo!(),
    }
}

#[cfg(test)]
mod test {
    use enumset::EnumSet;

    use super::*;
    use crate::compiler::{action_graph::TryNode, parse_domain};

    const DOMAIN_SRC: &str = "(define (domain inertia) 
    (:predicates (one ?a) (two ?a ?b))
    (:action a1 :parameters (?a ?b) :precondition (one ?a) :effect (and (not (one ?a)) (two ?a ?b)))
    (:action a2 :parameters (?a ?b) :precondition(not (two ?a ?b)) :effect (and (one ?a) (one ?b)))
    )";
    const PROBLEM_SRC: &str = "(define (problem inertia) (:domain inertia) (:objects one two three)
     (:init (one one) (one two) (two two three)) (:goal (one three)))";

    #[test]
    fn test_compiled_action_graph() {
        let domain = parse_domain(DOMAIN_SRC).unwrap();
        let problem = parse_problem(PROBLEM_SRC, EnumSet::EMPTY).unwrap();
        let mut preprocess = preprocess(&domain, &problem).unwrap();
        let (actions, state_inertia) = create_concrete_actions(&mut preprocess, &domain).unwrap();
        use Instruction::*;
        let one = (54..57, "one");
        let two = (58..61, "two");
        let three = (62..67, "three");
        assert_eq!(
            actions[0],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![one.clone(), one.clone()],
                precondition: vec![ReadState(0)],
                effect: vec![And(0), Not, SetState(0), And(0), SetState(3)]
            }
        );
        assert_eq!(
            actions[1],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![two.clone(), one.clone()],
                precondition: vec![ReadState(1)],
                effect: vec![And(0), Not, SetState(1), And(0), SetState(4)]
            }
        );
        assert_eq!(
            actions[2],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![three.clone(), one.clone()],
                precondition: vec![ReadState(2)],
                effect: vec![And(0), Not, SetState(2), And(0), SetState(5)]
            }
        );
        assert_eq!(
            actions[3],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![one.clone(), two.clone()],
                precondition: vec![ReadState(0)],
                effect: vec![And(0), Not, SetState(0), And(0), SetState(6)]
            }
        );
        assert_eq!(
            actions[4],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![two.clone(), two.clone()],
                precondition: vec![ReadState(1)],
                effect: vec![And(0), Not, SetState(1), And(0), SetState(7)]
            }
        );
        assert_eq!(
            actions[5],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![three.clone(), two.clone()],
                precondition: vec![ReadState(2)],
                effect: vec![And(0), Not, SetState(2), And(0), SetState(8)]
            }
        );
        assert_eq!(
            actions[6],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![one.clone(), three.clone()],
                precondition: vec![ReadState(0)],
                effect: vec![And(0), Not, SetState(0), And(0), SetState(9)]
            }
        );
        assert_eq!(
            actions[7],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![two.clone(), three.clone()],
                precondition: vec![ReadState(1)],
                effect: vec![And(0), Not, SetState(1), And(0), SetState(10)]
            }
        );
        assert_eq!(
            actions[8],
            CompiledAction {
                domain_action_idx: 0,
                args: vec![three.clone(), three.clone()],
                precondition: vec![ReadState(2)],
                effect: vec![And(0), Not, SetState(2), And(0), SetState(11)]
            }
        );
        assert_eq!(
            actions[9],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![one.clone(), one.clone()],
                precondition: vec![ReadState(3), Not],
                effect: vec![And(0), SetState(0), And(0), SetState(0)]
            }
        );
        assert_eq!(
            actions[10],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![two.clone(), one.clone()],
                precondition: vec![ReadState(4), Not],
                effect: vec![And(0), SetState(1), And(0), SetState(0)]
            }
        );
        assert_eq!(
            actions[11],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![three.clone(), one.clone()],
                precondition: vec![ReadState(5), Not],
                effect: vec![And(0), SetState(2), And(0), SetState(0)]
            }
        );
        assert_eq!(
            actions[12],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![one.clone(), two.clone()],
                precondition: vec![ReadState(6), Not],
                effect: vec![And(0), SetState(0), And(0), SetState(1)]
            }
        );
        assert_eq!(
            actions[13],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![two.clone(), two.clone()],
                precondition: vec![ReadState(7), Not],
                effect: vec![And(0), SetState(1), And(0), SetState(1)]
            }
        );
        assert_eq!(
            actions[14],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![three.clone(), two.clone()],
                precondition: vec![ReadState(8), Not],
                effect: vec![And(0), SetState(2), And(0), SetState(1)]
            }
        );
        assert_eq!(
            actions[15],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![one.clone(), three.clone()],
                precondition: vec![ReadState(9), Not],
                effect: vec![And(0), SetState(0), And(0), SetState(2)]
            }
        );
        assert_eq!(
            actions[16],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![two.clone(), three.clone()],
                precondition: vec![ReadState(10), Not],
                effect: vec![And(0), SetState(1), And(0), SetState(2)]
            }
        );
        assert_eq!(
            actions[17],
            CompiledAction {
                domain_action_idx: 1,
                args: vec![three.clone(), three.clone()],
                precondition: vec![ReadState(11), Not],
                effect: vec![And(0), SetState(2), And(0), SetState(2)]
            }
        );
        assert_eq!(actions.len(), 18);
        use TryNode::*;
        // assert_eq!(action_graph[0], Vec::new());
        // assert_eq!(action_graph[1], Vec::new());
        // assert_eq!(action_graph[2], Vec::new());
        // assert_eq!(action_graph[3], Vec::new());
        // assert_eq!(action_graph[4], Vec::new());
        // assert_eq!(action_graph[5], Vec::new());
        // assert_eq!(action_graph[6], Vec::new());
        // assert_eq!(action_graph[7], Vec::new());
        // assert_eq!(action_graph[8], Vec::new());
        // assert_eq!(action_graph[9], vec![Action(0), Action(3), Action(6), PreemptionPoint]);
        // assert_eq!(action_graph[10], vec![Action(0), Action(1), Action(3), Action(6), Action(7), PreemptionPoint]);
        // assert_eq!(action_graph[11], vec![Action(0), Action(2), Action(3), Action(5), Action(6), Action(8), PreemptionPoint]);
        // assert_eq!(action_graph[12], vec![Action(3), PreemptionPoint]);
        // assert_eq!(action_graph[13], vec![Action(4), PreemptionPoint]);
        // assert_eq!(action_graph[14], vec![Action(5), PreemptionPoint]);
        // assert_eq!(action_graph[15], vec![Action(6), PreemptionPoint]);
        // assert_eq!(action_graph[16], vec![Action(7), PreemptionPoint]);
        // assert_eq!(action_graph[17], vec![Action(8), PreemptionPoint]);
        // assert_eq!(action_graph.len(), 18);
    }
}
