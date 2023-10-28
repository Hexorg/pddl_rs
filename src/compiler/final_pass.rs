use crate::{Error, ErrorKind};

use super::{
    inertia::{Inertia, process_inertia},
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
        state_inertia: &'pass mut Vec<Inertia>,
        action_inertia: &'pass mut Vec<Inertia>
    },
    Precondition {
        variable_to_object: &'pass [(&'ast Name<'src>, &'ast Name<'src>)],
        compiled_action_idx: usize,
        instructions: Vec<Instruction>,
        state_inertia: &'pass mut Vec<Inertia>,
        action_inertia: &'pass mut Vec<Inertia>,
        is_positive: bool,
    },
    Effect {
        variable_to_object: &'pass [(&'ast Name<'src>, &'ast Name<'src>)],
        compiled_action_idx: usize,
        instructions: Vec<Instruction>,
        state_inertia: &'pass mut Vec<Inertia>,
        action_inertia: &'pass mut Vec<Inertia>,
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
    pub fn set_is_positive(&mut self, new_state:bool) {
        match self {
            Self::Effect { is_positive, .. } | Self::Precondition { is_positive, .. } => {
                *is_positive = new_state
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
    mut domain_data: DomainData<'src>,
    domain: &Domain<'src>,
    problem: &Problem<'src>,
    optimizations: EnumSet<Optimization>,
) -> Result<CompiledProblem<'src>, Error<'src>> {
    let (mut actions, state_inertia, action_inertia) = create_concrete_actions(&mut domain_data, domain)?;
    let init = visit_init(&domain_data, &problem.init)?;
    if optimizations.contains(Optimization::Inertia) {
        process_inertia(state_inertia, action_inertia, &init, &mut actions, &mut domain_data)?;
    }
    
    let mut goal_context = Context::Basic {
        instructions: Vec::with_capacity(32),
    };
    visit_precondition(&domain_data, &problem.goal, &mut goal_context)?;
    match goal_context {
        Context::Basic { instructions } => Ok(CompiledProblem {
            memory_size: domain_data.predicate_memory_map.len(),
            actions,
            init,
            goal: instructions,
            action_graph: domain_data.action_graph,
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
pub fn create_concrete_actions<'src>(
    pass_data: &mut DomainData<'src>,
    domain: &Domain<'src>,
) -> Result<(Vec<CompiledAction<'src>>, Vec<Inertia>, Vec<Inertia>), Error<'src>> {
    let mut all_actions =
        Vec::with_capacity(pass_data.predicate_memory_map.len() * domain.actions.len() / 5);

    // let mut state_inertia = Vec::new();
    let mut compiled_action_idx = 0;
    let mut state_inertia = vec![Inertia::new(); pass_data.predicate_memory_map.len()];
    let mut action_inertia = Vec::with_capacity(65535);
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
                        action_inertia: &mut action_inertia
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
    Ok((all_actions, state_inertia, action_inertia))
}

fn visit_basic_action<'src>(
    pass_data: &DomainData<'src>,
    action: &BasicAction<'src>,
    context: &mut Context<'src, '_, '_>,
    // args: Option<&[(&Name<'src>, &Name<'src>)]>,
    // domain_action_idx: usize,
    // compiled_action_count: usize,
    // state_inertia: &mut Vec<Inertia>,
) -> Result<CompiledAction<'src>, Error<'src>> {
    let (variable_to_object, args, compiled_action_idx, domain_action_idx, state_inertia, action_inertia) =
        match context {
            Context::Action {
                variable_to_object,
                domain_action_idx,
                compiled_action_idx,
                state_inertia,
                action_inertia
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
                    action_inertia
                )
            }
            _ => panic!("Unexpected state."),
        };
    let mut precondition_context = Context::Precondition {
        variable_to_object,
        instructions: Vec::new(),
        compiled_action_idx,
        state_inertia,
        action_inertia,
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
        action_inertia,
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
    // state_inertia: &mut Vec<Inertia>,
    // is_effect: bool,
) -> Result<(), Error<'src>> {
    use super::Term::*;
    use ErrorKind::UndeclaredVariable;
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
                        action_inertia,
                        compiled_action_idx,
                        is_positive,
                        ..
                    } => {
                        instructions.push(Instruction::SetState(*offset));
                        if *is_positive {
                            state_inertia[*offset]
                                .provides_positive
                                .insert(*compiled_action_idx);
                            if action_inertia.len() == *compiled_action_idx {
                                action_inertia.push(Inertia::new());
                            }
                            action_inertia.get_mut(*compiled_action_idx).unwrap().provides_positive.insert(*offset);
                            
                        } else {
                            state_inertia[*offset]
                                .provides_negative
                                .insert(*compiled_action_idx);
                            if action_inertia.len() == *compiled_action_idx {
                                action_inertia.push(Inertia::new())
                            }
                            action_inertia.get_mut(*compiled_action_idx).unwrap().provides_negative.insert(*offset);
                        }
                    }
                    Context::Precondition {
                        instructions,
                        state_inertia,
                        action_inertia,
                        compiled_action_idx,
                        is_positive,
                        ..
                    } => {
                        instructions.push(Instruction::ReadState(*offset));
                        if *is_positive {
                            state_inertia[*offset]
                                .wants_positive
                                .insert(*compiled_action_idx);
                            if action_inertia.len() == *compiled_action_idx {
                                action_inertia.push(Inertia::new())
                            } 
                            action_inertia.get_mut(*compiled_action_idx).unwrap().wants_positive.insert(*offset);
                        } else {
                            state_inertia[*offset]
                                .wants_negative
                                .insert(*compiled_action_idx);
                            if action_inertia.len() == *compiled_action_idx {
                                action_inertia.push(Inertia::new())
                            } 
                            action_inertia.get_mut(*compiled_action_idx).unwrap().wants_negative.insert(*offset);
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
            context.set_is_positive(false);
            visit_gd(pass_data, gd, context)?;
            context.set_is_positive(true);
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
    // state_inertia: &mut Vec<Inertia>,
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
    // state_inertia: &mut Vec<Inertia>,
    // is_effect: bool,
) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => visit_term_atomic_formula(pass_data, af, context),
        NegativeFormula::Not(af) => {
            context.set_is_positive(false);
            if context.is_effect() {
                // Effect sets state, so we need to invert stack value first, then set it
                context.instructions_mut().push(Instruction::Not);
                visit_term_atomic_formula(pass_data, af, context)?;
            } else {
                // Precondition reads state, so we need to read it first, then invert it on the stack
                visit_term_atomic_formula(pass_data, af, context)?;
                context.instructions_mut().push(Instruction::Not);
            }
            context.set_is_positive(true);
            Ok(())
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
    // state_inertia: &mut Vec<Inertia>,
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
    use crate::compiler::parse_domain;

    const DOMAIN_SRC: &str = "(define (domain inertia) 
    (:predicates (one ?a) (two ?a ?b))
    (:action a1 :parameters (?a ?b) :precondition (one ?a) :effect (and (not (one ?a)) (two ?a ?b)))
    (:action a2 :parameters (?a ?b) :precondition(not (two ?a ?b)) :effect (and (one ?a) (one ?b)))
    )";
    const PROBLEM_SRC: &str = "(define (problem inertia) (:domain inertia) (:objects one two three)
     (:init (one one) (one two) (two two three)) (:goal (one three)))";

    
}
