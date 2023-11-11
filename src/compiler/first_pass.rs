use std::collections::{HashSet, HashMap};

use crate::{Error, ErrorKind};

use super::{
    domain_data::{map_objects, validate_problem, DomainData},
    AtomicFSkeleton, AtomicFormula, BasicAction, Domain, Effect, List, Name, NegativeFormula,
    PreconditionExpr, Problem, Term, Type, GD, inertia::Inertia, StateUsize, CompiledActionUsize, for_all_type_object_permutations, Init,
};

/// Compiler context that gets passed to all AST visitors to keep track of
/// inter-node state as we are traversing the Abstract Systax Tree
#[derive(PartialEq, Eq)]
enum ContextKind {
    Precondition,
    Effect,
}

/// Gets passed to all AST visitors to keep track of inter-node state as we are
/// traversing the Abstract Systax Tree
struct Context<'src, 'pass> {
    pub problem:&'pass Problem<'src>,
    pub kind: ContextKind,
    pub is_negative: bool,
    pub action_id: CompiledActionUsize,
    pub predicate_memory_map: HashMap<AtomicFormula<'src, Name<'src>>, StateUsize>,
    pub unset_predicates:HashSet<Name<'src>>,
    pub unread_predicates:HashSet<Name<'src>>,
    pub action_inertia: Vec<Inertia<StateUsize>>,
    pub state_inertia: Vec<Inertia<CompiledActionUsize>>,
}

impl<'src, 'pass> Context<'src, 'pass> {
    pub fn new(problem: &'pass Problem<'src>) -> Self {
        Self { problem,
            kind:ContextKind::Precondition,
            is_negative:false, 
            action_id: 0,
            predicate_memory_map:HashMap::new(), 
            unset_predicates: HashSet::new(),
            unread_predicates: HashSet::new(),
            action_inertia:Vec::new(), 
            state_inertia:Vec::new() }
    }
}

/// First pass over the Abstract Syntax Tree - performs basic sanity checks,
/// And populates structures needed for optimization of the [`CompiledProblem`]
/// emitted in the [`final_pass`]
pub fn first_pass<'src, 'ast>(
    domain: &'ast Domain<'src>,
    problem: &'ast Problem<'src>,
    domain_data: &mut DomainData<'src>,
) -> Result<(), Error> where 'ast:'src {
    let mut context = Context::new(problem);

    for AtomicFSkeleton { name, .. } in &domain.predicates {
        context.unread_predicates.insert(*name);
        context.unset_predicates.insert(*name);
    }

    visit_init(&problem.init, &mut context)?;
    visit_all_actions(domain, &domain_data, &mut context)?;
    visit_precondition(&problem.goal, None, &mut context)?;
    
    let mut last_error = None;
    for unread in context.unread_predicates {
        let error = Error {
            span: unread.0,
            kind: ErrorKind::UnreadPredicate,
            chain: last_error.and_then(|e| Some(Box::new(e))),
        };
        last_error = Some(error);
    }
    if let Some(e) = last_error {
        Err(e)
    } else {
        Ok(())
    }
}

fn visit_init(
    init:&[Init],
    context: &mut Context
) -> Result<(), Error> {
    for init in init {
        match init {
            Init::AtomicFormula(formula) => visit_negative_name_formula(formula, context)?,
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(())
}

fn visit_all_actions(
    domain:&Domain, 
    domain_data:&DomainData, 
    context:&mut Context
) -> Result<(), Error> {
    let mut action_id = 0;
    for action in &domain.actions {
        match action {
            super::Action::Basic(ba) => {
                for_all_type_object_permutations(&domain_data.type_to_objects_map, &ba.parameters, |args| {
                    visit_basic_action(ba, args, context)
                });
            },
            super::Action::Durative(_) => todo!(),
            super::Action::Derived(_, _) => todo!(),
        }
        
    }
    Ok(())
}

fn visit_basic_action(
    action: &BasicAction,
    args: &[(Name, (u16, u16))],
    context: &mut Context
) -> Result<Option<bool>, Error> {
    if let Some(precondition) = &action.precondition {
        context.kind = ContextKind::Precondition;
        visit_precondition(precondition, Some(args), context)?;
    }

    if let Some(effect) = &action.effect {
        context.kind = ContextKind::Effect;
        visit_effect(effect, args, context)?;
    }
    Ok(None)
}

fn visit_effect(
    effect: &Effect, 
    args: &[(Name, (u16, u16))],
    context: &mut Context
) -> Result<(), Error> {
    match effect {
        super::Effect::And(vec) => { for effect in vec { visit_effect(effect, args, context)? } Ok(()) },
        super::Effect::Forall(_) => todo!(),
        super::Effect::When(_) => todo!(),
        super::Effect::NegativeFormula(formula) => visit_negative_term_formula(formula, args, context),
        super::Effect::Assign(_, _) => todo!(),
        super::Effect::AssignTerm(_, _) => todo!(),
        super::Effect::AssignUndefined(_) => todo!(),
        super::Effect::ScaleUp(_, _) => todo!(),
        super::Effect::ScaleDown(_, _) => todo!(),
        super::Effect::Increase(_, _) => Ok(()),
        super::Effect::Decrease(_, _) => todo!(),
    }
}

fn visit_negative_term_formula(
    formula: &NegativeFormula<Term>,
    args: &[(Name, (u16, u16))],
    context: &mut Context,
) -> Result<(), Error> {
    match formula {
        NegativeFormula::Direct(formula) => visit_term_formula(formula, Some(args), context),
        NegativeFormula::Not(formula) => { 
            let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            let r = visit_term_formula(formula, Some(args), context);
            context.is_negative = is_negative;
            r
        },
    }
}

fn visit_negative_name_formula(
    formula: &NegativeFormula<Name>,
    context: &mut Context,
) -> Result<(), Error> {
    match formula {
        NegativeFormula::Direct(formula) => visit_name_formula(formula, context),
        NegativeFormula::Not(formula) => { let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            let r = visit_name_formula(formula, context);
            context.is_negative = is_negative;
            r
        },
    }
}

fn visit_term_formula(
    formula: &AtomicFormula<Term>,
    args: Option<&[(Name, (u16, u16))]>,
    context: &mut Context,
) -> Result<(), Error> {
    let formula = match formula.try_into() {
        Ok(v) => v,
        Err(e) => if let Some(args) = args { 
            formula.concrete(context.problem, args) 
        } else { 
            return Err(e); 
        }
    };


    // match context.kind {
    //     ContextKind::Precondition => todo!(),
    //     ContextKind::Effect => todo!(),
    // }

    Ok(())
}

fn visit_name_formula(
    formula: &AtomicFormula<Name>,
    context: &mut Context,
) -> Result<(), Error> {
    Ok(())
}

fn visit_precondition(
    precondition: &PreconditionExpr,
    args: Option<&[(Name, (u16, u16))]>,
    context: &mut Context,
) -> Result<(), Error> {
    match precondition {
        PreconditionExpr::And(vec) => { for precondition in vec { visit_precondition(precondition, args, context)? } Ok(()) },
            
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => visit_gd(gd, args, context),
    }
}

fn visit_gd(
    gd: &GD, 
    args: Option<&[(Name, (u16, u16))]>,
    context: &mut Context
) -> Result<(), Error> {
    match gd {
        GD::AtomicFormula(formula) => visit_term_formula(formula, args, context),
        GD::And(vec) => { for gd in vec { visit_gd(gd, args, context)? } Ok(())},
        GD::Or(_) => todo!(),
        GD::Not(gd) => {
            let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            let r = visit_gd(gd, args, context);
            context.is_negative = is_negative;
            r
        },
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

#[cfg(test)]
mod tests {

}
