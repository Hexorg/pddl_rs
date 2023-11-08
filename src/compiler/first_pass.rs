use std::collections::HashSet;

use crate::{Error, ErrorKind};

use super::{
    domain_data::{map_objects, validate_problem, DomainData},
    AtomicFSkeleton, AtomicFormula, BasicAction, Domain, Effect, List, Name, NegativeFormula,
    PreconditionExpr, Problem, Term, Type, GD,
};

struct Context<'ast, 'src> {
    pub is_negative: bool,
    pub parameters: &'ast Vec<List<'src>>,
    pub negative: HashSet<AtomicFormula<'src, Type<'src>>>,
    pub positive: HashSet<AtomicFormula<'src, Type<'src>>>,
}

impl<'ast, 'src> Context<'ast, 'src> {
    pub fn new(parameters: &'ast Vec<List<'src>>) -> Self {
        Self {
            is_negative: false,
            parameters,
            negative: HashSet::new(),
            positive: HashSet::new(),
        }
    }
}

pub fn first_pass<'src>(
    domain: &Domain<'src>,
    problem: &'src Problem<'src>,
) -> Result<DomainData<'src>, Error> {
    validate_problem(domain, problem)?;
    let mut unread_predicates: HashSet<Name<'src>> =
        HashSet::with_capacity(domain.predicates.len());
    let mut unset_predicates: HashSet<Name<'src>> = HashSet::with_capacity(domain.predicates.len());
    for AtomicFSkeleton { name, .. } in &domain.predicates {
        unread_predicates.insert(*name);
        unset_predicates.insert(*name);
    }
    for (_idx, action) in domain.actions.iter().enumerate() {
        match action {
            super::Action::Basic(ba) => {
                visit_basic_action(ba, &mut unread_predicates, &mut unset_predicates)
            }
            super::Action::Durative(_) => todo!(),
            super::Action::Derived(_, _) => todo!(),
        }
    }
    let mut last_error = None;
    for unread in unread_predicates {
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
        map_objects(domain, problem, unset_predicates)
    }
}

fn visit_basic_action<'src>(
    action: &BasicAction<'src>,
    unread: &mut HashSet<Name<'src>>,
    unset: &mut HashSet<Name<'src>>,
) {
    if let Some(effect) = &action.effect {
        let mut context = Context::new(&action.parameters);
        visit_effect(effect, &mut context);
        for predicate in context.positive.union(&context.negative) {
            match predicate {
                AtomicFormula::Predicate(name, _) => unset.remove(name),
                AtomicFormula::Equality(_, _) => todo!(),
            };
        }
    }
    if let Some(precondition) = &action.precondition {
        let mut context = Context::new(&action.parameters);
        visit_precondition(precondition, &mut context);
        for predicate in context.positive.union(&context.negative) {
            match predicate {
                AtomicFormula::Predicate(name, ..) => unread.remove(name),
                AtomicFormula::Equality(_, _) => todo!(),
            };
        }
    }
}

fn visit_effect<'ast, 'src>(effect: &Effect<'src>, context: &mut Context<'ast, 'src>) {
    match effect {
        super::Effect::And(vec) => vec.iter().for_each(|effect| visit_effect(effect, context)),
        super::Effect::Forall(_) => todo!(),
        super::Effect::When(_) => todo!(),
        super::Effect::NegativeFormula(formula) => visit_negative_formula(formula, context),
        super::Effect::Assign(_, _) => todo!(),
        super::Effect::AssignTerm(_, _) => todo!(),
        super::Effect::AssignUndefined(_) => todo!(),
        super::Effect::ScaleUp(_, _) => todo!(),
        super::Effect::ScaleDown(_, _) => todo!(),
        super::Effect::Increase(_, _) => (),
        super::Effect::Decrease(_, _) => todo!(),
    }
}

fn visit_negative_formula<'ast, 'src>(
    formula: &NegativeFormula<'src, Term<'src>>,
    context: &mut Context<'ast, 'src>,
) {
    match formula {
        NegativeFormula::Direct(formula) => visit_term_formula(formula, context),
        NegativeFormula::Not(formula) => visit_term_formula(formula, context),
    }
}

fn visit_term_formula<'ast, 'src>(
    formula: &AtomicFormula<'src, Term<'src>>,
    context: &mut Context<'ast, 'src>,
) {
    let type_formula = formula.generalized_to_type(context.parameters);
    if context.is_negative {
        context.negative.insert(type_formula);
    } else {
        context.positive.insert(type_formula);
    }
}

fn visit_precondition<'ast, 'src>(
    precondition: &PreconditionExpr<'src>,
    context: &mut Context<'ast, 'src>,
) {
    match precondition {
        PreconditionExpr::And(vec) => vec
            .iter()
            .for_each(|precondition| visit_precondition(precondition, context)),
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => visit_gd(gd, context),
    }
}

fn visit_gd<'ast, 'src>(gd: &GD<'src>, context: &mut Context<'ast, 'src>) {
    match gd {
        GD::AtomicFormula(formula) => visit_term_formula(formula, context),
        GD::And(vec) => vec.iter().for_each(|gd| visit_gd(gd, context)),
        GD::Or(_) => todo!(),
        GD::Not(gd) => visit_gd(gd, context),
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

    use crate::{
        compiler::{
            parse_domain, parse_problem,
            tests::{TINY_DOMAIN_SRC, TINY_PROBLEM_SRC, TINY_SOURCES},
        },
        ReportPrinter,
    };

    use super::first_pass;

    #[test]
    fn test_unset_predicates() {
        let domain = parse_domain(TINY_DOMAIN_SRC).unwrap_or_print_report(&TINY_SOURCES);
        let problem = parse_problem(TINY_PROBLEM_SRC, domain.requirements)
            .unwrap_or_print_report(&TINY_SOURCES);
        let data = first_pass(&domain, &problem).unwrap_or_print_report(&TINY_SOURCES);
        assert_eq!(data.const_false_predicates.len(), 0);
        assert_eq!(data.const_true_predicates.len(), 1);
    }
}
