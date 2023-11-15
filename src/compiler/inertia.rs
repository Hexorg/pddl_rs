use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
};

use super::{AtomicFormula, List, Name, PredicateUsize, Problem, Term, Type};

/// Following the Koehler, Jana, and Jörg Hoffmann. "On the Instantiation of ADL Operators Involving Arbitrary First-Order Formulas." PuK. 2000. [paper](https://www.researchgate.net/profile/Jana-Koehler-2/publication/220916196_On_the_Instantiation_of_ADL_Operators_Involving_Arbitrary_First-Order_Formulas/links/53f5c12c0cf2fceacc6f65e0/On-the-Instantiation-of-ADL-Operators-Involving-Arbitrary-First-Order-Formulas.pdf),
/// Inertia allows us to start pruning unused states, actions, and instatiate basic action-graphs allowing us to skip many dead-end states.
#[derive(PartialEq, Eq, Clone)]
pub struct Inertia<'src, O>
where
    O: Eq + PartialEq + std::hash::Hash,
{
    pub wants_negative: HashSet<AtomicFormula<'src, O>>,
    pub wants_positive: HashSet<AtomicFormula<'src, O>>,
    pub provides_negative: HashSet<AtomicFormula<'src, O>>,
    pub provides_positive: HashSet<AtomicFormula<'src, O>>,
    pub parameters: Option<Vec<List<'src>>>,
}

impl<'src, O> Debug for Inertia<'src, O>
where
    O: Eq + PartialEq + std::hash::Hash + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.wants_negative.len() > 0 {
            f.write_fmt(format_args!(
                "\tWants negative: {}\n",
                self.wants_negative
                    .iter()
                    .map(|f| format!("{:?}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        if self.wants_positive.len() > 0 {
            f.write_fmt(format_args!(
                "\tWants positive: {}\n",
                self.wants_positive
                    .iter()
                    .map(|f| format!("{:?}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        if self.provides_negative.len() > 0 {
            f.write_fmt(format_args!(
                "\tProvides negative: {}\n",
                self.provides_negative
                    .iter()
                    .map(|f| format!("{:?}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        if self.provides_positive.len() > 0 {
            f.write_fmt(format_args!(
                "\tProvides positive: {}\n",
                self.provides_positive
                    .iter()
                    .map(|f| format!("{:?}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        Ok(())
    }
}

impl<'src, O> Inertia<'src, O>
where
    O: Eq + PartialEq + std::hash::Hash,
{
    pub fn new(parameters: Option<Vec<List<'src>>>) -> Self {
        Self {
            wants_negative: HashSet::new(),
            wants_positive: HashSet::new(),
            provides_negative: HashSet::new(),
            provides_positive: HashSet::new(),
            parameters,
        }
    }
}

impl<'src, O> Display for Inertia<'src, O>
where
    O: Display + Eq + PartialEq + std::hash::Hash,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.wants_negative.len() > 0 {
            f.write_fmt(format_args!(
                "\tWants negative: {}\n",
                self.wants_negative
                    .iter()
                    .map(|f| format!("{}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        if self.wants_positive.len() > 0 {
            f.write_fmt(format_args!(
                "\tWants positive: {}\n",
                self.wants_positive
                    .iter()
                    .map(|f| format!("{}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        if self.provides_negative.len() > 0 {
            f.write_fmt(format_args!(
                "\tProvides negative: {}\n",
                self.provides_negative
                    .iter()
                    .map(|f| format!("{}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        if self.provides_positive.len() > 0 {
            f.write_fmt(format_args!(
                "\tProvides positive: {}\n",
                self.provides_positive
                    .iter()
                    .map(|f| format!("{}", f))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))?;
        }
        Ok(())
    }
}

impl<'src> Inertia<'src, Term<'src>> {
    pub fn concrete(
        &self,
        problem: &Problem<'src>,
        args: &[(Name<'src>, (PredicateUsize, PredicateUsize))],
    ) -> Inertia<'src, Name<'src>> {
        let wants_positive = self
            .wants_positive
            .iter()
            .map(|f| f.concrete(&problem.objects, args))
            .collect();
        let wants_negative = self
            .wants_negative
            .iter()
            .map(|f| f.concrete(&problem.objects, args))
            .collect();
        let provides_positive = self
            .provides_positive
            .iter()
            .map(|f| f.concrete(&problem.objects, args))
            .collect();
        let provides_negative = self
            .provides_negative
            .iter()
            .map(|f| f.concrete(&problem.objects, args))
            .collect();
        Inertia {
            wants_negative,
            wants_positive,
            provides_negative,
            provides_positive,
            parameters: None,
        }
    }
}

pub trait DomainInertia {
    /// Check if action `from` enables any predicate that action `to` requires
    fn is_enables(&self, from: usize, to: usize) -> bool;
    /// Check if action `from` disables any predicate that action `to` requires
    fn is_disables(&self, from: usize, to: usize) -> bool;
}

impl<'src, O> DomainInertia for Vec<Inertia<'src, O>>
where
    O: Eq + PartialEq + std::hash::Hash,
{
    fn is_enables(&self, from: usize, to: usize) -> bool {
        self[from]
            .provides_positive
            .intersection(&self[to].wants_positive)
            .count()
            > 0
            || self[from]
                .provides_negative
                .intersection(&self[to].wants_negative)
                .count()
                > 0
    }
    fn is_disables(&self, from: usize, to: usize) -> bool {
        self[from]
            .provides_positive
            .intersection(&self[to].wants_negative)
            .count()
            > 0
            || self[from]
                .provides_negative
                .intersection(&self[to].wants_positive)
                .count()
                > 0
    }
}

pub trait VariableInertia<'src> {
    fn minimal_concrete(&self) -> Vec<Inertia<'src, (PredicateUsize, PredicateUsize)>>;
}

impl<'src> VariableInertia<'src> for Vec<Inertia<'src, Term<'src>>> {
    fn minimal_concrete(&self) -> Vec<Inertia<'src, (PredicateUsize, PredicateUsize)>> {
        let mut objects: HashMap<Type<'src>, Vec<(PredicateUsize, PredicateUsize)>> =
            HashMap::with_capacity(self.len());
        let mut concrete_inertia: Vec<Inertia<'src, (PredicateUsize, PredicateUsize)>> =
            Vec::with_capacity(self.len());
        for inertia in self {
            let mut used_objects: HashSet<(PredicateUsize, PredicateUsize)> = HashSet::new();
            let args: Vec<(Name, (PredicateUsize, PredicateUsize))> =
                inertia.parameters.as_ref().unwrap().iter().fold(
                    Vec::new(),
                    |mut acc, List { items, kind }| {
                        for param in items {
                            acc.push((
                                *param,
                                if objects.contains_key(kind) {
                                    if let Some(object) = objects
                                        .get(kind)
                                        .unwrap()
                                        .iter()
                                        .find(|o| !used_objects.contains(*o))
                                    {
                                        used_objects.insert(*object);
                                        *object
                                    } else {
                                        let vec = objects.get_mut(kind).unwrap();
                                        let kind_id = vec.last().unwrap().0;
                                        let new_object = (kind_id, vec.len() as PredicateUsize);
                                        vec.push(new_object);
                                        new_object
                                    }
                                } else {
                                    let new_object = (objects.len() as PredicateUsize, 0);
                                    objects.insert(kind.clone(), vec![new_object]);
                                    used_objects.insert(new_object);
                                    new_object
                                },
                            ));
                        }
                        acc
                    },
                );
            let wants_positive = inertia
                .wants_positive
                .iter()
                .map(|f| f.fake_concrete(args.as_slice()))
                .collect();
            let wants_negative = inertia
                .wants_negative
                .iter()
                .map(|f| f.fake_concrete(args.as_slice()))
                .collect();
            let provides_positive = inertia
                .provides_positive
                .iter()
                .map(|f| f.fake_concrete(args.as_slice()))
                .collect();
            let provides_negative = inertia
                .provides_negative
                .iter()
                .map(|f| f.fake_concrete(args.as_slice()))
                .collect();
            concrete_inertia.push(Inertia {
                wants_negative,
                wants_positive,
                provides_negative,
                provides_positive,
                parameters: None,
            });
        }
        concrete_inertia
    }
}

#[cfg(test)]
mod test {}
