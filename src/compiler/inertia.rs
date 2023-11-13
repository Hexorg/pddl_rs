
use std::{collections::{HashSet, HashMap}, hash::Hash, fmt::Display};

use super::{AtomicFormula, Term, PredicateUsize, Problem, Name, CompiledAction, Domain, BasicAction, List, maps::Maps};

/// Following the Koehler, Jana, and Jörg Hoffmann. "On the Instantiation of ADL Operators Involving Arbitrary First-Order Formulas." PuK. 2000. [paper](https://www.researchgate.net/profile/Jana-Koehler-2/publication/220916196_On_the_Instantiation_of_ADL_Operators_Involving_Arbitrary_First-Order_Formulas/links/53f5c12c0cf2fceacc6f65e0/On-the-Instantiation-of-ADL-Operators-Involving-Arbitrary-First-Order-Formulas.pdf),
/// Inertia allows us to start pruning unused states, actions, and instatiate basic action-graphs allowing us to skip many dead-end states.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Inertia<O>
where
    O: Eq + PartialEq + std::hash::Hash,
{
    pub wants_negative: HashSet<O>,
    pub wants_positive: HashSet<O>,
    pub provides_negative: HashSet<O>,
    pub provides_positive: HashSet<O>,
}
impl<O> Inertia<O>
where
    O: Eq + PartialEq + std::hash::Hash,
{
    pub fn new() -> Self {
        Self {
            wants_negative: HashSet::new(),
            wants_positive: HashSet::new(),
            provides_negative: HashSet::new(),
            provides_positive: HashSet::new(),
        }
    }
}


impl<O> Display for Inertia<O> where O:Display+Eq+PartialEq+std::hash::Hash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.wants_negative.len() > 0 {
            f.write_fmt(format_args!("\tWants negative: {}\n", self.wants_negative.iter().map(|f| format!("{}", f)).collect::<Vec<_>>().join(", ")))?;
        }
        if self.wants_positive.len() > 0 {
            f.write_fmt(format_args!("\tWants positive: {}\n", self.wants_positive.iter().map(|f| format!("{}", f)).collect::<Vec<_>>().join(", ")))?;
        }
        if self.provides_negative.len() > 0 {
            f.write_fmt(format_args!("\tProvides negative: {}\n", self.provides_negative.iter().map(|f| format!("{}", f)).collect::<Vec<_>>().join(", ")))?;
        }
        if self.provides_positive.len() > 0 {
            f.write_fmt(format_args!("\tProvides positive: {}\n", self.provides_positive.iter().map(|f| format!("{}", f)).collect::<Vec<_>>().join(", ")))?;
        }
        Ok(())
    }
}

impl<'src> Inertia<AtomicFormula<'src, Term<'src>>> {
    pub fn concrete(&self, problem:&Problem<'src>, args:&[(Name<'src>, (PredicateUsize, PredicateUsize))]) -> Inertia<AtomicFormula<'src, Name<'src>>>{
        let wants_positive = self.wants_positive.iter().map(|f| f.concrete(problem, args)).collect();
        let wants_negative = self.wants_negative.iter().map(|f| f.concrete(problem, args)).collect();
        let provides_positive = self.provides_positive.iter().map(|f| f.concrete(problem, args)).collect();
        let provides_negative = self.provides_negative.iter().map(|f| f.concrete(problem, args)).collect();
        Inertia { wants_negative, wants_positive, provides_negative, provides_positive }
    }
}

pub trait DomainInertia {
    /// Check if action `from` enables any predicate that action `to` requires
    fn is_enables(&self, from: usize, to: usize) -> bool;
    /// Check if action `from` disables any predicate that action `to` requires
    fn is_disables(&self, from: usize, to: usize) -> bool;
}

impl<'src, O> DomainInertia for Vec<Inertia<O>>
where O:Eq+PartialEq+std::hash::Hash{
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

#[cfg(test)]
mod test {

    
}
