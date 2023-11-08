use std::{collections::HashSet, hash::Hash};

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

pub trait DomainInertia {
    fn is_enables(&self, from: usize, to: usize) -> bool;
    fn is_disables(&self, from: usize, to: usize) -> bool;
}

impl<O> DomainInertia for Vec<Inertia<O>>
where
    O: Eq + Hash,
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

#[cfg(test)]
mod test {

    use crate::{
        compiler::{final_pass::final_pass, first_pass::first_pass, parse_domain, parse_problem},
        lib_tests::load_repo_pddl,
        ReportPrinter, Requirement,
    };

    #[test]
    fn test_inertia() {
        let domain_filename = "sample_problems/simple_domain.pddl";
        let problem_filename = "sample_problems/simple_problem.pddl";
        let sources = load_repo_pddl(domain_filename, problem_filename);
        let domain = parse_domain(&sources.domain_src).unwrap_or_print_report(&sources);
        let problem = parse_problem(&sources.problem_src, Requirement::Typing.into())
            .unwrap_or_print_report(&sources);
        let data = first_pass(&domain, &problem).unwrap_or_print_report(&sources);
        let c_problem = final_pass(data, &domain, &problem).unwrap_or_print_report(&sources);
        println!(
            "Compiled problem uses {} bits of memory and has {} actions.",
            c_problem.memory_size,
            c_problem.actions.len()
        );
    }
}
