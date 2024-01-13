
use std::{
    collections::{HashSet, HashMap},
    hash::Hash, fmt::Debug, 
};


use crate::{ Error, parser::ast::{list::{TypedList, List}, term::Term}};

use super::{AtomicFormula, PredicateUsize, maps::Maps, domain::{CompiledAtomicFormula, ArgKind}, permutate};




// #[derive(Clone)]
/// Inertia of one expression - of a predicate, an effect, problem init, or problem goal
/// Note that for predicate and effect the formulas use action parameter index as their argument
/// while for problem init and goal the formulas use problem object index as their argument
pub struct ExpressionInertia {
    pub negative: Vec<CompiledAtomicFormula>,
    pub positive: Vec<CompiledAtomicFormula>
}

impl ExpressionInertia {
    pub fn new() -> Self {
        Self { negative: Vec::new(), positive: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.negative.len() + self.positive.len()
    }

    pub fn insert(&mut self, is_negative:bool, formula:CompiledAtomicFormula) {
        let vec = if is_negative { &mut self.negative } else { &mut self.positive };
        if let Err(idx) = vec.binary_search(&formula) {
            vec.insert(idx, formula)
        }
    }

    pub fn decompile(&self, maps:&Maps, action_parameters:Option<&[PredicateUsize]>, arg_kind:ArgKind) -> String {
        let positive = self.positive.iter().map(|f| f.decompile(maps, action_parameters, arg_kind)).collect::<Vec<_>>().join(" & ");
        let negative = self.negative.iter().map(|f| format!("!{}", f.decompile(maps, action_parameters, arg_kind))).collect::<Vec<_>>().join(" & ");
        if positive.len() == 0 {
            negative
        } else if negative.len() == 0 {
            positive
        } else {
            format!("{} & {}", positive, negative)
        }
    }

    pub fn intersect(&self, other:&Self, assignment:&[Option<PredicateUsize>]) -> (usize, usize) {
        let from_to_map = assignment.iter().enumerate().filter_map(|(idx, f)| if let Some(f) = f { Some((*f, idx as PredicateUsize))} else { None }).collect::<HashMap<_, _>>();
        let mut same_matches = 0;
        let mut opposite_matches = 0;
        for f in &self.positive {
            let other_args = f.args.iter().filter_map(|idx| from_to_map.get(idx)).copied().collect::<Vec<_>>();
            if other_args.len() == f.args.len() {
                let other_f = CompiledAtomicFormula{predicate_idx:f.predicate_idx, args:other_args};
                if other.positive.binary_search(&other_f).is_ok() {
                    same_matches += 1;
                } else if other.negative.binary_search(&other_f).is_ok() {
                    opposite_matches += 1;
                }
            }
        }
        for f in &self.negative {
            let other_args = f.args.iter().filter_map(|idx| from_to_map.get(idx)).copied().collect::<Vec<_>>();
            if other_args.len() == f.args.len() {
                let other_f = CompiledAtomicFormula{predicate_idx:f.predicate_idx, args:other_args};
                if other.negative.binary_search(&other_f).is_ok() {
                    same_matches += 1;
                } else if other.positive.binary_search(&other_f).is_ok() {
                    opposite_matches += 1;
                }
            }
        }
        (same_matches, opposite_matches)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Relationship {
    Enables,
    Unrelated,
    Disables
}


pub struct ActionInertia {
    /// list of type id per arg
    pub args: Vec<PredicateUsize>,
    /// Action precondition, `ExpressionInertia` is stored with `ArgType::ParameterIndex`
    pub precondition: ExpressionInertia,
    /// Action effect, `ExpressionInertia` is stored with `ArgType::ParameterIndex`
    pub effect:ExpressionInertia,
}

impl ActionInertia {
    pub fn new(parameters:&TypedList, maps:&Maps) -> Self {
        let mut args = Vec::new();
        for List{items, kind} in parameters {
            let kind = kind.to_id(maps);
            for _ in 0..items.len() {
                args.push(kind);
            }
        }
        Self{args, precondition:ExpressionInertia::new(), effect:ExpressionInertia::new()}
    }

    fn type_counts(&self) -> HashMap<PredicateUsize, PredicateUsize> {
        let mut type_counts = HashMap::new();
        for arg_type in self.args.iter() {
            if let Some(count) = type_counts.get_mut(arg_type) {
                *count += 1;
            } else {
                type_counts.insert(*arg_type, 1);
            }
        }
        type_counts
    }

    /// Given to lists of arguments, generate a Vec of all possible assignments
    /// And Assignment is a Vec of the same length as other.args where a None means no match, 
    /// and Some(idx) gives a self.args[idx] for assignment.
    pub fn arg_intersect(&self, other:&Self, maps:&Maps) -> Vec<Vec<Option<PredicateUsize>>> {
        // println!("arg_intersect({:?}, {:?})", self.args, other.args);
        let self_types = self.type_counts();
        let mut other_map: HashMap<usize, usize> = HashMap::new();
        for (idx, arg_type) in other.args.iter().enumerate() {
            if self_types.contains_key(arg_type) {
                let arg_pos = other_map.len();
                other_map.insert(arg_pos, idx);
            }
        }
        permutate(other_map.len(), 
            |_| self.args.iter().copied().enumerate(), 
            |args| {let v = args.iter().enumerate().map(|(i, (idx, arg))| if maps.is_subtype(*arg, other.args[*other_map.get(&i).unwrap()]) { Some(*idx as PredicateUsize) } else { None }).collect::<Vec<_>>();
                if v.iter().any(|f| f.is_some()) {
                    let mut result = vec![None; other.args.len()];
                    for i in 0..other_map.len() {
                        result[*other_map.get(&i).unwrap()] = v[i];
                    }
                    Ok(Some(result))
                } else {
                    Ok(None)
                }
            }
        ).unwrap()
    }

    pub fn classify(&self, other:&Self, assignment:&[Option<PredicateUsize>]) -> Relationship {
        let (positive, negative) = self.effect.intersect(&other.precondition, assignment);
        if negative > 0 {
            Relationship::Disables
        } else if positive > 0 {
            Relationship::Enables
        } else {
            Relationship::Unrelated
        }

    }


    pub fn insert(&mut self, is_effect:bool, is_negative:bool, maps:&Maps, parameters:&TypedList, formula:&AtomicFormula<Term>) -> Result<(), Error> {
        let f = CompiledAtomicFormula::compile(maps, parameters, formula)?;
        if is_effect { self.effect.insert(is_negative, f)} else { self.precondition.insert(is_negative, f)}
        Ok(())
    }

}


/// Following the Koehler, Jana, and Jörg Hoffmann. "On the Instantiation of ADL Operators Involving Arbitrary First-Order Formulas." PuK. 2000. [paper](https://www.researchgate.net/profile/Jana-Koehler-2/publication/220916196_On_the_Instantiation_of_ADL_Operators_Involving_Arbitrary_First-Order_Formulas/links/53f5c12c0cf2fceacc6f65e0/On-the-Instantiation-of-ADL-Operators-Involving-Arbitrary-First-Order-Formulas.pdf),
/// Inertia allows us to start pruning unused states, actions, and instatiate basic action-graphs allowing us to skip many dead-end states.
pub struct Inertia
{
    /// List of all domain actions
    pub actions: Vec<ActionInertia>,
    /// Action preconditions, `ExpressionInertia` is stored with `ArgType::Object`
    pub problem_init: ExpressionInertia,
    /// Action preconditions, `ExpressionInertia` is stored with `ArgType::Object`
    pub problem_goal: ExpressionInertia,
}



impl Inertia
{
    pub fn new() -> Self {
        Self { actions: Vec::new(), problem_init:ExpressionInertia::new(), problem_goal:ExpressionInertia::new()}
    }

    /// Roughly compares two actions - if there is at least one assignment that 
    /// enables `to` - returns `Relationship::Enables`
    /// If there's at least one assignment that returns `Relationhip:Disables` and nothing
    /// else that enables - returns `Relationship::Disables`
    /// returns `Relationship::Unrelated` if all possible assignments result in unrelated relationships
    pub fn cmp(&self, from:usize, to:usize, maps:&Maps) -> Relationship {
        let mut rel = Relationship::Unrelated;
        for assignment in self.actions[from].arg_intersect(&self.actions[to], maps) {
            match self.actions[from].classify(&self.actions[to], assignment.as_slice()) {
                Relationship::Disables => if rel == Relationship::Unrelated {
                    rel = Relationship::Disables;
                }
                Relationship::Enables => rel = Relationship::Enables,
                Relationship::Unrelated => (),
            }
        }
        rel
    }


}


#[cfg(test)]
mod test {

    use crate::{lib_tests::load_repo_pddl, compiler::{passes::Compiler, ASTActionUsize, inertia::Relationship}, ReportPrinter, parser::ast::list::TypedList};

    use super::{ActionInertia, ExpressionInertia};

    #[test]
    fn test_arg_intersect() {
        let sources = load_repo_pddl(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
        );
        // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let compiler = Compiler::new(&domain, &problem, sources.domain_path.clone(), sources.problem_path.clone());
        let c_problem = compiler.compile().unwrap_or_print_report(&sources);
        let vec = c_problem.inertia.actions[0].arg_intersect(&c_problem.inertia.actions[2], &c_problem.maps);
        assert_eq!(vec.len(), 2);
        assert_eq!(vec[0], vec![None, None, None, Some(0), None]);
        assert_eq!(vec[1], vec![None, None, Some(0), None, None]);
    }

    #[test]
    fn experiment()  {
        let sources = load_repo_pddl(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
        );
        // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let compiler = Compiler::new(&domain, &problem, sources.domain_path.clone(), sources.problem_path.clone());
        let c_problem = compiler.compile().unwrap_or_print_report(&sources);
        for action_idx in 0..domain.actions.len() {
            // println!("{}\n\tWants:\n\t\t{:?}\n\tProvides:\n\t\t{:?}", domain.get_action_string(action_idx), c_problem.inertia.action_wants[action_idx].decompile(&c_problem.maps), c_problem.inertia.action_provides[action_idx].decompile(&c_problem.maps));
            for other in 0..domain.actions.len() {
                if action_idx != other {
                    println!("Comparing {} to {}: {:?}", domain.get_action_string(action_idx), domain.get_action_string(other), c_problem.inertia.cmp(action_idx, other, &c_problem.maps));
                    // for assignment in c_problem.inertia.actions[action_idx].arg_intersect(&c_problem.inertia.actions[other], &c_problem.maps) {
                    //     let r = c_problem.inertia.actions[action_idx].classify(&c_problem.inertia.actions[other], assignment.as_slice());
                    //     if r != Relationship::Unrelated {
                    //         println!("{:?} -> {:?}", assignment, r);

                    //     }
                    // }

                }
            }
        }
    }

}
