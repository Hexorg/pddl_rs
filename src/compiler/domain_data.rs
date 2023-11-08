use std::{
    collections::{HashMap, HashSet},
    num::NonZeroI8,
    ops::Range,
};

use enumset::EnumSet;

use super::{
    action_graph::ActionGraph, for_all_type_object_permutations, AtomicFSkeleton, AtomicFormula,
    Domain, List, Name, NegativeFormula, Objects, PredicateUsize, Problem, Span, StateUsize, Type,
};
use crate::{Error, ErrorKind, Requirement};

/// Logical structures for compiling PDDL problems.
#[derive(Debug, PartialEq)]
pub struct DomainData<'src> {
    /// Domain and problem requirements
    pub requirements: EnumSet<Requirement>,
    /// Type inheritance tree. Everything should end up being an object.
    pub type_tree: HashMap<&'src str, Name<'src>>,
    /// Source code position mapping of where types are declared.
    pub type_src_pos: HashMap<&'src str, Span>,
    /// Problem object map to Domain type.
    pub object_to_type_map: HashMap<&'src str, Name<'src>>,
    /// Domain type map to vector of objects. Note: `"object"` type must list all
    /// problem objects.
    pub type_to_objects_map: HashMap<&'src str, Vec<(PredicateUsize, PredicateUsize)>>,
    /// Source code position mapping of where problem objects are declared.
    pub object_src_pos: HashMap<&'src str, Span>,
    /// Mapping a vector of `[predicate, arg1, arg2, .., argN]` to a memory bit offset.
    pub predicate_memory_map: HashMap<AtomicFormula<'src, Name<'src>>, StateUsize>,
    // Optimization structures:
    /// Each offset in this vector matches the offset of action list vector.
    pub action_graph: ActionGraph,
    /// Set of all predicate names that have been identified as constant
    pub constant_predicates: HashSet<Name<'src>>,
    /// Set of all concrete atomic formulas that have been identified to stay true
    /// no matter what actions have been executed
    pub const_true_predicates: HashSet<AtomicFormula<'src, Name<'src>>>,
    /// Set of all concrete atomic formulas that have been identified to stay false
    /// no matter what actions have been executed
    pub const_false_predicates: HashSet<AtomicFormula<'src, Name<'src>>>,
    /// A map of AST Actions to Compiled action ranges. The range represents
    /// All possible calls of a given action (for permutated objects)
    pub compiled_action_ranges: Vec<Range<usize>>,
}

/// Perform basic sanity checks like if the problem's domain match domain name
pub fn validate_problem<'src>(domain: &Domain<'src>, problem: &Problem<'src>) -> Result<(), Error> {
    use ErrorKind::*;
    if problem.domain.1 != domain.name.1 {
        return Err(Error {
            // input: None,
            kind: MissmatchedDomain,
            chain: None,
            span: problem.domain.0,
        });
    }

    Ok(())
}

/// Iterate through proper domain and problem structs to build type tree,
/// object type map, and mapping of predicate calls to memory offsets.
/// # Arguments
/// * `domain` - PDDL Domain
/// * `problem` - PDDL Problem
pub fn map_objects<'src>(
    domain: &Domain<'src>,
    problem: &'src Problem<'src>,
    constants: HashSet<Name<'src>>,
) -> Result<DomainData<'src>, Error> {
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
    for (list_idx, List { items, kind }) in problem.objects.iter().enumerate() {
        let list_idx = list_idx as u16;
        match kind {
            Type::Exact(kind) => {
                for (item_idx, item) in items.iter().enumerate() {
                    let item_idx = item_idx as u16;
                    object_src_pos.insert(item.1, item.0.clone());
                    object_to_type_map.insert(item.1, kind.to_owned());
                    let mut type_name = kind.1;
                    while let Some(parent_type) = type_tree.get(type_name) {
                        if type_to_objects_map
                            .get_mut(type_name)
                            .and_then(|vec: &mut Vec<(u16, u16)>| {
                                Some(vec.push((list_idx, item_idx)))
                            })
                            .is_none()
                        {
                            type_to_objects_map.insert(type_name, vec![(list_idx, item_idx)]);
                        }
                        type_name = parent_type.1;
                    }
                    type_to_objects_map
                        .get_mut("object")
                        .and_then(|vec: &mut Vec<(u16, u16)>| {
                            Some(vec.extend((0..items.len()).map(|i| (list_idx, i as u16))))
                        });
                }
            }
            Type::None => {
                object_src_pos.extend(items.iter().map(|i| (i.1, i.0.clone())));
                type_to_objects_map
                    .get_mut("object")
                    .and_then(|vec: &mut Vec<(u16, u16)>| {
                        Some(vec.extend((0..items.len()).map(|i| (list_idx, i as u16))))
                    });
            }
            Type::Either(_) => todo!(),
        }
    }
    let mut predicate_memory_map = HashMap::new();
    let mut const_true_predicates = HashSet::new();
    let mut const_false_predicates = HashSet::new();
    let mut constant_predicates = HashSet::new();
    //Iterate over predicates and its objects and build a memory map
    for AtomicFSkeleton { name, variables } in &domain.predicates {
        if !constants.contains(name) {
            for_all_type_object_permutations::<_, NonZeroI8>(
                &type_to_objects_map,
                &variables,
                |args| {
                    let formula = AtomicFormula::predicate(
                        name.clone(),
                        args.iter()
                            .map(|i| problem.objects.get_object(i.1 .0, i.1 .1).item)
                            .collect(),
                    );
                    if !predicate_memory_map.contains_key(&formula) {
                        predicate_memory_map
                            .insert(formula, predicate_memory_map.len() as PredicateUsize);
                    } else {
                        panic!("Predicate memory map already contains this");
                    }
                    Ok(None)
                },
            )?;
        } else {
            for init in &problem.init {
                match init {
                    super::Init::AtomicFormula(af) => match af {
                        NegativeFormula::Direct(af) => {
                            if af.name().1 == name.1 {
                                const_true_predicates.insert(af.clone());
                                constant_predicates.insert(*name);
                            }
                        }
                        NegativeFormula::Not(af) => {
                            if af.name().1 == name.1 {
                                const_false_predicates.insert(af.clone());
                                constant_predicates.insert(*name);
                            }
                        }
                    },
                    super::Init::At(_, _) => todo!(),
                    super::Init::Equals(_, _) => todo!(),
                    super::Init::Is(_, _) => todo!(),
                }
            }
        }
    }
    Ok(DomainData {
        requirements,
        type_tree,
        type_src_pos,
        object_to_type_map,
        type_to_objects_map,
        constant_predicates,
        object_src_pos,
        predicate_memory_map,
        action_graph: ActionGraph::new(),
        const_false_predicates,
        const_true_predicates,
        compiled_action_ranges: Vec::with_capacity(domain.actions.len()),
    })
}

#[cfg(test)]
mod test {
    use crate::{
        compiler::{
            parse_domain, parse_problem,
            tests::{TINY_DOMAIN_SRC, TINY_PROBLEM_SRC, TINY_SOURCES},
        },
        ReportPrinter,
    };

    use super::*;

    #[test]
    fn test_mapping() {
        let domain = parse_domain(TINY_DOMAIN_SRC).unwrap_or_print_report(&TINY_SOURCES);
        let problem = parse_problem(TINY_PROBLEM_SRC, domain.requirements)
            .unwrap_or_print_report(&TINY_SOURCES);
        let predicates = domain.get_predicate_names();
        let objects = problem.get_objects();
        let compiler = map_objects(&domain, &problem, HashSet::new()).unwrap();
        assert_eq!(
            compiler.predicate_memory_map,
            HashMap::<AtomicFormula<'_, Name>, PredicateUsize>::from([
                (
                    AtomicFormula::predicate(predicates[0].clone(), vec![objects[0].clone()]),
                    0
                ),
                (
                    AtomicFormula::predicate(predicates[0].clone(), vec![objects[1].clone()]),
                    1
                ),
                (
                    AtomicFormula::predicate(predicates[0].clone(), vec![objects[2].clone()]),
                    2
                ),
                // (vec!["pb", "a", "a"], 3),
                (
                    AtomicFormula::predicate(
                        predicates[1].clone(),
                        vec![objects[1].clone(), objects[0].clone()]
                    ),
                    3
                ),
                (
                    AtomicFormula::predicate(
                        predicates[1].clone(),
                        vec![objects[2].clone(), objects[0].clone()]
                    ),
                    4
                ),
                (
                    AtomicFormula::predicate(
                        predicates[1].clone(),
                        vec![objects[0].clone(), objects[1].clone()]
                    ),
                    5
                ),
                // (vec!["pb", "b", "b"], 7),
                (
                    AtomicFormula::predicate(
                        predicates[1].clone(),
                        vec![objects[2].clone(), objects[1].clone()]
                    ),
                    6
                ),
                (
                    AtomicFormula::predicate(
                        predicates[1].clone(),
                        vec![objects[0].clone(), objects[2].clone()]
                    ),
                    7
                ),
                (
                    AtomicFormula::predicate(
                        predicates[1].clone(),
                        vec![objects[1].clone(), objects[2].clone()]
                    ),
                    8
                ),
                // (vec!["pb", "c", "c"], 11),
            ])
        )
    }
}
