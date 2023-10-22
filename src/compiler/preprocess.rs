use std::{collections::HashMap, ops::Range};

use enumset::EnumSet;

use crate::{Requirement, Error, ErrorKind};
use super::{Name, Domain, Problem, List, Type, AtomicFSkeleton, for_all_type_object_permutations};


/// Logical structures for compiling PDDL problems. 
#[derive(Debug)]
pub struct PreprocessData<'src> {
    pub requirements: EnumSet<Requirement>,
    /// Type inheritance tree. Everything should end up being an object.
    pub type_tree: HashMap<&'src str, Name<'src>>,
    /// Source code position mapping of where types are declared.
    pub type_src_pos: HashMap<&'src str, Range<usize>>,
    /// Problem object map to Domain type.
    pub object_to_type_map: HashMap<&'src str, Name<'src>>,
    /// Domain type map to vector of objects. Note: `"object"` type must list all
    /// problem objects.
    pub type_to_objects_map: HashMap<&'src str, Vec<Name<'src>>>,
    /// Source code position mapping of where problem objects are declared.
    pub object_src_pos: HashMap<&'src str, Range<usize>>,
    /// Mapping a vector of `[predicate, arg1, arg2, .., argN]` to a memory bit offset.
    pub predicate_memory_map: HashMap<Vec<&'src str>, usize>,
}

pub fn preprocess<'src>(domain:&Domain<'src>, problem:&Problem<'src>) -> Result<PreprocessData<'src>, Error<'src>> {
    validate_problem(domain, problem)?;
    map_objects(domain, problem)
}

fn validate_problem<'src>(
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<(), Error<'src>> {
    use ErrorKind::*;
    if problem.domain.1 != domain.name.1 {
        return Err(Error {
            input: None,
            kind: MissmatchedDomain(domain.name.1),
            chain: None,
            range: problem.domain.0.clone(),
        });
    }

    Ok(())
}

/// Iterate through proper domain and problem structs to build type tree,
/// object type map, and mapping of predicate calls to memory offsets.
/// # Arguments
/// * `domain` - PDDL Domain
/// * `problem` - PDDL Problem
fn map_objects<'src>(
    domain: &Domain<'src>,
    problem: &Problem<'src>,
) -> Result<PreprocessData<'src>, Error<'src>> {
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
    for List { items, kind } in &problem.objects {
        match kind {
            Type::Exact(kind) => {
                for item in items {
                    object_src_pos.insert(item.1, item.0.clone());
                    object_to_type_map.insert(item.1, kind.to_owned());
                    let mut type_name = kind.1;
                    while let Some(parent_type) = type_tree.get(type_name) {
                        if type_to_objects_map
                            .get_mut(type_name)
                            .and_then(|vec: &mut Vec<Name>| Some(vec.push(item.to_owned())))
                            .is_none()
                        {
                            type_to_objects_map.insert(type_name, vec![item.to_owned()]);
                        }
                        type_name = parent_type.1;
                    }
                    type_to_objects_map
                        .get_mut("object")
                        .and_then(|vec: &mut Vec<Name>| Some(vec.extend(items.iter().cloned())));
                }
            }
            Type::None => {
                object_src_pos.extend(items.iter().map(|i| (i.1, i.0.clone())));
                type_to_objects_map
                    .get_mut("object")
                    .and_then(|vec: &mut Vec<Name>| Some(vec.extend(items.iter().cloned())));
            }
            Type::Either(_) => todo!(),
        }
    }
    let mut predicate_memory_map = HashMap::new();
    //Iterate over predicates and its objects and build a memory map
    for AtomicFSkeleton { name, variables } in &domain.predicates {
        for_all_type_object_permutations(&type_to_objects_map, &variables, |args| {
            let mut call_vec = vec![name.1];
            call_vec.extend(args.iter().map(|i| i.1 .1));
            if !predicate_memory_map.contains_key(&call_vec) {
                predicate_memory_map.insert(call_vec, predicate_memory_map.len());
            }
            Ok(())
        })?;
    }
    Ok(PreprocessData {
        requirements,
        type_tree,
        type_src_pos,
        object_to_type_map,
        type_to_objects_map,
        object_src_pos,
        predicate_memory_map,
    })
}

#[cfg(test)]
mod test {
    use crate::compiler::{parse_domain, parse_problem};

    use super::*;
    fn get_tiny_domain() -> (Domain<'static>, Problem<'static>) {
        let domain = parse_domain(
            "(define (domain unit-test)
                (:predicates (a ?one) (b ?one ?two))
                (:action aOne :parameters(?one ?two) 
                    :precondition(and (a ?one) (b ?one ?two) (a ?two))
                    :effect (and (not (a ?one)) (not (a ?two)))
                ))",
        )
        .unwrap();
        let problem = parse_problem(
            "(define (problem unit-test)
                (:domain unit-test)
                (:objects a b c)
                (:init (a a) (b a b))
                (:goal (not (a a)))
                )",
            enumset::EnumSet::EMPTY,
        )
        .unwrap();
        (domain, problem)
    }

    #[test]
    fn test_mapping() {
        let (domain, problem) = get_tiny_domain();
        let compiler = map_objects(&domain, &problem).unwrap();
        assert_eq!(
            compiler.predicate_memory_map,
            HashMap::<Vec<&str>, usize>::from([
                (vec!["a", "a"], 0),
                (vec!["a", "b"], 1),
                (vec!["a", "c"], 2),
                (vec!["b", "a", "a"], 3),
                (vec!["b", "b", "a"], 4),
                (vec!["b", "c", "a"], 5),
                (vec!["b", "a", "b"], 6),
                (vec!["b", "b", "b"], 7),
                (vec!["b", "c", "b"], 8),
                (vec!["b", "a", "c"], 9),
                (vec!["b", "b", "c"], 10),
                (vec!["b", "c", "c"], 11),
            ])
        )
    }
}