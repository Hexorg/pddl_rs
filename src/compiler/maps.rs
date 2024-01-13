use std::collections::HashMap;

use enumset::EnumSet;

use super::{span::Span, AtomicFormula, Domain, List, Name, PredicateUsize, Problem, Type};
use crate::{Error, ErrorKind::{MissmatchedDomain, DuplicateType, DuplicateObject, DuplicatePredicate, FirstDefinedHere, UndefinedType}, Requirement, parser::ast::AtomicFSkeleton};

/// Logical structures for compiling PDDL problems.
#[derive(Debug, PartialEq)]
pub struct Maps<'src> {
    /// Domain and problem requirements
    pub requirements: EnumSet<Requirement>,
    /// Name of type to integer identifying it. Type 0 is reserved for "object".
    pub type_id_map: HashMap<&'src str, PredicateUsize>,
    /// integer identifying a type to the type's name. Type 0 is reserved for "object".
    pub id_type_map: Vec<Name<'src>>,
    /// Type inheritance tree. Top-most value is 0 - "object" type
    pub type_tree: HashMap<PredicateUsize, PredicateUsize>,
    /// object name to integer identifying it
    pub object_id_map: HashMap<&'src str, PredicateUsize>,
    /// integer identifying an object to its type
    pub id_object_map: Vec<Name<'src>>,
    /// Problem object map to Domain type.
    pub object_to_type_map: HashMap<PredicateUsize, PredicateUsize>,
    /// Domain type map to vector of objects. Note: all objects are just `0..self.id_object_map.len()`
    pub type_to_objects_map: HashMap<PredicateUsize, Vec<PredicateUsize>>,
    /// Name of predicate to integer identifying it
    pub predicate_id_map: HashMap<&'src str, PredicateUsize>,
    /// Integer identifying a predicate to its name
    pub id_predicate_map: Vec<Name<'src>>,

    // / Mapping a memory bit offset to predicate representing it. Used in `Vec<`[`Instruction`]`>::decomp()`
    // pub memory_map: Vec<AtomicFormula<'src, Name<'src>>>,
    // /// Mapping of argument vectors to compiled actions that use them
    // pub args_map: Vec<HashMap<Name<'src>, (PredicateUsize, PredicateUsize)>>,
}

impl<'src> Maps<'src> {
    pub fn new() -> Self {
        Self { requirements: EnumSet::new(), 
            type_id_map: HashMap::new(),
            id_type_map: Vec::new(),
            type_tree: HashMap::new(), 
            object_id_map: HashMap::new(),
            id_object_map: Vec::new(), 
            object_to_type_map: HashMap::new(), 
            type_to_objects_map: HashMap::new(), 
            predicate_id_map: HashMap::new(),
            id_predicate_map: Vec::new(),
            // memory_map: Vec::new()
         }
    }

    pub fn is_subtype(&self, mut current:PredicateUsize, parent:PredicateUsize) -> bool {
        if current == parent {
            return true;
        }
        while let Some(next) = self.type_tree.get(&current) {
            if *next == parent {
                return true;
            }
            current = *next
        }
        false
    }
}

/// Perform basic sanity checks like if the problem's domain match domain name
pub fn validate_problem<'src>(domain: &Domain<'src>, problem: &Problem<'src>) -> Result<(), Error> {
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
    problem: &Problem<'src>,
) -> Result<Maps<'src>, Error> {
    let requirements = domain.requirements | problem.requirements;
    let mut type_id_map =  HashMap::new();
    let mut id_type_map = Vec::new();
    let mut type_tree = HashMap::new();
    let mut object_id_map = HashMap::new();
    let mut id_object_map:Vec<Name<'src>> = Vec::new();
    let mut object_to_type_map = HashMap::new();
    let mut type_to_objects_map = HashMap::new();
    let mut predicate_id_map = HashMap::new();
    let mut id_predicate_map:Vec<Name<'src>> = Vec::new();

    type_id_map.insert("object", 0);
    id_type_map.push(Name::new(0..0, "object"));
    type_to_objects_map.insert(0, Vec::new());

    // Iterate over types and build the type tree
    for List { items, kind } in &domain.types {
        if let Type::Exact(kind) = kind {
            let kind_idx = if let Some(kind_idx) = type_id_map.get(kind.1).copied() {
                kind_idx
            } else {
                let kind_idx = type_id_map.len() as PredicateUsize;
                type_id_map.insert(kind.1, kind_idx);
                id_type_map.push(*kind);
                kind_idx
            };
            for item in items {
                let idx = id_type_map.len() as PredicateUsize;
                if let Some(duplicate_idx) = type_id_map.insert(item.1, idx) {
                    let duplicate_span = id_type_map[duplicate_idx as usize].0;
                    return Err(Error{span:item.0, kind:DuplicateType, chain:Some(Box::new(Error{span:duplicate_span, kind:FirstDefinedHere, chain:None}))})
                }
                id_type_map.push(*item);
                type_tree.insert(idx, kind_idx);
            }
        } else {
            todo!()
        }
    }

    for AtomicFSkeleton{name, ..} in &domain.predicates {
        let predicate_idx = id_predicate_map.len() as PredicateUsize;
        if let Some(duplicate_idx) = predicate_id_map.insert(name.1, predicate_idx) {
            let duplicate_span = id_predicate_map[duplicate_idx as usize].0;
            return Err(Error{span:name.0, kind:DuplicatePredicate, chain:Some(Box::new(Error{span:duplicate_span, kind:FirstDefinedHere, chain:None}))});
        }
        id_predicate_map.push(*name);
    }

    // Iterate over objects and build a Object to Type and Type to Object maps
    for List { items, kind } in &problem.objects {
        for item in items {
            let object_idx = id_object_map.len() as PredicateUsize;
            if let Some(duplicate_idx) = object_id_map.insert(item.1, object_idx) {
                let duplicate_span = id_object_map[duplicate_idx as usize].0;
                return Err(Error{span:item.0, kind:DuplicateObject, chain:Some(Box::new(Error{span:duplicate_span, kind:FirstDefinedHere, chain:None}))});
            }
            id_object_map.push(*item);

            let mut kind_id = match kind {
                Type::None => 0,
                Type::Either(_) => todo!(),
                Type::Exact(kind) => if let Some(idx) = type_id_map.get(kind.1) { *idx } else { return Err(Error{span:kind.0, kind:UndefinedType, chain:None}) },
            };

            object_to_type_map.insert(object_idx, kind_id);

            loop {
                if type_to_objects_map
                .get_mut(&kind_id)
                .and_then(|vec: &mut Vec<PredicateUsize>| {
                    Some(vec.push(object_idx))
                })
                .is_none()
                {
                    type_to_objects_map.insert(kind_id, vec![object_idx]);
                }
                if let Some(parent_type_id) = type_tree.get(&kind_id) {
                    kind_id = *parent_type_id;
                } else {
                    break;
                }
            }
        }
    }
    Ok(Maps {
        requirements,
        type_id_map,
        id_type_map,
        type_tree,
        object_id_map,
        id_object_map,
        object_to_type_map,
        type_to_objects_map,
        predicate_id_map,
        id_predicate_map
    })
}

#[cfg(test)]
mod test {
    use crate::{compiler::tests::TINY_SOURCES, ReportPrinter, parser::ast::name::Name, lib_tests::load_repo_pddl};

    use super::map_objects;

    #[test]
    fn test_map() {
        let (domain, problem) = TINY_SOURCES.parse();
        let maps = match map_objects(&domain, &problem) {
            Ok(maps) => maps,
            Err(e) => Err(vec![e]).unwrap_or_print_report(&TINY_SOURCES)
        };
        assert_eq!(maps.object_id_map.get("a"), Some(&0));
        assert_eq!(maps.object_id_map.get("b"), Some(&1));
        assert_eq!(maps.object_id_map.get("c"), Some(&2));
        assert_eq!(maps.id_object_map.len(), 3);
        assert_eq!(maps.predicate_id_map.get("a"), Some(&0));
        assert_eq!(maps.predicate_id_map.get("b"), Some(&1));
        assert_eq!(maps.predicate_id_map.len(), 2);
        assert_eq!(maps.type_to_objects_map.get(&0), Some(&vec![0, 1, 2]));
        assert_eq!(maps.type_to_objects_map.len(), 1);
        assert_eq!(maps.id_type_map.get(0), Some(&Name::new(0..0, "object")));
        assert_eq!(maps.id_type_map.len(), 1)
    }

    #[test]
    fn test_barman() {
        let sources = load_repo_pddl(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
        );
        let (domain, problem) = sources.parse();
        println!("{:?}", domain.types);
        let maps = match map_objects(&domain, &problem) {
            Ok(maps) => maps,
            Err(e) => Err(vec![e]).unwrap_or_print_report(&sources)
        };
        assert_eq!(maps.type_id_map.len(), 10);
        assert_eq!(maps.type_id_map.get("container"), Some(&5));
        assert_eq!(maps.type_to_objects_map.get(&5), Some(&vec![]))
    }

}
