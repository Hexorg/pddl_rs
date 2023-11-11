use std::{
    collections::{HashMap, HashSet},
    num::NonZeroI8,
    ops::Range,
};

use enumset::EnumSet;

use super::{
    action_graph::ActionGraph, for_all_type_object_permutations, AtomicFSkeleton, AtomicFormula,
    Domain, List, Name, NegativeFormula, Objects, PredicateUsize, Problem, span::Span, StateUsize, Type, inertia::Inertia,
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
    /// All Readable and Writable typed predicates used in the domain ordered by action
    pub action_inertia: Vec<Inertia<AtomicFormula<'src, Type<'src>>>>,
    /// Set of all predicate names that have been identified as constant
    // pub constant_predicates: HashSet<Name<'src>>,
    /// Set of all concrete atomic formulas that have been identified to stay true
    /// no matter what actions have been executed
    pub const_true_predicates: HashSet<AtomicFormula<'src, Name<'src>>>,
    /// Set of all concrete atomic formulas that have been identified to stay false
    /// no matter what actions have been executed
    pub const_false_predicates: HashSet<AtomicFormula<'src, Name<'src>>>,
    // /// A map of AST Actions to Compiled action ranges. The range represents
    // /// All possible calls of a given action (for permutated objects)
    // pub compiled_action_ranges: Vec<Range<usize>>,
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
    Ok(DomainData {
        requirements,
        type_tree,
        type_src_pos,
        object_to_type_map,
        type_to_objects_map,
        object_src_pos,
        predicate_memory_map: HashMap::new(),
        action_inertia: Vec::new(),
        action_graph: ActionGraph::new(),
        const_false_predicates: HashSet::new(),
        const_true_predicates: HashSet::new(),
    })
}

// fn digitize_names<'src, 'ast>(
//     compiler: &Compiler<'ast, 'src>,
//     context: &mut Context<'src>
// ) {
//     let mut predicate_id_map:HashMap<&'src str, PredicateUsize> = HashMap::new();
//     let mut id_predicate_map:Vec<Name<'src>> = Vec::new();
//     let mut type_id_map:HashMap<Type<'src>, PredicateUsize> = HashMap::new();
//     let mut id_type_map:Vec<Type<'src>> = Vec::new();
//     let mut object_id_map:HashMap<&'src str, StateUsize> = HashMap::new();
//     let mut id_object_map:Vec<Name<'src>> = Vec::new();
//     let mut type_tree_map:HashMap<PredicateUsize, PredicateUsize> = HashMap::new();
//     for AtomicFSkeleton { name, variables } in compiler.domain.predicates {
//         let id = predicate_id_map.len() as PredicateUsize;
//         if predicate_id_map.insert(name.1, id).is_some() {
//             context.errors.push(Error { span: name.0, kind:RedefinedPredicate, chain:None })
//         } else {
//             if id_predicate_map.len() != id as usize { panic!("id to predicate and predicate to id maps diverged.")}
//             id_predicate_map.push(name);

//         }
//     }
//     type_id_map.insert(Type::Exact(Name::new(0..0, "object")), 0);
//     for List { items, kind } in compiler.domain.types {
//         let kind_id = if !type_id_map.contains_key(&kind) {
//             let id = type_id_map.len() as PredicateUsize;
//             type_id_map.insert(kind, id);
//             if id_type_map.len() != id as usize { panic!("id to type and type to id maps diverged")}
//             id_type_map.push(kind);
//             id
//         } else {
//             *type_id_map.get(&kind).unwrap()
//         };
//         for item in items {
//             let item = Type::Exact(item);
//             let item_id = if !type_id_map.contains_key(&item) {
//                 let id = type_id_map.len() as PredicateUsize;
//                 type_id_map.insert(item, id);
//                 if id_type_map.len() != id as usize { panic!("id to type and type to id maps diverged")}
//                 id
//             } else {
//                 *type_id_map.get(&item).unwrap()
//             };
//             if type_tree_map.insert(item_id, kind_id).is_some() {
//                 context.errors.push(Error { span: id_type_map[item_id as usize].span(), kind: RedefinedType, chain: None })
//             }
//         }
//     }
//     for List { items, kind } in compiler.problem.objects {
//         for item in items {
//             let id = object_id_map.len() as StateUsize;
//             if object_id_map.insert(item.1, id).is_some() {
//                 context.errors.push(Error { span: item.0, kind:RedefinedObject, chain:None })
//             }
//             if id_object_map.len() != id as usize { panic!("id to object and object to id maps diverged")}
//             id_object_map.push(item);
//         }
//     }
// }

#[cfg(test)]
mod test {
}