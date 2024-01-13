use crate::{parser::ast::{atomic_formula::AtomicFormula, term::Term, r#type::Type, list::TypedList}, Error, ErrorKind::{UndefinedPredicate, ExpectedVariable, UndefinedVariable, UndefinedObject}, SpannedAst};

use super::{PredicateUsize, maps::Maps};

#[derive(Clone, Copy)]
pub enum ArgKind {
    /// Used in Inertia
    ParameterIndex,
    /// Used in Compiled Problem where everything has been mapped to the object
    Object,
    /// Used in Solution estimation where we only know types.
    Type
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
/// Representation of an atomic formula (predicate with terms)
/// where args are indexes in its parent action
pub struct CompiledAtomicFormula {
    /// Predicate ID
    pub predicate_idx: PredicateUsize,
    /// Vector of indexes into action parameters or objects,
    /// Depending on where this is used.
    pub args: Vec<PredicateUsize>,
}


impl CompiledAtomicFormula {
    pub fn compile(maps:&Maps, parameters_or_objects:&TypedList, formula:&AtomicFormula<Term>) -> Result<Self, Error> {
        match formula {
            AtomicFormula::Predicate(name, args) => {
                let predicate_idx = *maps.predicate_id_map.get(name.1).ok_or(Error{span:name.0, kind:UndefinedPredicate, chain:None})?;
                let args = args.iter().map(|a| match a {
                    Term::Name(v) => parameters_or_objects.find(|i| i.1 == v.1).ok_or(Error{span:v.0, kind:UndefinedObject, chain:None}),
                    Term::Variable(v) => parameters_or_objects.find(|i| i.1 == v.1).ok_or(Error{span:v.0, kind:UndefinedVariable, chain:None}),
                    Term::Function(_) => Err(Error{span:a.span(), kind:ExpectedVariable, chain:None}),
                }).collect::<Result<Vec<_>, Error>>()?;
                Ok(Self { predicate_idx, args })
            },
            AtomicFormula::Equality(_, _) => todo!(),
        }
    }

    pub fn decompile(&self, maps:&Maps, action_parameters:Option<&[PredicateUsize]>, arg_kind:ArgKind) -> String {
        let predicate = maps.id_predicate_map.get(self.predicate_idx as usize).unwrap().1;
        let args = self.args.iter().map(|a| match arg_kind {
            ArgKind::ParameterIndex => if let Some(parameters) = action_parameters {
                maps.id_type_map.get(parameters[*a as usize] as usize).unwrap().1.to_owned() } else {
                    format!("?{}", char::from_u32(97+(*a) as u32).unwrap())
            },
            ArgKind::Object => maps.id_object_map[*a as usize].1.to_owned(),
            ArgKind::Type => maps.id_type_map[*a as usize].1.to_owned()
        }).collect::<Vec<_>>().join(", ");
        format!("{}({})", predicate, args)
    }
}
