

use std::fmt::Display;


use crate::SpannedAst;

use super::{name::Name, term::Term};


#[derive(PartialEq, Debug)]
pub enum AtomicFormula<'src, T> {
    Predicate(Name<'src>, Vec<T>),
    Equality(T, T),
}

impl<'src, T> SpannedAst for AtomicFormula<'src, T> where T:SpannedAst{
    fn span(&self) -> super::span::Span {
        match self {
            AtomicFormula::Predicate(p,..) => p.span(),
            AtomicFormula::Equality(p,..) => p.span(),
        }
    }
}

impl<'src, T> AtomicFormula<'src, T> {
    pub fn name(&self) -> Name<'src> {
        if let Self::Predicate(name,..) = self {
            *name
        } else {
            panic!("Expected predicate formula")
        }
    }
}
// impl Ord for AtomicFormula<Name> {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         match self {
//             AtomicFormula::Predicate(self_name, self_args) => match other {
//                 AtomicFormula::Predicate(other_name, other_args) => todo!(),
//                 AtomicFormula::Equality(..) => std::cmp::Ordering::Greater,
//             },
//             AtomicFormula::Equality(left, right) => match other {
//                 AtomicFormula::Equality(_, _) => todo!(),
//                 AtomicFormula::Predicate(..) => std::cmp::Ordering,
//             },
//         }
//     }
// }
// impl PartialOrd for AtomicFormula<Name> {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         todo!()
//     }
// }
impl<'src, T> Display for AtomicFormula<'src, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicFormula::Predicate(name, vec) => f.write_fmt(format_args!(
                "{}({})",
                name,
                vec.iter()
                    .map(|i| format!("{}", i))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
            AtomicFormula::Equality(left, right) => {
                f.write_fmt(format_args!("{} = {}", left, right))
            }
        }
    }
}
// impl<T> Debug for AtomicFormula<T>
// where
//     T: Debug,
// {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             AtomicFormula::Predicate(name, vec) => f.write_fmt(format_args!(
//                 "{}({})",
//                 name,
//                 vec.iter()
//                     .map(|i| format!("{:?}", i))
//                     .collect::<Vec<_>>()
//                     .join(", ")
//             )),
//             AtomicFormula::Equality(left, right) => {
//                 f.write_fmt(format_args!("{:?} = {:?}", left, right))
//             }
//         }
//     }
// }


// impl<'src> AtomicFormula<Name<'src>> {
//     pub fn to_typed(
//         &self,
//         type_tree: &HashMap<&'src str, Name>,
//     ) -> HashSet<AtomicFormula<Type>> {
//         let mut result = HashSet::new();
//         match self {
//             AtomicFormula::Predicate(predicate, objects) => {
//                 let mut type_vec = objects.clone();
//                 let mut more_iterations = true;
//                 while more_iterations {
//                     more_iterations = false;
//                     let mut new_type_vec = Vec::new();
//                     if type_tree.len() > 0 {
//                         for obj in &type_vec {
//                             let type_name = *type_tree.get(obj.1).unwrap();
//                             if type_name.1 != "object" {
//                                 more_iterations = true;
//                             }
//                             new_type_vec.push(type_name);
//                         }
//                         result.insert(AtomicFormula::Predicate(
//                             *predicate,
//                             new_type_vec.iter().map(|t| Type::Exact(*t)).collect(),
//                         ));
//                     } else {
//                         result.insert(AtomicFormula::Predicate(
//                             *predicate,
//                             (0..type_vec.len()).map(|_| Type::None).collect(),
//                         ));
//                     }
//                     type_vec = new_type_vec;
//                 }
//             }
//             AtomicFormula::Equality(_, _) => todo!(),
//         }
//         result
//     }
// }
impl<'src> Into<AtomicFormula<'src, Term<'src>>> for &AtomicFormula<'src, Name<'src>> {
    fn into(self) -> AtomicFormula<'src, Term<'src>> {
        match self {
            AtomicFormula::Predicate(name, args) => {
                let term_vec = args.iter().map(|arg| Term::Name(*arg)).collect::<Vec<_>>();
                AtomicFormula::Predicate(*name, term_vec)
            }
            AtomicFormula::Equality(_, _) => todo!(),
        }
    }
}
// impl TryInto<AtomicFormula<Name>> for &AtomicFormula<Term> {
//     type Error = Error;

//     fn try_into(self) -> Result<AtomicFormula<Name>, Self::Error> {
//         match self {
//             AtomicFormula::Predicate(name, terms) => {
//                 let mut name_vec = Vec::with_capacity(terms.len());
//                 for term in terms {
//                     match term {
//                         Term::Name(name) => name_vec.push(*name),
//                         _ => {
//                             return Err(Self::Error {
//                                 span: terms.span(),
//                                 kind: ExpectedName,
//                                 chain: None,
//                             })
//                         }
//                     }
//                 }
//                 Ok(AtomicFormula::Predicate(*name, name_vec))
//             }
//             AtomicFormula::Equality(_, _) => todo!(),
//         }
//     }
// }

// impl AtomicFormula<Term> {
//     pub fn concrete(
//         &self,
//         objects: &[List],
//         args: &[(Name, (PredicateUsize, PredicateUsize))],
//     ) -> Result<AtomicFormula<Name>, Error> {
//         match self {
//             AtomicFormula::Predicate(predicate, variables) => {
//                 let name_vec = variables.iter().map(|t| t.concrete_name(objects, args)).collect::<Result<Vec<_>, Error>>()?;
//                 Ok(AtomicFormula::Predicate(predicate.clone(), name_vec))
//             }
//             AtomicFormula::Equality(_, _) => todo!(),
//         }
//     }

//     pub fn typed(&self, parameters:&[List]) -> Result<AtomicFormula<Type>, Error> {
//         match self {
//             AtomicFormula::Predicate(predicate, variables) => {
//                 let name_vec = variables.iter().map(|t| t.concrete_type(parameters)).collect::<Result<Vec<_>, Error>>()?;
//                 Ok(AtomicFormula::Predicate(predicate.clone(), name_vec))
//             }
//             AtomicFormula::Equality(_, _) => todo!(),
//         }
//     }
// }


#[derive(PartialEq, Debug)]
pub enum NegativeFormula<'src, T>
{
    Direct(AtomicFormula<'src, T>),
    Not(AtomicFormula<'src, T>),
}


