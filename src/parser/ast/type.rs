use std::{
    fmt::{Debug, Display},
    hash::Hash, collections::HashMap
};

use crate::compiler::{PredicateUsize, maps::Maps};

use super::{name::Name, SpannedAst, Span};

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum Type<'src> {
    None,
    Either(Vec<Name<'src>>),
    Exact(Name<'src>),
}

impl<'src> SpannedAst for Type<'src> {
    fn span(&self) -> Span {
        match self {
            Type::None => Span {
                start: 0,
                end: 0,
                is_problem: false,
            },
            Type::Either(vec) => vec.span(),
            Type::Exact(name) => name.span(),
        }
    }
}
impl<'src> Display for Type<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::None => f.write_str("object"),
            Type::Either(vec) => f.write_fmt(format_args!(
                "(either {})",
                vec.iter().map(|n| n.1).collect::<Vec<_>>().join(", ")
            )),
            Type::Exact(name) => f.write_str(name.1),
        }
    }
}
impl<'src> Debug for Type<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Self as Display>::fmt(&self, f)
    }
}

impl<'src> Type<'src> {
    pub const OBJECT:Name<'static> = Name(Span { start: 0, end: 0, is_problem: false }, "object");
    pub fn to_id(&self, maps:&Maps) -> PredicateUsize {
        match self {
            Type::None => 0,
            Type::Either(_) => todo!(),
            Type::Exact(t) => maps.type_id_map.get(t.1).copied().unwrap(),
        }
    }
    pub fn unwrap_name(&self) -> Name<'src> {
        match self {
            Type::None => Type::OBJECT,
            Type::Either(_) => todo!(),
            Type::Exact(name) => *name,
        }
    }
}