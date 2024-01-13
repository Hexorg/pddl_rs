use std::{
    fmt::{Debug, Display},
    hash::Hash
};

use crate::{compiler::PredicateUsize, Error, ErrorKind::{UndefinedVariable, ExpectedVariable}, parser::ast::List};

use super::{Name, SpannedAst, Span};

/// Function name with 0 or more arguments
#[derive(PartialEq, Clone)]
pub struct FunctionTerm<'src> {
    pub name: Name<'src>,
    pub terms: Vec<Term<'src>>,
}
impl<'src> Debug for FunctionTerm<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}({:?})", self.name.1, self.terms))
    }
}
impl<'src> SpannedAst for FunctionTerm<'src> {
    fn span(&self) -> Span {
        self.name.0.change_end(self.terms.span().end)
    }
}


/// A name, variable, or function
#[derive(PartialEq, Debug, Clone)]
pub enum Term<'src> {
    Name(Name<'src>),
    Variable(Name<'src>),
    Function(FunctionTerm<'src>), // :object-fluents
}


impl<'src> SpannedAst for Term<'src> {
    fn span(&self) -> Span {
        match self {
            Self::Name(Name(s,..)) |
            Self::Variable(Name(s,..)) => *s,
            Self::Function(f) => f.span(),
        }
    }
}
