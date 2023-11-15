use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::Range,
};

use super::span::*;

#[derive(Clone, Copy)]
pub struct Name<'src>(pub Span, pub &'src str);
impl<'src> Name<'src> {
    pub fn new(range: impl Into<Range<usize>>, name: &'src str) -> Self {
        Self(range.into().into(), name)
    }
}
impl<'src> Display for Name<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.1)
    }
}
impl<'src> Debug for Name<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.1)
    }
}
impl<'src> Into<Name<'src>> for Spanned<&'src str> {
    fn into(self) -> Name<'src> {
        Name(self.0, self.1)
    }
}
impl<'src> SpannedAst for Name<'src> {
    fn span(&self) -> Span {
        self.0
    }
}
impl<'src> SpannedAstMut<'src> for Name<'src> {
    fn span_mut(&mut self) -> &mut Span {
        &mut self.0
    }
}
impl<'src> PartialEq for Name<'src> {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}
impl<'src> Eq for Name<'src> {}
impl<'src> Hash for Name<'src> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.1.hash(state)
    }
}
