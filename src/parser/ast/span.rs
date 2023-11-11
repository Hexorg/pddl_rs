use std::{ops::Range, fmt::{Debug, Display}};


#[derive(PartialEq, Eq, Clone, Copy)]
/// Span of an AST element in the source code. `start` and `end` represet byte-offsets in the source code
/// Also keeps track if the AST element is in the problem source or domain.
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub is_problem: bool,
}
impl<'src> Span {
    pub fn expand(&self, add: usize) -> Self {
        let mut copy = *self;
        copy.end += add;
        copy
    }
    pub fn change_end(&self, end: usize) -> Self {
        Self {
            start: self.start,
            end,
            is_problem: self.is_problem,
        }
    }
    pub fn new_range(&self, range: Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            is_problem: self.is_problem,
        }
    }
}

impl<'src> Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}..{}", self.start, self.end))
    }
}

impl<'src> Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}..{}", self.start, self.end))
    }
}

impl<'src> Into<Span> for Range<usize> {
    fn into(self) -> Span {
        Span {
            start: self.start,
            end: self.end,
            is_problem: false,
        }
    }
}
impl<'src> Into<Range<usize>> for Span {
    fn into(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Any AST Node that spans some source code characters.
pub trait SpannedAst {
    fn span(&self) -> Span;
}

/// Any AST Node that spans some source code characters and allows that span to be changed.
pub trait SpannedAstMut<'src>: SpannedAst {
    fn span_mut(&mut self) -> &mut Span;
}
impl<O> SpannedAst for Spanned<O> {
    #[inline]
    fn span(&self) -> Span {
        self.0
    }
}
impl<'src, O> SpannedAstMut<'src> for Spanned<O> {
    #[inline]
    fn span_mut(&mut self) -> &mut Span {
        &mut self.0
    }
}

pub type Spanned<O> = (Span, O);

impl<O> SpannedAst for Vec<O>
where
    O: SpannedAst,
{
    fn span(&self) -> Span {
        let (start, is_problem) = self
            .first()
            .and_then(|r| Some((r.span().start, r.span().is_problem)))
            .unwrap_or((0, false));
        let end = self
            .last()
            .and_then(|r| Some(r.span().end))
            .unwrap_or(start);
        Span {
            start,
            end,
            is_problem,
        }
    }
}