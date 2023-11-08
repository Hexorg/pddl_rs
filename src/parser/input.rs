use super::ast::{Requirement, Span, SpannedAst};
use enumset::EnumSet;
use nom::{Compare, InputIter, InputLength, InputTake, Offset, Slice, UnspecializedInput};
use std::{
    ops::{RangeFrom, RangeTo},
    str::{CharIndices, Chars},
};

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Input<'src> {
    pub is_problem: bool,
    pub src: &'src str,
    pub input_pos: usize,
    pub requirements: EnumSet<Requirement>,
}
impl<'src> Input<'src> {
    pub fn new(is_problem: bool, src: &'src str) -> Self {
        Self {
            // filename:None,
            src,
            is_problem,
            input_pos: 0,
            requirements: EnumSet::EMPTY,
        }
    }
    pub fn span_end(&self, end: usize) -> Span {
        Span {
            start: self.input_pos,
            end,
            is_problem: self.is_problem,
        }
    }
}

impl InputLength for Input<'_> {
    fn input_len(&self) -> usize {
        self.src.len()
    }
}
impl<'src> InputIter for Input<'src> {
    type Item = char;
    type Iter = CharIndices<'src>;
    type IterElem = Chars<'src>;

    fn iter_indices(&self) -> Self::Iter {
        self.src.iter_indices()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.src.iter_elements()
    }

    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.src.position(predicate)
    }

    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        self.src.slice_index(count)
    }
}
impl<'src> InputTake for Input<'src> {
    fn take(&self, count: usize) -> Self {
        let src = &self.src[..count];
        Self {
            // filename:self.filename,
            src,
            is_problem: self.is_problem,
            input_pos: self.input_pos,
            requirements: self.requirements,
        }
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.src.split_at(count);
        let prefix = Self {
            // filename:self.filename,
            src: prefix,
            is_problem: self.is_problem,
            input_pos: self.input_pos,
            requirements: self.requirements,
        };
        let suffix = Self {
            // filename:self.filename,
            src: suffix,
            is_problem: self.is_problem,
            input_pos: self.input_pos + count,
            requirements: self.requirements,
        };
        (suffix, prefix)
    }
}
impl<'src> Compare<&str> for Input<'src> {
    fn compare(&self, t: &str) -> nom::CompareResult {
        self.src.compare(t)
    }

    fn compare_no_case(&self, t: &str) -> nom::CompareResult {
        self.src.compare_no_case(t)
    }
}
impl<'src> Slice<RangeFrom<usize>> for Input<'src> {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        let input_pos = self.input_pos + range.start;
        let src = self.src.slice(range);
        Self {
            // filename:self.filename,
            src,
            is_problem: self.is_problem,
            input_pos,
            requirements: self.requirements,
        }
    }
}
impl<'src> Slice<RangeTo<usize>> for Input<'src> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        let src = self.src.slice(range);
        Self {
            // filename:self.filename,
            src,
            is_problem: self.is_problem,
            input_pos: self.input_pos,
            requirements: self.requirements,
        }
    }
}
impl<'src> Offset for Input<'src> {
    fn offset(&self, second: &Self) -> usize {
        self.src.offset(second.src)
    }
}
impl<'src> UnspecializedInput for Input<'src> {}
impl<'src> SpannedAst<'src> for Input<'src> {
    fn span(&self) -> Span {
        Span {
            start: self.input_pos,
            end: self.input_pos + self.input_len(),
            is_problem: self.is_problem,
        }
    }
}
impl<'src> Into<Span> for Input<'src> {
    fn into(self) -> Span {
        Span {
            start: self.input_pos,
            end: self.input_pos + self.input_len(),
            is_problem: self.is_problem,
        }
    }
}
// impl<'src> Into<std::ops::Range<usize>> for Input<'src> {
//     fn into(self) -> std::ops::Range<usize> {
//         std::ops::Range {
//             start: self.input_pos,
//             end: self.input_pos + self.input_len(),
//         }
//     }
// }
