use enumset::EnumSet;
use std::{str::{CharIndices, Chars}, ops::{RangeFrom, RangeTo}};
use nom::{InputLength, InputIter, InputTake, UnspecializedInput, Compare, Slice, Offset};
use super::ast::{Requirement, SpannedAst};


#[derive(Clone, PartialEq, Debug)]
pub struct Input<'src> {
    pub src:&'src str,
    pub input_pos:usize,
    pub requirements:EnumSet<Requirement>
}
impl<'src> Input<'src> {
    pub fn new(src: &'src str) -> Self {
        Self{src, input_pos:0, requirements:EnumSet::EMPTY}
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
        P: Fn(Self::Item) -> bool {
        self.src.position(predicate)
    }

    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        self.src.slice_index(count)
    }
}
impl<'src> InputTake for Input<'src> {
    fn take(&self, count: usize) -> Self {
        let src = &self.src[..count];
        Self{src, input_pos:self.input_pos, requirements:self.requirements}
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.src.split_at(count);
        let prefix = Self{src:prefix, input_pos:self.input_pos, requirements:self.requirements};
        let suffix = Self{src:suffix, input_pos:self.input_pos+count, requirements:self.requirements};
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
        let input_pos = self.input_pos+range.start;
        let src = self.src.slice(range);
        Self{src, input_pos, requirements:self.requirements}
    }
}
impl<'src> Slice<RangeTo<usize>> for Input<'src> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        let src = self.src.slice(range);
        Self{src, input_pos:self.input_pos, requirements:self.requirements}
    }
}
impl<'src> Offset for Input<'src> {
    fn offset(&self, second: &Self) -> usize {
        self.src.offset(second.src)
    }
}
impl<'src> UnspecializedInput for Input<'src> {

}
impl<'src> SpannedAst for Input<'src> {
    fn range(&self) -> std::ops::Range<usize> {
        std::ops::Range{start:self.input_pos, end:self.input_pos+self.input_len()}
    }
}
impl<'src> Into<std::ops::Range<usize>> for Input<'src> {
    fn into(self) -> std::ops::Range<usize> {
        std::ops::Range{start:self.input_pos, end:self.input_pos+self.input_len()}
    }
}
