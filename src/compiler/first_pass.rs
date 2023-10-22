use crate::{Error, ErrorKind, compiler::SpannedAst};

use super::*;

pub struct FirstPassData<'src> {
    pub preprocess: PreprocessData<'src>

}

#[derive(Debug, Default)]
pub struct Inertia<'src> {
    wants_positive: Vec<Name<'src>>,
    wants_negative: Vec<Name<'src>>,
    provides_positive: Vec<Name<'src>>,
    provides_negative: Vec<Name<'src>>,
}

pub fn first_pass<'src>(preprocess:PreprocessData<'src>, domain:&Domain<'src>, problem:&Problem<'src>) -> Result<FirstPassData<'src>, Error<'src>> {
    Ok(FirstPassData {preprocess})
}