
pub mod parser;
pub mod compiler;

use std::ops::Range;
pub use enumset::EnumSet;
pub use parser::ast::Requirement;

#[derive(PartialEq, Clone, Copy, Debug)]
enum ErrorKind<'src> {
    Nom(nom::error::ErrorKind),
    UnsetRequirement(EnumSet<Requirement>),
    Tag(&'src str),
    Many1(&'static str),
    FunctionType,
    Name,
    Variable,
    Parenthesis,
    UnclosedParenthesis,
    PreconditionExpression,
    Effect,
    FluentExpression,
    GD, 
    Term, 
    FunctionTypedList,
    // Compiler Errors
    MissmatchedDomain(&'src str),
}

#[derive(PartialEq, Clone, Debug)]
pub struct Error<'src> {
    input:Option<&'src str>,
    kind:ErrorKind<'src>,
    chain:Option<Box<Self>>,
    range: Range<usize>,
}

impl<'src> nom::error::ParseError<parser::input::Input<'src>> for Error<'src> {
    fn from_error_kind(input: parser::input::Input<'src>, kind: nom::error::ErrorKind) -> Self {
        Self{input:Some(input.src), kind:ErrorKind::Nom(kind), chain:None, range:parser::ast::SpannedAst::range(&input)}
    }

    fn append(input: parser::input::Input<'src>, kind: nom::error::ErrorKind, other: Self) -> Self {
        Self{input:Some(input.src), kind:ErrorKind::Nom(kind), chain:Some(Box::new(other)), range:parser::ast::SpannedAst::range(&input)}
    }
}

impl<'src> Error<'src> {
    pub fn unset_requirement(input:parser::input::Input<'src>, requirements:EnumSet<Requirement>) -> Self {
        Self{input:Some(input.src), kind:ErrorKind::UnsetRequirement(requirements), chain:None, range:parser::ast::SpannedAst::range(&input)}
    }
}

impl<'src> Error<'src> {
    fn make_label(&self, filename:&'static str) -> ariadne::Label<(&'src str, Range<usize>)> {
        let label = ariadne::Label::new((filename, self.range.clone()));
        match self.kind {
            ErrorKind::Nom(_) => todo!(),
            ErrorKind::UnsetRequirement(r) => label.with_message(format!("Unset requirements {}.", r.into_iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "))),
            ErrorKind::Tag(name) => label.with_message(format!("Expected keyword {}.", name)),
            ErrorKind::Many1(name) => label.with_message(format!("Expected one or more {}.", name)),
            ErrorKind::FunctionType => todo!(),
            ErrorKind::Name => todo!(),
            ErrorKind::Variable => todo!(),
            ErrorKind::Parenthesis => label.with_message("Expected '('."),
            ErrorKind::UnclosedParenthesis => label.with_message("Expected ')'."),
            ErrorKind::PreconditionExpression => label.with_message("Expected precondition expression."),
            ErrorKind::Effect => todo!(),
            ErrorKind::FluentExpression => todo!(),
            ErrorKind::GD => label.with_message("Expected GD."),
            ErrorKind::Term => label.with_message("Expected name, variable, or function term if :object-fluents is set."),
            ErrorKind::FunctionTypedList => todo!(),
            ErrorKind::MissmatchedDomain(name) => label.with_message(format!("Problem and Domain names missmatch. Expected {}.", name)),
        }
    }
    pub fn report(&self, filename:&'static str) -> ariadne::Report<'src, (&'src str, Range<usize>)> {
        let report = ariadne::Report::<'src, (&'src str, Range<usize>)>::build(ariadne::ReportKind::Error, filename, self.range.start);
        let mut report = report.with_message("Parse error");
        report.add_label(self.make_label(filename));
        let mut cerror = self;
        while let Some(e) = cerror.chain.as_ref() {
            cerror = e.as_ref();
            report.add_label(cerror.make_label(filename));
        }
        report.finish()
    }
}


#[cfg(test)]
mod tests {
    use ariadne::Source;
    use enumset::EnumSet;

    use crate::parser::{self, ast::Requirement};

    #[test]
    fn test_domain() {
        let filename = "problem_5_10_7.pddl";
        // let code = std::fs::read_to_string(filename).unwrap();
        let code = "(define (problem test) (:domain td) (:goal (end)))";
        match parser::parse_problem(code,  EnumSet::EMPTY) {
            Ok(problem) => println!("{:?}", problem),
            Err(e) => {e.report(&filename).eprint((filename, Source::from(code)));},
        }
        // let t:Option<Result<(), ()>> = Some(Err(()));
        // let t = t.and_then(|r| r.or_else(|e| return Some(Err(e))));
        // let mut parser = parser::Parser::new(code.as_str(), Some(filename));
        // match parser.next() {
        //     Some(Ok(s)) => println!("{:?}", s),
        //     Some(Err(e)) => { println!("{}", e); assert!(false); },
        //     None => assert!(false),
        // }
    }
}