
pub mod parser;
pub mod compiler;
pub mod search;

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
    Type,
    TypedList,
    StructureDef,
    Name,
    Variable,
    Literal,
    AtomicFormula,
    FunctionTerm,
    Parenthesis,
    UnclosedParenthesis(usize), // usize-position of matched openning '('
    PreconditionExpression,
    Effect,
    FluentExpression,
    GD, 
    Term, 
    FunctionTypedList,
    // Compiler Errors
    MissmatchedDomain(&'src str),
    UndefinedType,
    ExpectedVariable,
    ExpectedName,
    UndeclaredVariable,
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
        use ErrorKind::*;
        let label = ariadne::Label::new((filename, self.range.clone()));
        match self.kind {
            Nom(e) => label.with_message(format!("Parser {:?} failed.", e)),
            UnsetRequirement(r) => label.with_message(format!("Unset requirements {}.", r.into_iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "))),
            Tag(name) => label.with_message(format!("Expected keyword {}.", name)),
            Many1(name) => label.with_message(format!("Expected one or more {}.", name)),
            FunctionType => todo!(),
            Type => label.with_message("Expected Type."),
            TypedList => label.with_message("Expected Typed List."),
            StructureDef => label.with_message("Expected actions."),
            Name => label.with_message("Expected name."),
            Variable => label.with_message("Expected variable."),
            Parenthesis => label.with_message("Expected '('."),
            UnclosedParenthesis(_) => label.with_message("Expected ')'."),
            PreconditionExpression => label.with_message("Expected precondition expression."),
            Effect => todo!(),
            FluentExpression => todo!(),
            FunctionTerm => label.with_message("Expected function term."),
            Literal => label.with_message("Expected litera."),
            AtomicFormula => label.with_message("Expected atomic formula."),
            GD => label.with_message("Expected GD."),
            Term => label.with_message("Expected name, variable, or function term if :object-fluents is set."),
            FunctionTypedList => todo!(),
            MissmatchedDomain(name) => label.with_message(format!("Problem and Domain names missmatch. Expected {}.", name)),
            UndefinedType => label.with_message("Domain :types() does not declare this type."),
            ExpectedVariable => label.with_message("Expected variable."),
            UndeclaredVariable => label.with_message("Undeclared variable."),
            ExpectedName => label.with_message("Expected name."),
        }
    }
    pub fn report(&self, filename:&'static str) -> ariadne::Report<'src, (&'src str, Range<usize>)> {
        use ErrorKind::*;
        let report = ariadne::Report::<'src, (&'src str, Range<usize>)>::build(ariadne::ReportKind::Error, filename, self.range.start);
        let mut report = report.with_message("Parse error");
        report.add_label(self.make_label(filename));
        match self.kind {
            UnclosedParenthesis(pos) => report.add_label(ariadne::Label::new((filename, pos..(pos+1))).with_message("Matching '('")),
            _ => ()
        }
        let mut cerror = self;
        while let Some(e) = cerror.chain.as_ref() {
            cerror = e.as_ref();
            report.add_label(cerror.make_label(filename));
            match cerror.kind {
                UnclosedParenthesis(pos) => report.add_label(ariadne::Label::new((filename, pos..(pos+1))).with_message("Matching '('")),
                _ => ()
            }
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