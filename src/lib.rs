//! PDDL Parsing library based on [Daniel L. Kovacs' BNF definition](http://pddl4j.imag.fr/repository/wiki/BNF-PDDL-3.1.pdf)
//! BNF Definition of PDDL. Future plans include adding planning algorithms to
//! reflect [PDDL4J library](https://github.com/pellierd/pddl4j)
//!
//! From PDDL4J's Readme:
//!
//! > PDDL was originally developed by Drew McDermott and the 1998 planning
//! competition committee. It was inspired by the need to encourage the
//! empirical comparison of planning systems and the exchange of planning
//! benchmarks within the community. Its development improved the communication
//! of research results and triggered an explosion in performance, expressivity
//! and robustness of planning systems.
//! >
//!> PDDL has become a de facto standard language for describing planning
//! domains, not only for the competition but more widely, as it offers an
//! opportunity to carry out empirical evaluation of planning systems on a
//! growing collection of generally adopted standard benchmark domains. The
//! emergence of a language standard will have an impact on the entire field,
//! influencing what is seen as central and what peripheral in the development
//! of planning systems.
//!
//! ## Example
//!
//! ```rust
//! use std::fs;
//! use pddl_rs::{compiler::{CompiledProblem, compile_problem, Optimization}, search::{a_star, AstarInternals}, parser::{parse_domain, parse_problem, ast::Action}, ReportPrinter};
//! let domain_filename = "sample_problems/simple_domain.pddl";
//! let problem_filename = "sample_problems/simple_problem.pddl";
//! let domain_src = fs::read_to_string(domain_filename).unwrap();
//! let domain = parse_domain(&domain_src).unwrap_or_print_report(domain_filename, &domain_src);
//! let problem_src = fs::read_to_string(problem_filename).unwrap();
//! let problem = parse_problem(&problem_src, domain.requirements).unwrap_or_print_report(problem_filename, &problem_src);
//! let c_problem = compile_problem(&domain, &problem, Optimization::all()).unwrap_or_print_report(problem_filename, &problem_src);
//! println!("Compiled problem needs {} bits of memory and uses {} actions.", c_problem.memory_size, c_problem.actions.len());
//! let mut args = AstarInternals::new();
//! if let Some(solution) = a_star(&c_problem, &mut args) {
//!     println!("Solution is {} actions long.", solution.len());
//!     for action_id in &solution {
//!         let action = c_problem.actions.get(*action_id).unwrap();
//!         println!("\t{}{:?}", match &domain.actions[action.domain_action_idx]{ Action::Basic(ba)=>ba.name.1, _=> todo!() }, action.args.iter().map(|(_, s)| *s).collect::<Vec<&str>>());
//! }
//! }
//! ```
//!
//! The code is avilable on [GitHub](https://github.com/Hexorg/pddl_rs)
//!
pub mod compiler;
pub mod parser;
pub mod search;

/// Used to represent domain requirements.
pub use enumset::EnumSet;
pub use parser::ast::Requirement;
use std::ops::Range;

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
    UnreadPredicate(&'src str),
    UndeclaredVariable,
}

/// Parser and Compiler Error that uses Adriane to generate a pretty report and point at the right
/// PDDL formatting locations.
#[derive(PartialEq, Clone, Debug)]
pub struct Error<'src> {
    input: Option<&'src str>,
    kind: ErrorKind<'src>,
    chain: Option<Box<Self>>,
    range: Range<usize>,
}

impl<'src> nom::error::ParseError<parser::Input<'src>> for Error<'src> {
    fn from_error_kind(input: parser::Input<'src>, kind: nom::error::ErrorKind) -> Self {
        Self {
            input: Some(input.src),
            kind: ErrorKind::Nom(kind),
            chain: None,
            range: parser::ast::SpannedAst::range(&input),
        }
    }

    fn append(input: parser::Input<'src>, kind: nom::error::ErrorKind, other: Self) -> Self {
        Self {
            input: Some(input.src),
            kind: ErrorKind::Nom(kind),
            chain: Some(Box::new(other)),
            range: parser::ast::SpannedAst::range(&input),
        }
    }
}

pub trait ReportPrinter<O> {
    fn unwrap_or_print_report(self, filename:&str, source:&str) -> O;
} 

impl<'src, O> ReportPrinter<O> for Result<O, Error<'src>> {
    fn unwrap_or_print_report(self, filename:&str, source:&str) -> O {
        match self {
            Err(e) => {
                e.report(filename)
                    .eprint((filename, ariadne::Source::from(source))).unwrap();
                panic!()
            }
            Ok(cd) => cd,
        }
    }
}

impl<'src> Error<'src> {
    pub fn unset_requirement(
        input: parser::Input<'src>,
        requirements: EnumSet<Requirement>,
    ) -> Self {
        Self {
            input: Some(input.src),
            kind: ErrorKind::UnsetRequirement(requirements),
            chain: None,
            range: parser::ast::SpannedAst::range(&input),
        }
    }
}

impl<'src> Error<'src> {
    fn make_label(&self, filename: &'src str) -> ariadne::Label<(&'src str, Range<usize>)> {
        use ErrorKind::*;
        let label = ariadne::Label::new((filename, self.range.clone()));
        match self.kind {
            Nom(e) => label.with_message(format!("Parser {:?} failed.", e)),
            UnsetRequirement(r) => label.with_message(format!(
                "Unset requirements {}.",
                r.into_iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            )),
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
            Term => label.with_message(
                "Expected name, variable, or function term if :object-fluents is set.",
            ),
            FunctionTypedList => todo!(),
            MissmatchedDomain(name) => label.with_message(format!(
                "Problem and Domain names missmatch. Expected {}.",
                name
            )),
            UndefinedType => label.with_message("Domain :types() does not declare this type."),
            UndeclaredVariable => label.with_message("Undeclared variable."),
            UnreadPredicate(v) => label.with_message(format!("Unused Predicate call: {:?}", v))
        }
    }
    pub fn report<'fname>(
        &self,
        filename: &'src str,
    ) -> ariadne::Report<'src, (&'src str, Range<usize>)> {
        use ErrorKind::*;
        let report = ariadne::Report::<'src, (&'src str, Range<usize>)>::build(
            ariadne::ReportKind::Error,
            filename,
            self.range.start,
        );
        let mut report = report.with_message("Parse error");
        report.add_label(self.make_label(filename));
        match self.kind {
            UnclosedParenthesis(pos) => report.add_label(
                ariadne::Label::new((filename, pos..(pos + 1))).with_message("Matching '('"),
            ),
            _ => (),
        }
        let mut cerror = self;
        while let Some(e) = cerror.chain.as_ref() {
            cerror = e.as_ref();
            report.add_label(cerror.make_label(filename));
            match cerror.kind {
                UnclosedParenthesis(pos) => report.add_label(
                    ariadne::Label::new((filename, pos..(pos + 1))).with_message("Matching '('"),
                ),
                _ => (),
            }
        }
        report.finish()
    }
}

#[cfg(test)]
pub mod lib_tests {
    use ariadne::Source;
    use enumset::EnumSet;
    use parser::{parse_domain, parse_problem};

    use crate::{parser, ReportPrinter, compiler::{compile_problem, Optimization}};

    pub fn load_repo_pddl<'src>(
        domain_filename: &'static str,
        problem_filename: &'static str,
    ) -> (String, String) {
        use std::{env, fs, path::Path};
        let workspace_path = match env::var("GITHUB_WORKSPACE") {
            Ok(path) => path,
            Err(_) => match env::var("CARGO_MANIFEST_DIR") {
                Ok(path) => path,
                Err(_) => String::from("."),
            },
        };
        let p = Path::new(&workspace_path);
        let domain_src = fs::read_to_string(p.join(domain_filename)).unwrap();
        let problem_src = fs::read_to_string(p.join(problem_filename)).unwrap();
        (domain_src, problem_src)
    }

    #[test]
    fn test_domain() -> std::io::Result<()> {
        let filename = "problem_5_10_7.pddl";
        // let code = std::fs::read_to_string(filename).unwrap();
        let code = "(define (problem test) (:domain td) (:goal (end)))";
        match parser::parse_problem(code, EnumSet::EMPTY) {
            Ok(problem) => println!("{:?}", problem),
            Err(e) => {
                e.report(&filename).eprint((filename, Source::from(code)))?;
            }
        }
        Ok(())
    }

    #[test]
    #[ignore = "Benchmark test to run manually"]
    fn benchmark() {
        let domain_filename = "sample_problems/barman/domain.pddl";
        let problem_filename = "sample_problems/barman/problem_5_10_7.pddl";
        let (domain_src, problem_src) = load_repo_pddl(domain_filename, problem_filename);
        let domain = parse_domain(&domain_src).unwrap_or_print_report(domain_filename, &domain_src);
        let problem = parse_problem(&problem_src, domain.requirements).unwrap_or_print_report(problem_filename, &problem_src);
        let runs = [Optimization::none(), Optimization::all()];
        for optimizations in runs {
            let c_problem = compile_problem(&domain, &problem, optimizations).unwrap_or_print_report(problem_filename, &problem_src);
            println!("At {:?}: {}.{} uses {} bits of memory and has {} actions.", optimizations, domain.name.1, problem.name.1, c_problem.memory_size, c_problem.actions.len());
        }
    }
}
