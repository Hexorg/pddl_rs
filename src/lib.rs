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
//! use std::path::PathBuf;
//! use pddl_rs::{Sources, Objects, search::{a_star, AstarInternals}};
//! let domain_filename = PathBuf::from("sample_problems/simple_domain.pddl");
//! let problem_filename = PathBuf::from("sample_problems/simple_problem.pddl");
//! let sources = Sources::load(domain_filename, problem_filename);
//! let (domain, problem) = sources.parse();
//! let c_problem = sources.compile(&domain, &problem);
//! println!("Compiled problem needs {} bits of memory and uses {} actions.", c_problem.memory_size, c_problem.actions.len());
//! let mut args = AstarInternals::new(&c_problem.action_graph);
//! if let Some(solution) = a_star(&c_problem, Some(&domain), Some(&problem), &mut args) {
//!     println!("Solution is {} actions long.", solution.len());
//!     for action_id in &solution {
//!         let action = c_problem.actions.get(*action_id as usize).unwrap();
//!         println!("\t{}{:?}", domain.actions[action.domain_action_idx as usize].name(), action.args.iter().map(|(row, col)| problem.objects.get_object_name(*row,*col).1).collect::<Vec<&str>>());
//! }
//! }
//! ```
//!
//! The code is avilable on [GitHub](https://github.com/Hexorg/pddl_rs)
//!
pub mod compiler;
pub mod parser;
pub mod search;

use ariadne::Cache;
use compiler::{compile_problem, CompiledProblem};
// use compiler::{Span, Input};
/// Used to represent domain requirements.
pub use enumset::EnumSet;
use parser::{ast::{span::Span}, parse_domain, parse_problem};
pub use parser::ast::{span::SpannedAst, Requirement, Domain, Problem};
use std::{ops::Range, path::PathBuf};

#[derive(PartialEq, Clone, Copy, Debug)]
enum ErrorKind {
    Nom(nom::error::ErrorKind),
    UnsetRequirement(EnumSet<Requirement>),
    Tag(&'static str),
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
    MissmatchedDomain,
    UndefinedType,
    UndefinedVariable,
    UndefinedPredicate,
    UndefinedObject,
    ExpectedName,
    ExpectedVariable,
    DuplicateType,
    DuplicatePredicate,
    DuplicateObject,
    FirstDefinedHere,
    UnmetGoal,
    UnmetPredicate,
}

/// Parser and Compiler Error that uses Adriane to generate a pretty report and point at the right
/// PDDL formatting locations.
#[derive(PartialEq, Clone, Debug)]
pub struct Error {
    span: Span,
    kind: ErrorKind,
    chain: Option<Box<Self>>,
}

impl<'src> nom::error::ParseError<parser::Input<'src>> for Error {
    fn from_error_kind(input: parser::Input<'src>, kind: nom::error::ErrorKind) -> Self {
        let len = input
            .src
            .char_indices()
            .find(|(_, c)| c.is_ascii_whitespace())
            .and_then(|(p, _)| Some(p))
            .unwrap_or(0);
        let span = Span {
            start: input.input_pos,
            end: input.input_pos + len,
            is_problem: input.is_problem,
        };
        Self {
            kind: ErrorKind::Nom(kind),
            chain: None,
            span,
        }
    }

    fn append(input: parser::Input<'src>, kind: nom::error::ErrorKind, other: Self) -> Self {
        Self {
            kind: ErrorKind::Nom(kind),
            chain: Some(Box::new(other)),
            span: SpannedAst::span(&input),
        }
    }
}

impl From<Error> for Vec<Error> {
    fn from(value: Error) -> Self {
        vec![value]
    }
}

pub struct Sources {
    pub domain_path: PathBuf,
    pub problem_path: PathBuf,
    pub domain_ad: ariadne::Source,
    pub problem_ad: ariadne::Source,
    pub domain_src: String,
    pub problem_src: String,
}

impl Sources {
    pub fn load(domain_path: PathBuf, problem_path: PathBuf) -> Self {
        let domain_src = std::fs::read_to_string(domain_path.to_str().unwrap()).unwrap();
        let problem_src = std::fs::read_to_string(problem_path.to_str().unwrap()).unwrap();
        let domain_ad = ariadne::Source::from(domain_src.clone());
        let problem_ad = ariadne::Source::from(problem_src.clone());
        Self {
            domain_path,
            problem_path,
            domain_src,
            problem_src,
            domain_ad,
            problem_ad,
        }
    }

    pub fn parse(&self) -> (Domain, Problem) {
        let mut domain = parse_domain(&self.domain_src).unwrap_or_print_report(self);
        let mut problem =
            parse_problem(&self.problem_src, domain.requirements).unwrap_or_print_report(self);
        (domain, problem)
    }

    pub fn compile<'ast, 'src>(
        &self,
        domain: &'ast Domain<'src>,
        problem: &'ast Problem<'src>,
    ) -> CompiledProblem<'ast, 'src>
    where
        'ast: 'src,
    {
        compile_problem(domain, problem, self.domain_path.clone(), self.problem_path.clone()).unwrap_or_print_report(self)
    }
}

impl Cache<&str> for &Sources {
    fn fetch(&mut self, id: &&str) -> Result<&ariadne::Source, Box<dyn std::fmt::Debug + '_>> {
        if Some(*id) == self.domain_path.to_str() {
            Ok(&self.domain_ad)
        } else if Some(*id) == self.problem_path.to_str() {
            Ok(&self.problem_ad)
        } else {
            panic!()
        }
    }

    fn display<'a>(&self, id: &'a &str) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(*id))
    }
}

pub trait ReportPrinter<O> {
    fn unwrap_or_print_report(self, sources: &Sources) -> O;
}

impl<'src, O> ReportPrinter<O> for Result<O, Vec<Error>> {
    fn unwrap_or_print_report(self, sources: &Sources) -> O {
        match self {
            Err(vec) => {
                for e in vec {
                    let filename = match e.span.is_problem {
                        true => &sources.problem_path,
                        false => &sources.domain_path,
                    };
                    e.report(filename.to_str().unwrap())
                        .eprint(sources)
                        .unwrap();
                }
                panic!()
            }
            Ok(cd) => cd,
        }
    }
}

impl Error {
    pub fn unset_requirement(input: parser::Input, requirements: EnumSet<Requirement>) -> Self {
        Self {
            kind: ErrorKind::UnsetRequirement(requirements),
            chain: None,
            span: SpannedAst::span(&input),
        }
    }
}

impl Error {
    fn make_label<'fname>(
        &self,
        filename: &'fname str,
    ) -> ariadne::Label<(&'fname str, Range<usize>)> {
        use ErrorKind::*;
        let label = ariadne::Label::new((filename, self.span.into()));
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
            DuplicateType => label.with_message("Duplicate type."),
            DuplicateObject => label.with_message("Duplicate object."),
            DuplicatePredicate => label.with_message("Duplicate predicate."),
            FirstDefinedHere => label.with_message("First defined here."),
            MissmatchedDomain => label.with_message(format!("Problem and Domain names missmatch.")),
            ExpectedName => label.with_message("Expected name."),
            ExpectedVariable => label.with_message("Expected variable."),
            UndefinedType => label.with_message("Domain :types() does not declare this type."),
            UndefinedVariable => label.with_message("Undefined variable."),
            UndefinedPredicate => label.with_message("Undefined predicate."),
            UndefinedObject => label.with_message("Undefined object."),
            UnmetGoal => label.with_message("Problem goal can not be met."),
            UnmetPredicate => label.with_message("Predicate is impossible to satisfy."),
        }
    }
    pub fn report<'fname>(
        &self,
        filename: &'fname str,
    ) -> ariadne::Report<(&'fname str, Range<usize>)> {
        use ErrorKind::*;
        let report = ariadne::Report::<(&str, Range<usize>)>::build(
            ariadne::ReportKind::Error,
            filename,
            self.span.start,
        );
        let mut report = match self.kind {
            MissmatchedDomain | UndefinedType | ExpectedName => report.with_message("Domain Error"),
            _ => report.with_message("Parser Error"),
        };
        report.add_label(self.make_label(filename));
        match self.kind {
            UnclosedParenthesis(pos) => report.add_label(
                ariadne::Label::new((filename, pos..pos + 1)).with_message("Matching '('"),
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
    use parser::{parse_domain, parse_problem};

    use crate::{compiler::compile_problem, parser, ReportPrinter, Sources};

    pub fn load_repo_pddl<'src>(
        domain_filename: &'static str,
        problem_filename: &'static str,
    ) -> Sources {
        use std::{env, path::Path};
        let workspace_path = match env::var("GITHUB_WORKSPACE") {
            Ok(path) => path,
            Err(_) => match env::var("CARGO_MANIFEST_DIR") {
                Ok(path) => path,
                Err(_) => String::from("."),
            },
        };
        let p = Path::new(&workspace_path);
        Sources::load(p.join(domain_filename), p.join(problem_filename))
    }

    #[test]
    #[ignore = "Benchmark test to run manually"]
    fn benchmark() {
        let domain_filename = "sample_problems/barman/domain.pddl";
        let problem_filename = "sample_problems/barman/problem_5_10_7.pddl";
        for _ in 0..10000 {
            let sources = load_repo_pddl(domain_filename, problem_filename);
            let domain = parse_domain(&sources.domain_src).unwrap_or_print_report(&sources);
            let problem = parse_problem(&sources.problem_src, domain.requirements)
                .unwrap_or_print_report(&sources);
            let _c_problem = compile_problem(&domain, &problem, sources.domain_path.clone(), sources.problem_path.clone()).unwrap_or_print_report(&sources);
            // println!("At {:?}: {}.{} uses {} bits of memory and has {} actions.", optimizations, domain.name.1, problem.name.1, c_problem.memory_size, c_problem.actions.len());
        }
    }
}
