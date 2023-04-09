pub mod lexer;
pub mod ast;

use ast::Stmt;
use enumset::EnumSet;
use lexer::Lexer;




use self::ast::{TypedList, Requirements};

use super::Error;
use super::tokens::{Token, TokenKind, KeywordToken, BinOpToken};

/// Parses PDDL 3.1 syntax
/// Based on https://github.com/jan-dolejsi/pddl-reference/blob/master/_citedpapers/pddl3bnf.pdf
/// 
/// Example:
/// ```rust
/// use pddl_rs::parser::pddl::{Parser, ast::Stmt};
/// let filename = "domain.pddl";
/// let code = std::fs::read_to_string(filename).unwrap();
/// let mut parser = Parser::new(code.as_str(), Some(filename));
/// for result in parser {
///     match result {
///         Some(Ok(Stmt::Domain(domain))) => println!("{:?}", domain),
///         Some(Ok(Stmt::Problem(problem))) => println!("{:?}", problem),
///         Some(Err(e)) => println!("{}", e),
///         None => println!("Done."),
///     }
/// }
/// ```

pub struct Parser<'a> {
    lexer: std::iter::Peekable<lexer::Lexer<'a>>,
    filename: Option<&'a str>,
    requirements: EnumSet<Requirements>,
}

impl<'a> Iterator for Parser<'a> {
    type Item = Result<Stmt<'a>, Error<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let None = self.lexer.peek() {
            None
        } else {
            let r = self.root();
            if r.is_err() {
                self.error_recover();
            }
            Some(r)
        }
    }
}

const EXPECTED_IDENTIFIER: &str = "Expected identifier.";
const EXPECTED_COLON:&str = "Expected ':'.";
const EXPECTED_OPEN_PARENTHESIS: &str = "Expected '('.";
const EXPECTED_CLOSE_PARENTHESIS: &str = "Expected matched ')'.";

#[macro_export]
macro_rules! expect {
    ($input:expr, {$($p:pat => $b:expr$(,)?)+}, $err:expr) => {{
        let filename = $input.filename.clone();
        match $input.lexer.next() {
            $($p => $b,)+
            Some(Ok(t)) => Err(Error::UnexpectedToken{t, suggestion:$err}),
            Some(Err(e)) => Err(e),
            None => Err(Error::UnexpectedEOF{filename, suggestion:$err})
        }}
    };
}

impl<'a> Parser<'a> {

    fn error_recover(&mut self) {

    }

    fn problem(&mut self) -> Result<Stmt<'a>, Error<'a>> {
        use TokenKind::{Keyword, Colon, Identifier, OpenParenthesis, CloseParenthesis};
        use KeywordToken::*;
        let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, "Expected domain name.")?;
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        let mut domain = None;
        let mut requirements = EnumSet::empty();
        let mut objects = Vec::new();
        let mut init = None;
        let mut goal = None;
        while self.lexer.next_if(|r| matches!(r, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            expect!(self, {Some(Ok(Token{kind:Colon,..})) => Ok(())}, EXPECTED_COLON)?;
            expect!(self, {
                Some(Ok(Token{kind:Keyword(Domain),..})) => Ok(domain = Some(expect!(self, {Some(Ok(Token{kind:Identifier(s),..}))=>Ok(s)}, EXPECTED_IDENTIFIER)?)),
                Some(Ok(Token{kind:Keyword(Requirements),..})) => Ok(requirements = self.requirements()?),
                Some(Ok(Token{kind:Keyword(Objects),..})) => Ok(objects = self.types()?),
                Some(Ok(Token{kind:Keyword(Init),..})) => Ok(init = Some(self.and()?)), // force it to use a vector of Expressions
                Some(Ok(Token{kind:Keyword(Goal),..})) => Ok(goal = Some(self.expr()?)),
            }, "Expected :domain, :requirements, :objects.")?;
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        let domain = domain.unwrap();
        let init = init.unwrap();
        let goal = goal.unwrap();
        Ok(Stmt::Problem(ast::Problem{name, domain, requirements, objects, init, goal}))
    }

    fn literal(&mut self, name:&'a str) -> Result<ast::Expr<'a>, Error<'a>> {
        use TokenKind::{Identifier, QuestionMark};
        let mut variables = Vec::new();
        const EXPECTED_VARIABLE: &str = "Expected variable.";
        match self.lexer.peek() {
            Some(Ok(Token{kind:QuestionMark,..})) => {
                while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..}))).is_some() {
                    variables.push(expect!(self, {
                        Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)
                    }, EXPECTED_IDENTIFIER)?)
                }
                Ok(ast::Expr::Literal { name, variables })
            },
            Some(Ok(Token{kind:Identifier(_),..})) => {
                while let Some(Ok(Token{kind:Identifier(s),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
                    variables.push(s);
                }
                Ok(ast::Expr::Literal { name, variables })
            },
            Some(Ok(t)) => Err(Error::UnexpectedToken {t:*t, suggestion: EXPECTED_VARIABLE }),
            Some(Err(e)) => Err(e.clone()),
            None => Err(Error::UnexpectedEOF{filename:self.filename, suggestion: EXPECTED_VARIABLE })
        }
    }

    fn not(&mut self) -> Result<ast::Expr<'a>, Error<'a>> {
        Ok(ast::Expr::Not(Box::new(self.expr()?)))
    }

    fn and(&mut self) -> Result<ast::Expr<'a>, Error<'a>> {
        use TokenKind::{OpenParenthesis};
        let mut group = Vec::new();
        while matches!(self.lexer.peek(), Some(Ok(Token{kind:OpenParenthesis,..}))) {
            group.push(self.expr()?)
        }
        Ok(ast::Expr::And(group))
    }

    fn expr(&mut self) -> Result<ast::Expr<'a>, Error<'a>> {
        use TokenKind::{BinOp, Identifier, OpenParenthesis, CloseParenthesis};
        use BinOpToken::{And, Not};
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..})) => Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = expect!(self, {
            Some(Ok(Token{kind:BinOp(And),..})) => self.and(),
            Some(Ok(Token{kind:BinOp(Not),..})) => self.not(),
            Some(Ok(Token{kind:Identifier(s),..})) => self.literal(s),
        }, "Expected expression.")?;
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        Ok(result)
    }

    fn action(&mut self) -> Result<ast::Action<'a>, Error<'a>> {
        use TokenKind::{Keyword, Identifier, QuestionMark, Colon, OpenParenthesis, CloseParenthesis};
        use KeywordToken::{Parameters, Precondition, Effect};
        let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
        let mut parameters = Vec::new();
        expect!(self, {Some(Ok(Token{kind:Colon,..}))=>Ok(())}, EXPECTED_COLON)?;
        expect!(self, {Some(Ok(Token{kind:Keyword(Parameters),..})) => Ok(())}, "Expected 'parameters'.")?;
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..})) => Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        while let Some(Ok(Token{kind:QuestionMark,..})) = self.lexer.peek() {
            parameters.push(self.typed_list_variable()?);
        }
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        let mut precondition = None;
        let mut effect = None;
        self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Colon,..})));
        if self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Keyword(Precondition),..}))).is_some() {
            precondition = Some(self.expr()?);
        }
        self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Colon,..})));
        if self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Keyword(Effect),..}))).is_some() {
            effect = Some(self.expr()?);
        }
        Ok(ast::Action{name, parameters, precondition, effect})
    }

    /// ```ebnf
    /// <functions-def> ::= (:functions <function typed list (atomic function skeleton)>)
    /// ```
    fn functions(&mut self) -> Result<(), Error<'a>> {
        Ok(())
    }

    /// ```ebnf
    /// <predicates-def> ::= (:predicates <atomic formula skeleton>+)
    /// ```
    fn predicates(&mut self) -> Result<Vec<ast::Predicate<'a>>, Error<'a>> {
        use TokenKind::{OpenParenthesis, Identifier, QuestionMark, CloseParenthesis};
        let mut predicates = Vec::new();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
            let mut variables = Vec::new();
            while let Some(Ok(Token{kind:QuestionMark,..})) = self.lexer.peek() {
                variables.push(self.typed_list_variable()?);
            }
            predicates.push(ast::Predicate{name, variables});
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        Ok(predicates)
    }

    fn typed_list_variable(&mut self) -> Result<TypedList<'a>, Error<'a>> {
        use TokenKind::{BinOp, QuestionMark, Identifier};
        use BinOpToken::Minus;
        let mut identifiers = Vec::new();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..}))).is_some() {
            identifiers.push(expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?);
        }
        let mut kind = None;
        // TODO: Both problem and domain specification uses typed_list, 
        // but it's possible to have domain with requirements and not problem. 
        // figure out how to deal with missing requirements for problem
        let has_minus = if let Some(Ok(Token{kind:BinOp(Minus),..})) = self.lexer.peek() { true } else { false};
        if self.requirements.contains(Requirements::Typing) || has_minus {
            expect!(self, {Some(Ok(Token{kind:BinOp(Minus),..})) => Ok(())}, ":typing is enabled - expected '-' at the end of typed list.")?;
            kind = Some(expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?);
        } else {
            
        }
        Ok(TypedList{identifiers, kind})
    }

    fn typed_list_name(&mut self) -> Result<TypedList<'a>, Error<'a>> {
        use TokenKind::{BinOp, Identifier};
        use BinOpToken::Minus;
        let mut identifiers = Vec::new();
        while let Some(Ok(Token{kind:Identifier(s),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
            identifiers.push(s);
        }
        let mut kind = None;
        let has_minus = if let Some(Ok(Token{kind:BinOp(Minus),..})) = self.lexer.peek() { true } else { false};
        if self.requirements.contains(Requirements::Typing) || has_minus {
            expect!(self, {Some(Ok(Token{kind:BinOp(Minus),..})) => Ok(())}, ":typing is enabled - expected '-' at the end of typed list.")?;
            kind = Some(expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?);
        }
        Ok(TypedList{identifiers, kind})
    }

    /// ```ebnf
    /// <constants-def> ::= (:constants <typed list (name)>)
    /// ```
    fn constants(&mut self) -> Result<(), Error<'a>> {
        Ok(())
    }

    /// ```ebnf
    /// <types-def> ::= (:types <typed list (name)>)
    /// ```
    fn types(&mut self) -> Result<Vec<TypedList<'a>>, Error<'a>> {
        use TokenKind::*;
        let mut types = Vec::new();
        while let Some(Ok(Token{kind:Identifier(_),..})) = self.lexer.peek() {
            types.push(self.typed_list_name()?);
        }
        Ok(types)
    }

    /// ```ebnf
    /// <require-def> ::= (:requirements <require-key>+)
    /// ```
    fn requirements(&mut self) -> Result<EnumSet<ast::Requirements>, Error<'a>> {
        use TokenKind::{Identifier, Colon};
        let mut r = EnumSet::empty();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Colon,..}))).is_some() {
            expect!(self, {
                Some(Ok(Token{kind:Identifier("strips"),..})) => Ok(r.insert(ast::Requirements::Strips)),
                Some(Ok(Token{kind:Identifier("typing"),..})) => Ok(r.insert(ast::Requirements::Typing)),
                Some(Ok(Token{kind:Identifier("negative-preconditions"),..})) => Ok(r.insert(ast::Requirements::NegativePreconditions)),
                Some(Ok(Token{kind:Identifier("disjunctive-preconditions"),..})) => Ok(r.insert(ast::Requirements::DisjunctivePreconditions)),
                Some(Ok(Token{kind:Identifier("action-costs"),..})) => Ok(r.insert(ast::Requirements::ActionCosts)),
                Some(Ok(Token{kind:Identifier("equality"),..})) => Ok(r.insert(ast::Requirements::Equality)),
                Some(Ok(Token{kind:Identifier("existential-preconditions"),..})) => Ok(r.insert(ast::Requirements::ExistentialPreconditions)),
                Some(Ok(Token{kind:Identifier("universal-preconditions"),..})) => Ok(r.insert(ast::Requirements::UniversalPreconditions)),
                Some(Ok(Token{kind:Identifier("quantified-preconditions"),..})) => Ok(r.insert(ast::Requirements::QuantifiedPreconditions)),
                Some(Ok(Token{kind:Identifier("conditional-effects"),..})) => Ok(r.insert(ast::Requirements::ConditionalEffects)),
                Some(Ok(Token{kind:Identifier("fluents"),..})) => Ok(r.insert(ast::Requirements::Fluents)),
                Some(Ok(Token{kind:Identifier("adl"),..})) => Ok(r.insert(ast::Requirements::ADL)),
                Some(Ok(Token{kind:Identifier("durative-actions"),..})) => Ok(r.insert(ast::Requirements::DurativeActions)),
                Some(Ok(Token{kind:Identifier("derived-predicates"),..})) => Ok(r.insert(ast::Requirements::DerivedPredicates)),
                Some(Ok(Token{kind:Identifier("timed-initial-literals"),..})) => Ok(r.insert(ast::Requirements::TimedInitialLiterals)),
                Some(Ok(Token{kind:Identifier("preferences"),..})) => Ok(r.insert(ast::Requirements::Preferences)),
                Some(Ok(Token{kind:Identifier("constraints"),..})) => Ok(r.insert(ast::Requirements::Constraints)),
            }, "Expected requirements.")?;
        }
        self.requirements = r;
        Ok(r)
    }

    /// ```ebnf
    /// <domain> ::= (define (domain <name>) 
    ///             [<require-def>]
    ///             [<types-def>] (* if :typing *)
    ///             [<constants-def>]
    ///             [<predicates-def>]
    ///             [<functions-def>] (* if :fluents *)
    ///             [<constraints>] 
    ///             <structure-def>*)
    /// ```
    fn domain(&mut self) -> Result<Stmt<'a>, Error<'a>> {
        use TokenKind::{Keyword, Colon, Identifier, OpenParenthesis, CloseParenthesis};
        use KeywordToken::*;
        let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, "Expected domain name.")?;
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        let mut requirements = EnumSet::empty();
        let mut types = Vec::new();
        let mut predicates = Vec::new();
        let mut actions = Vec::new();
        while self.lexer.next_if(|r| matches!(r, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            expect!(self, {Some(Ok(Token{kind:Colon,..})) => Ok(())}, EXPECTED_COLON)?;
            expect!(self, {
                Some(Ok(Token{kind:Keyword(Requirements),..})) => Ok(requirements = self.requirements()?),
                Some(Ok(Token{kind:Keyword(Types),..})) => Ok(types = self.types()?),
                // Some(Ok(Token{kind:Keyword(Constants),..})) => Ok(constants = self.constants()?),
                Some(Ok(Token{kind:Keyword(Predicates),..})) => Ok(predicates = self.predicates()?),
                // Some(Ok(Token{kind:Keyword(Functions),..})) => Ok(functions = self.functions()?),
                // Some(Ok(Token{kind:Keyword(Constraints),..})) => Ok(constraints = self.constraints()?),
                Some(Ok(Token{kind:Keyword(Action),..})) => Ok(actions.push(self.action()?)),
            }, "Expected :requirements, :types, :constants :predicates, :functions, :constraints: or :action.")?;
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        Ok(Stmt::Domain(ast::Domain{name, requirements, types, predicates, actions}))
    }
    
    fn root(&mut self)-> Result<Stmt<'a>, Error<'a>> {
        use KeywordToken::*;
        use TokenKind::*;

        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..})) => Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        expect!(self, {Some(Ok(Token{kind:Keyword(Define),..})) => Ok(())}, "Expected 'define'.")?;
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..})) => Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let body = expect!(self, {
            Some(Ok(Token{kind:Keyword(Domain),..})) => self.domain(),
            Some(Ok(Token{kind:Keyword(Problem),..})) => self.problem()
        }, "Expected 'domain' or 'problem'.")?;
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        Ok(body)
    }

    pub fn new(code:&'a str, filename:Option<&'a str>) -> Self {
        let lexer = Lexer::<'a>::new(code, filename).peekable();
        Self{lexer, filename, requirements:EnumSet::empty()}
    }
}

#[cfg(test)]
mod tests {
    use enumset::{EnumSet, enum_set};

    // use crate::htn::parser::{Parser, Error, statement::{Stmt, StmtKind, Block}, expression::{Expr, ExprKind}, tokens::{Span, Literal::*}};
    use super::Parser;
    use super::ast::{Stmt, Domain, Problem, Requirements, TypedList, Predicate, Action, Expr};
    #[test]
    fn test_domain() {
        let code = "(define (domain test) (:requirements :strips :typing) (:types hand - object water - beverage) (:predicates (warm ?o - object)) (:action test :parameters (?h - hand ?b - beverage) :precondition (cold ?h) :effect (warm ?b)))";
        let mut parser = Parser::new(code, None);
        assert_eq!(parser.next(), Some(Ok(Stmt::Domain(Domain{
            name:"test", 
            requirements:enum_set!(Requirements::Strips | Requirements::Typing), 
            types:vec![TypedList{identifiers:vec!["hand"], kind:Some("object")},
                       TypedList{identifiers:vec!["water"], kind:Some("beverage")}], 
            predicates:vec![Predicate{name:"warm", variables:vec![TypedList{identifiers:vec!["o"], kind:Some("object")}]}], 
            actions:vec![Action{
                name:"test", 
                parameters:vec![TypedList{identifiers:vec!["h"], kind:Some("hand")}, TypedList{identifiers:vec!["b"], kind:Some("beverage")}],
                precondition:Some(Expr::Literal { name: "cold", variables: vec!["h"] }),
                effect:Some(Expr::Literal { name: "warm", variables: vec!["b"] })
            }]
        }))));
        assert_eq!(parser.next(), None);
    }

    #[test]
    fn test_problem() {
        let code = "(define (problem test) (:domain barman) (:objects shaker1 - shaker) (:init (ontable shaker1)) (:goal (and (contains shot1 cocktail1))))";
        let mut parser = Parser::new(code, None);
        assert_eq!(parser.next(), Some(Ok(Stmt::Problem(Problem{
            name:"test",
            domain:"barman",
            requirements: EnumSet::empty(),
            objects:vec![TypedList{identifiers:vec!["shaker1"], kind:Some("shaker")}],
            init: Expr::And(vec![Expr::Literal { name: "ontable", variables: vec!["shaker1"] }]),
            goal: Expr::And(vec![Expr::Literal { name: "contains", variables: vec!["shot1", "cocktail1"] }])
        }))))
    }
    
}