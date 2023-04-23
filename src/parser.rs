pub mod tokens;
pub mod lexer;
pub mod ast;

use ast::Stmt;
use enumset::{EnumSet, enum_set};
use lexer::Lexer;


use self::ast::*;

use tokens::{Token, Span, TokenKind, KeywordToken, OpToken, Literal};


use std::num::{ParseFloatError, ParseIntError};

#[derive(PartialEq, Clone, Debug)]
pub enum Error<'a> {
    OmitedRequiredStatement{t:Token<'a>, suggestion:&'static str},
    UnsetRequirement{t:Token<'a>, requirement: Requirements},
    UnexpectedToken{t:Token<'a>, suggestion:&'static str},
    UnexpectedEOF{filename:Option<&'a str>, suggestion:&'static str},
    UnexpectedCharacter{filename:Option<&'a str>, span:Span, line: &'a str},
    ParseFloatError{filename:Option<&'a str>, span:Span, line: &'a str, source:ParseFloatError},
    ParseIntError{filename:Option<&'a str>, span:Span, line: &'a str, source:ParseIntError}
}

impl<'a> std::error::Error for Error<'a> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::OmitedRequiredStatement{..} |
            Self::UnsetRequirement{..} |
            Self::UnexpectedToken{..} |
            Self::UnexpectedEOF{..} |
            Self::UnexpectedCharacter{..} => None,
            Self::ParseFloatError{source,..} => Some(source),
            Self::ParseIntError{source,..} => Some(source),
        }
    }
}

impl<'a> std::fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OmitedRequiredStatement{t, suggestion } => {
                let filename = if t.filename.is_some() { t.filename.unwrap() } else { "<stdin>" };
                let caret_col_pos = format!("{}", t.span.line).len() + 1 + t.span.len + t.span.col;
                let caret = "^".repeat(t.span.len);
                write!(f, "{}:{} {:?} is missing required statement:\n\t{}: {}\n\t{:->width$} {}", filename, t.span.line, t.kind, t.span.line, t.line, caret, suggestion, width=caret_col_pos)
            },
            Self::UnsetRequirement{t, requirement } => {
                let filename = if t.filename.is_some() { t.filename.unwrap() } else { "<stdin>" };
                let caret_col_pos = format!("{}", t.span.line).len() + 1 + t.span.len + t.span.col;
                let caret = "^".repeat(t.span.len);
                write!(f, "{}:{} unset requirement {}:\n\t{}: {}\n\t{:->width$} Add {} to domain requirements.", filename, t.span.line, requirement, t.span.line, t.line, caret, requirement, width=caret_col_pos)
            },
            Self::UnexpectedToken{t, suggestion } => {
                let filename = if t.filename.is_some() { t.filename.unwrap() } else { "<stdin>" };
                let caret_col_pos = format!("{}", t.span.line).len() + 1 + t.span.len + t.span.col;
                let caret = "^".repeat(t.span.len);
                write!(f, "{}:{} Unexpected token {:?}:\n\t{}: {}\n\t{:->width$} {}", filename, t.span.line, t.kind, t.span.line, t.line, caret, suggestion, width=caret_col_pos)
            },
            Self::UnexpectedEOF{filename, suggestion} => {
                let filename = if filename.is_some() { filename.unwrap() } else { "<stdin>" };
                write!(f, "{}: Unexpected end of file: {}", filename, suggestion)
            },
            Self::UnexpectedCharacter{filename, span, line } => {
                let filename = if filename.is_some() { filename.unwrap() } else { "<stdin>" };
                let caret_col_pos = format!("{}", span.line).len() + 1 + span.len + span.col;
                let caret = "^".repeat(span.len);
                write!(f, "{}:{} Unexpected character:\n\t{}: {}\n\t{:->width$} {}", filename, span.line, span.line, line, caret, ' ', width=caret_col_pos)
            },
            Self::ParseFloatError{filename, span, line, source } => {
                let filename = if filename.is_some() { filename.unwrap() } else { "<stdin>" };
                let caret_col_pos = format!("{}", span.line).len() + 1 + span.len + span.col;
                let caret = "^".repeat(span.len);
                write!(f, "{}:{} {}:\n\t{}: {}\n\t{:->width$} {}", filename, span.line, source, span.line, line, caret, ' ', width=caret_col_pos)
            },
            Self::ParseIntError{filename, span, line, source } => {
                let filename = if filename.is_some() { filename.unwrap() } else { "<stdin>" };
                let caret_col_pos = format!("{}", span.line).len() + 1 + span.len + span.col;
                let caret = "^".repeat(span.len);
                write!(f, "{}:{} {}:\n\t{}: {}\n\t{:->width$} {}", filename, span.line, source, span.line, line, caret, ' ', width=caret_col_pos)
            },
        }
    }
}

/// Parses PDDL 3.1 syntax
/// Based on [Daniel L. Kovacs' BNF definition](http://pddl4j.imag.fr/repository/wiki/BNF-PDDL-3.1.pdf)
/// 
/// Example:
/// ```rust
/// use pddl_rs::parser::{Parser, ast::Stmt};
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

#[macro_export]
macro_rules! check_requirements {
    ($s:expr, $req:expr, $valid:expr, $t:expr) => {
        if $s.requirements.contains($req) {
            $valid
        } else {
            Err(Error::UnsetRequirement{t:$t, requirement:$req})
        }
    };
}

impl<'a> Parser<'a> {

    fn error_recover(&mut self) {

    }

    fn literal(&mut self) -> Result<Literal<'a>, Error<'a>> {
        use TokenKind::{Literal};
        expect!(self, {
            Some(Ok(Token{kind:Literal(l),..})) => Ok(l)
        }, "Expected a literal.")
    }

    fn timed_effect(&mut self) -> Result<TimedEffect<'a>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Keyword};
        use KeywordToken::{At, Start, End};
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = match self.lexer.peek() {
            Some(Ok(Token{kind:Keyword(At),..})) => { 
                self.lexer.next();
                expect!(self, {
                    Some(Ok(Token{kind:Keyword(Start),..})) => Ok(TimedEffect::AtStart(self.effect(false)?)),
                    Some(Ok(Token{kind:Keyword(End),..})) => Ok(TimedEffect::AtEnd(self.effect(false)?)),
                }, "Expected 'start' or 'end'.")
            },
            _ => Ok(TimedEffect::Effect(self.effect(false)?))
        };
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }

    fn timed_gd(&mut self) -> Result<TimedGD<'a>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Keyword};
        use KeywordToken::{At, Start, End, Over, All};
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = expect!(self, {
            Some(Ok(Token{kind:Keyword(At),..})) => expect!(self, {
                Some(Ok(Token{kind:Keyword(Start),..})) => Ok(TimedGD::AtStart(self.gd(false)?)),
                Some(Ok(Token{kind:Keyword(End),..})) => Ok(TimedGD::AtEnd(self.gd(false)?))
            }, "Expected 'start' or 'end'."),
            Some(Ok(Token{kind:Keyword(Over),..})) => expect!(self, {Some(Ok(Token{kind:Keyword(All),..}))=>Ok(TimedGD::OverAll(self.gd(false)?))}, "Expected 'all'."),
        }, "Expected timed gd.");
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }

    fn duration_gd(&mut self) -> Result<DurationGD<'a>, Error<'a>> {
        use TokenKind::{Op, Keyword, Identifier, OpenParenthesis, CloseParenthesis};
        use OpToken::And;
        use KeywordToken::{Forall, Preference};
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = match self.lexer.peek() {
            Some(Ok(Token{kind:Op(And),..})) => {
                self.lexer.next();
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.duration_gd()?)
                }
                Ok(DurationGD::And(vec))
            },
            Some(Ok(Token{kind:Keyword(Forall),..})) => {
                self.lexer.next();
                Ok(DurationGD::Forall(self.vec_typed_list()?, Box::new(self.duration_gd()?)))

            },
            Some(Ok(Token{kind:Keyword(Preference),..})) => {
                self.lexer.next();
                let name = if let Some(Ok(Token{kind:Identifier(i),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
                    Some(i)
                } else {
                    None
                };
                Ok(DurationGD::Preference(name, self.timed_gd()?))
            }
            _ => Ok(DurationGD::GD(self.timed_gd()?))
        };
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }

    fn duration_effect(&mut self) -> Result<DurationEffect<'a>, Error<'a>> {
        use TokenKind::{Op, Keyword, OpenParenthesis, CloseParenthesis};
        use OpToken::And;
        use KeywordToken::{Forall, When};
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = match self.lexer.peek() {
            Some(Ok(Token{kind:Op(And),..})) => {
                self.lexer.next();
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.duration_effect()?)
                }
                Ok(DurationEffect::And(vec))
            },
            Some(Ok(Token{kind:Keyword(Forall),..})) => {
                let t = self.lexer.next().unwrap().unwrap();
                check_requirements!(self, Requirements::ConditionalEffects, 
                    Ok(DurationEffect::Forall(self.vec_typed_list()?, Box::new(self.duration_effect()?))),
                    t)
            },
            Some(Ok(Token{kind:Keyword(When),..})) => {
                let t = self.lexer.next().unwrap().unwrap();
                check_requirements!(self, Requirements::ConditionalEffects, 
                    Ok(DurationEffect::When(self.duration_gd()?, self.timed_effect()?)),
                    t)
            }
            _ => Ok(DurationEffect::GD(self.timed_effect()?))
        };
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }

    fn duration_constraint(&mut self) -> Result<DurationConstraint<'a>, Error<'a>> {
        use TokenKind::{Op, Keyword, OpenParenthesis, CloseParenthesis};
        use KeywordToken::{At, Start, End};
        use OpToken::{Equals, And, SmallerOrEquals, GreaterOrEquals};
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = expect!(self, {
            Some(Ok(Token{kind:Keyword(At),..})) => expect!(self, {
                Some(Ok(Token{kind:Keyword(Start),..})) => Ok(DurationConstraint::AtStart(Box::new(self.duration_constraint()?))),
                Some(Ok(Token{kind:Keyword(End),..})) => Ok(DurationConstraint::AtEnd(Box::new(self.duration_constraint()?))),
            }, "Expected 'start' or 'end'."),
            Some(Ok(Token{kind:Op(Equals),..})) => Ok(DurationConstraint::Equals(self.fluent_expression()?)),
            Some(Ok(t @ Token{kind:Op(SmallerOrEquals),..})) => check_requirements!(self, Requirements::DurationInequalities, Ok(DurationConstraint::LessThanOrEquals(self.fluent_expression()?)), t),
            Some(Ok(t @ Token{kind:Op(GreaterOrEquals),..})) => check_requirements!(self, Requirements::DurationInequalities, Ok(DurationConstraint::GreaterOrEquals(self.fluent_expression()?)), t),
            Some(Ok(t @ Token{kind:Op(And),..})) => {
                let mut vec = Vec::new();
                while matches!(self.lexer.peek(), Some(Ok(Token{kind:OpenParenthesis,..}))) {
                    vec.push(self.duration_constraint()?)
                }
                check_requirements!(self, Requirements::DurationInequalities, Ok(DurationConstraint::And(vec)), t)
            }
        }, "Expected duration constraint.");
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }

    fn precondition_expr(&mut self) -> Result<PreconditionExpr<'a>, Error<'a>> {
        use TokenKind::{Op, Keyword, Identifier, OpenParenthesis, CloseParenthesis};
        use OpToken::And;
        use KeywordToken::{Forall, Preference};
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = match self.lexer.peek() {
            Some(Ok(Token{kind:Op(And),..})) => {
                self.lexer.next();
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.precondition_expr()?)
                }
                Ok(PreconditionExpr::And(vec))
            },
            Some(Ok(Token{kind:Keyword(Forall),..})) => {
                self.lexer.next();
                Ok(PreconditionExpr::Forall(self.vec_typed_list()?, Box::new(self.precondition_expr()?)))

            },
            Some(Ok(Token{kind:Keyword(Preference),..})) => {
                self.lexer.next();
                let name = if let Some(Ok(Token{kind:Identifier(i),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
                    Some(i)
                } else {
                    None
                };
                Ok(PreconditionExpr::Preference(name, self.gd(false)?))
            }
            _ => Ok(PreconditionExpr::GD(self.gd(false)?))
        };
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }

    fn effect(&mut self, is_consume_parenthesis: bool) -> Result<Effect<'a>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Op, Keyword, Identifier};
        use OpToken::{And, Not};
        use KeywordToken::{Forall, When, Assign, ScaleDown, ScaleUp, Increase, Decrease};
        if is_consume_parenthesis {
            expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        }
        let result = expect!(self, {
            Some(Ok(Token{kind:Op(And),..})) => {
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.effect(true)?);
                }
                Ok(Effect::And(vec))
            },
            Some(Ok(t @ Token{kind:Keyword(Forall),..})) => check_requirements!(self, Requirements::ConditionalEffects, Ok(Effect::Forall(self.vec_typed_list()?, Box::new(self.effect(true)?))), t),
            Some(Ok(t @ Token{kind:Keyword(When),..})) => check_requirements!(self, Requirements::ConditionalEffects, {
                let gd = self.gd(false)?;
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.effect(true)?);
                }
                Ok(Effect::When(gd, vec))
            }, t),
            Some(Ok(Token{kind:Identifier(i),..})) => Ok(Effect::AtomicFormula(i, self.vec_term(false)?)),
            Some(Ok(Token{kind:Op(Not),..})) => {
                expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
                let result = Ok(Effect::NotAtomicFormula(expect!(self, {Some(Ok(Token{kind:Identifier(i),..}))=>Ok(i)}, EXPECTED_IDENTIFIER)?, self.vec_term(false)?));
                expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
                result
            },
            Some(Ok(t @ Token{kind:Keyword(Assign),..})) => {
                let fterm = self.function_term(false)?;
                if let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    check_requirements!(self, Requirements::ObjectFluents, Ok(Effect::Assign(fterm, self.fluent_expression()?)), t)
                } else {
                    check_requirements!(self, Requirements::NumericFluents, Ok(Effect::AssignUndefined(fterm)), t)
                }
            },
            Some(Ok(t @ Token{kind:Keyword(ScaleUp),..})) => {
                if self.requirements.contains(Requirements::ActionCosts) || self.requirements.contains(Requirements::NumericFluents) {
                    Ok(Effect::Increase(self.function_term(true)?, self.fluent_expression()?))
                } else {
                    Err(Error::UnsetRequirement{t, requirement:Requirements::NumericFluents})
                }
            },
            Some(Ok(t @ Token{kind:Keyword(ScaleDown),..})) => {
                if self.requirements.contains(Requirements::ActionCosts) || self.requirements.contains(Requirements::NumericFluents) {
                    Ok(Effect::Increase(self.function_term(true)?, self.fluent_expression()?))
                } else {
                    Err(Error::UnsetRequirement{t, requirement:Requirements::NumericFluents})
                }
            },
            Some(Ok(t @ Token{kind:Keyword(Increase),..})) => {
                if self.requirements.contains(Requirements::ActionCosts) || self.requirements.contains(Requirements::NumericFluents) {
                    Ok(Effect::Increase(self.function_term(true)?, self.fluent_expression()?))
                } else {
                    Err(Error::UnsetRequirement{t, requirement:Requirements::NumericFluents})
                }
            },
            Some(Ok(t @ Token{kind:Keyword(Decrease),..})) => {
                if self.requirements.contains(Requirements::ActionCosts) || self.requirements.contains(Requirements::NumericFluents) {
                    Ok(Effect::Increase(self.function_term(true)?, self.fluent_expression()?))
                } else {
                    Err(Error::UnsetRequirement{t, requirement:Requirements::NumericFluents})
                }
            },
        }, "Expected effect.");
        if is_consume_parenthesis {
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        result
    }


    /// ```bnf
    /// <derived-def> ::= (:derived <atomic formula skeleton> <GD>)
    /// ```
    fn derived_action(&mut self, token:Token<'a>) -> Result<ast::Action<'a>, Error<'a>> {
        if self.requirements.contains(Requirements::DerivedPredicates) {
            let predicate = self.atomic_f_skeleton()?;
            let expr = self.gd(true)?;
            Ok(ast::Action::Derived(predicate, expr))
        } else {
            Err(Error::UnsetRequirement{t:token, requirement: Requirements::DerivedPredicates})
        }
    }

    /// ```bnf
    /// <durative-action-def> ::= (:durative-action <da-symbol>
    ///                 :parameters (<typed list (variable)>)
    ///                 :duration <duration-constraint>
    ///                 :condition <emptyOr (da-GD)>
    ///                 :effect <emptyOr (da-effect)>
    ///                 )
    /// ```
    fn durative_action(&mut self, token:Token<'a>) -> Result<ast::Action<'a>, Error<'a>> {
        use TokenKind::{Identifier, Keyword, Colon, OpenParenthesis, CloseParenthesis, QuestionMark};
        use KeywordToken::{Condition, Effect, Duration, Parameters};
        let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
        let mut parameters = Vec::new();
        let mut condition = None;
        let mut effect = None;
        let mut duration = None;
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Colon,..}))).is_some() {
            expect!(self, {
                Some(Ok(Token{kind:Keyword(Parameters),..})) => {
                    expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..})) => Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
                    while let Some(Ok(Token{kind:QuestionMark,..})) = self.lexer.peek() {
                        parameters.push(self.typed_list_variable()?);
                    }
                    expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
                    Ok(())
                },  
                Some(Ok(Token{kind:Keyword(Condition),..})) => Ok(condition = Some(self.duration_gd()?)),   
                Some(Ok(Token{kind:Keyword(Effect),..})) => Ok(effect = Some(self.duration_effect()?)),  
                Some(Ok(Token{kind:Keyword(Duration),..})) => Ok(duration = Some(self.duration_constraint()?)),   
            }, "Expected Action properties.")?;
        }
        if self.requirements.contains(Requirements::DurativeActions) {
            if duration.is_some() {
                let duration = duration.unwrap();
                Ok(Action::Durative(DurativeAction{name, parameters, duration, condition, effect}))
            } else {
                Err(Error::OmitedRequiredStatement { t: token, suggestion: "Add :duration statement." })
            }
        } else {
            Err(Error::UnsetRequirement{t:token, requirement: Requirements::DurativeActions})
        }
    }

    /// ```bnf 
    /// <action_def> ::= (:action <action-symbol> 
    ///                 :parameters (<typed list (variable)>) 
    ///                 [:precondition <emptyOr (pre-GD)>]
    ///                 [:effect <emptyOr (effect)>] 
    ///                 )
    /// ```
    fn basic_action(&mut self) -> Result<ast::Action<'a>, Error<'a>> {
        use TokenKind::{Keyword, Identifier, QuestionMark, Colon, OpenParenthesis, CloseParenthesis};
        use KeywordToken::{Parameters, Precondition, Effect};
        let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
        let mut parameters = Vec::new();
        let mut precondition = None;
        let mut effect = None;
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Colon,..}))).is_some() {
            expect!(self, {
                Some(Ok(Token{kind:Keyword(Parameters),..})) => {
                    expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..})) => Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
                    while let Some(Ok(Token{kind:QuestionMark,..})) = self.lexer.peek() {
                        parameters.push(self.typed_list_variable()?);
                    }
                    expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
                    Ok(())
                },  
                Some(Ok(Token{kind:Keyword(Precondition),..})) => Ok(precondition = Some(self.precondition_expr()?)),   
                Some(Ok(Token{kind:Keyword(Effect),..})) => Ok(effect = Some(self.effect(true)?)),  
            }, "Expected Action properties.")?;
        }
        Ok(Action::Basic(BasicAction { name, parameters, precondition, effect }))
    }

    fn fluent_expression(&mut self) -> Result<FluentExpression<'a>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Literal, Op, Identifier, QuestionMark};
        use OpToken::{Minus, Plus, Slash, Star};
        if let Some(Ok(Token{kind:Literal(l),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Literal(_),..}))) {
             Ok(FluentExpression::Number(l))
        } else {
            expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
            let result = expect!(self, {
                Some(Ok(Token{kind:Op(Minus),..})) => Ok(FluentExpression::Subtract(Box::new((self.fluent_expression()?, self.fluent_expression()?)))),
                Some(Ok(Token{kind:Op(Slash),..})) => Ok(FluentExpression::Divide(Box::new((self.fluent_expression()?, self.fluent_expression()?)))),
                Some(Ok(Token{kind:Op(Plus),..})) => { 
                    let mut vec = Vec::new();
                    while matches!(self.lexer.peek(), Some(Ok(Token{kind:OpenParenthesis,..}))) { 
                        vec.push(self.fluent_expression()?);
                    }
                    Ok(FluentExpression::Add(vec))
                },
                Some(Ok(Token{kind:Op(Star),..})) => { 
                    let mut vec = Vec::new();
                    while matches!(self.lexer.peek(), Some(Ok(Token{kind:OpenParenthesis,..}))) { 
                        vec.push(self.fluent_expression()?);
                    }
                    Ok(FluentExpression::Multiply(vec))
                },
                Some(Ok(Token{kind:Identifier(name),..})) => {
                    let are_variables = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..}))).is_some();
                    let mut vec = Vec::new();
                    while let Some(Ok(Token{kind:Identifier(i),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
                        if are_variables {
                            vec.push(Term::Variable(i));
                            self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..})));
                        } else {
                            vec.push(Term::Name(i));
                        }
                    }
                    Ok(FluentExpression::Function(FunctionTerm{name, terms:vec}))
                }
            }, "Expected Fluent Expression.");
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
            result
        }
    }

    fn vec_term(&mut self, funcs_allowed:bool) -> Result<Vec<Term<'a>>, Error<'a>> {
        // The BNF is ambigous for how to differentiate a <function-term> vs a <term>+
        // Implementing as-is for now. This will likely never execute as first term() 
        // will collect all <name>+ as a function-term.
        use TokenKind::{QuestionMark, Identifier};
        let mut vec = Vec::new();
        while let Some(Ok(Token{kind:QuestionMark | Identifier(_),..})) = self.lexer.peek() {
            vec.push(self.term(funcs_allowed)?);
        }
        Ok(vec)
    }

    fn function_term(&mut self, is_consume_parenthesis: bool) -> Result<FunctionTerm<'a>, Error<'a>> {
        use TokenKind::{Identifier, QuestionMark, OpenParenthesis, CloseParenthesis};
        if is_consume_parenthesis {
            expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        }
        let this = expect!(self, {
            Some(Ok(Token{kind:Identifier(i),..})) => Ok(i)
        }, EXPECTED_IDENTIFIER)?;
        let are_variables = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..}))).is_some();
        let mut vec = Vec::new();
        while let Some(Ok(Token{kind:Identifier(i),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
            if are_variables {
                vec.push(Term::Variable(i));
                self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..})));
            } else {
                vec.push(Term::Name(i));
            }
        }
        if is_consume_parenthesis {
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        Ok(FunctionTerm{name:this, terms:vec})
    }

    fn term(&mut self, funcs_allowed:bool) -> Result<Term<'a>, Error<'a>> {
        use TokenKind::{QuestionMark, Identifier};
        if self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..}))).is_some() {
            expect!(self, {
                Some(Ok(Token{kind:Identifier(i),..})) => Ok(Term::Variable(i))
            }, EXPECTED_IDENTIFIER)
        } else {
            // The BNF is ambigous about the expected structure
            // I'm going to assume a function name can't follow function name
            // and instead a function name will follow variables or name terminals.
            if funcs_allowed {
                let fterm = self.function_term(false)?;
                if fterm.terms.len() > 0 {
                    Ok(Term::Function(fterm))
                } else {
                    Ok(Term::Name(fterm.name))
                }
            } else {
                expect!(self, {
                    Some(Ok(Token{kind:Identifier(i),..})) => Ok(Term::Name(i))
                }, EXPECTED_IDENTIFIER)
            }
        }
    }

    fn gd(&mut self, is_consume_parenthesis: bool) -> Result<GD<'a>, Error<'a>> {
        const EXPECTED_GD:&str = "Expected expression.";
        use TokenKind::{OpenParenthesis, CloseParenthesis, Identifier, Op, Keyword};
        use OpToken::{Equals, And, Not, Or, Smaller, Greater, SmallerOrEquals, GreaterOrEquals};
        use KeywordToken::{Imply, Forall};
        if is_consume_parenthesis {
            expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        }
        let result = expect!(self, {
            Some(Ok(Token{kind:Identifier(i),..})) => Ok(GD::AtomicFormula(i, self.vec_term(false)?)),
            Some(Ok(Token{kind:Op(Equals),..})) => Ok(GD::AtomicEquality(self.term(true)?, self.term(true)?)),
            Some(Ok(t @ Token{kind:Op(Not),..})) => if self.requirements.contains(Requirements::NegativePreconditions) {
                expect!(self, {
                    Some(Ok(Token{kind:Identifier(i),..})) => Ok(GD::NotAtomicFormula(i, self.vec_term(false)?))
                    Some(Ok(Token{kind:Op(Equals),..})) => Ok(GD::NotAtomicEquality(self.term(true)?, self.term(true)?))
                }, EXPECTED_GD)
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::NegativePreconditions })
            },
            Some(Ok(Token{kind:Op(And),..})) => { 
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.gd(true)?);
                }
                Ok(GD::And(vec))
            },
            Some(Ok(t @ Token{kind:Op(Or),..})) => if self.requirements.contains(Requirements::DisjunctivePreconditions) {
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.gd(true)?);
                }
                Ok(GD::Or(vec))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::DisjunctivePreconditions})
            },
            Some(Ok(t @ Token{kind:Op(Not),..})) => if self.requirements.contains(Requirements::DisjunctivePreconditions) {
                Ok(GD::Not(Box::new(self.gd(true)?)))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::DisjunctivePreconditions })
            },
            Some(Ok(t @ Token{kind:Keyword(Imply),..})) => if self.requirements.contains(Requirements::DisjunctivePreconditions) {
                Ok(GD::Imply(Box::new((self.gd(true)?, self.gd(true)?))))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::DisjunctivePreconditions })
            },
            Some(Ok(t @ Token{kind:Keyword(Exists),..})) => if self.requirements.contains(Requirements::ExistentialPreconditions) {
                Ok(GD::Exists(self.vec_typed_list()?, Box::new(self.gd(true)?)))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::ExistentialPreconditions })
            },
            Some(Ok(t @ Token{kind:Keyword(Forall),..})) => if self.requirements.contains(Requirements::UniversalPreconditions) {
                Ok(GD::Forall(self.vec_typed_list()?, Box::new(self.gd(true)?)))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::UniversalPreconditions })
            },
            Some(Ok(t @ Token{kind:Op(Smaller),..})) => if self.requirements.contains(Requirements::NumericFluents) {
                Ok(GD::LessThan(self.fluent_expression()?, self.fluent_expression()?))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::NumericFluents })
            },
            Some(Ok(t @ Token{kind:Op(SmallerOrEquals),..})) => if self.requirements.contains(Requirements::NumericFluents) {
                Ok(GD::LessThanOrEqual(self.fluent_expression()?, self.fluent_expression()?))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::NumericFluents })
            },
            Some(Ok(t @ Token{kind:Op(Equals),..})) => if self.requirements.contains(Requirements::NumericFluents) {
                Ok(GD::Equal(self.fluent_expression()?, self.fluent_expression()?))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::NumericFluents })
            },
            Some(Ok(t @ Token{kind:Op(Greater),..})) => if self.requirements.contains(Requirements::NumericFluents) {
                Ok(GD::GreaterThan(self.fluent_expression()?, self.fluent_expression()?))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::NumericFluents })
            },
            Some(Ok(t @ Token{kind:Op(GreaterOrEquals),..})) => if self.requirements.contains(Requirements::NumericFluents) {
                Ok(GD::GreatherThanOrEqual(self.fluent_expression()?, self.fluent_expression()?))
            } else {
                Err(Error::UnsetRequirement { t, requirement: Requirements::NumericFluents })
            },

        }, EXPECTED_GD);
        if is_consume_parenthesis {
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        result
    }

    fn pref_constraint_gd(&mut self) -> Result<PrefConstraintGD<'a>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Keyword, Op, Identifier};
        use KeywordToken::{Forall, Preference};
        use OpToken::And;
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = match self.lexer.peek() {
            Some(Ok(Token{kind:Op(And),..})) => {
                self.lexer.next();
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.pref_constraint_gd()?);
                }
                Ok(PrefConstraintGD::And(vec))
            },
            Some(Ok(Token{kind:Keyword(Forall),..})) => {
                self.lexer.next();
                Ok(PrefConstraintGD::Forall(self.vec_typed_list()?, Box::new(self.pref_constraint_gd()?)))
            },
            Some(Ok(Token{kind:Keyword(Preference),..})) => {
                self.lexer.next();
                expect!(self, {
                Some(Ok(Token{kind:Identifier(i),..}))=>Ok(PrefConstraintGD::Preference(i, self.constraint_gd()?))}, "Expected preference name.")
            },
            _ => Ok(PrefConstraintGD::GD(self.constraint_gd()?))
        };
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }

    fn metric(&mut self) -> Result<Metric<'a>, Error<'a>> {
        todo!()
    }

    fn length(&mut self) -> Result<LengthSpecification<'a>, Error<'a>> {
        todo!()
    }


    fn constraint_gd(&mut self) -> Result<ConstraintGD<'a>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Keyword, Op};
        use KeywordToken::{Forall, At, End, Always, Sometime, Within, AtMostOnce, SometimeAfter, 
            SometimeBefore, AlwaysWithin, HoldAfter, HoldDuring};
        use OpToken::And;
        expect!(self, {Some(Ok(Token{kind:OpenParenthesis,..}))=>Ok(())}, EXPECTED_OPEN_PARENTHESIS)?;
        let result = expect!(self, {
            Some(Ok(Token{kind:Op(And),..})) => {
                let mut vec = Vec::new();
                while let Some(Ok(Token{kind:OpenParenthesis,..})) = self.lexer.peek() {
                    vec.push(self.constraint_gd()?);
                }
                Ok(ConstraintGD::And(vec))
            },
            Some(Ok(Token{kind:Keyword(Forall),..})) => Ok(ConstraintGD::Forall(self.vec_typed_list()?, Box::new(self.constraint_gd()?))),
            Some(Ok(Token{kind:Keyword(At),..})) => expect!(self, {Some(Ok(Token{kind:Keyword(End),..}))=>Ok(ConstraintGD::AtEnd(self.gd(true)?))}, "Expected 'end'."),
            Some(Ok(Token{kind:Keyword(Always),..})) => Ok(ConstraintGD::Always(self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(Sometime),..})) => Ok(ConstraintGD::Sometime(self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(Within),..})) => Ok(ConstraintGD::Within(self.literal()?, self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(AtMostOnce),..})) => Ok(ConstraintGD::AtMostOnce(self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(SometimeAfter),..})) => Ok(ConstraintGD::SometimeAfter(self.gd(true)?, self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(SometimeBefore),..})) => Ok(ConstraintGD::SometimeBefore(self.gd(true)?, self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(AlwaysWithin),..})) => Ok(ConstraintGD::AlwaysWithin(self.literal()?, self.gd(true)?, self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(HoldDuring),..})) => Ok(ConstraintGD::HoldDuring(self.literal()?, self.literal()?, self.gd(true)?)),
            Some(Ok(Token{kind:Keyword(HoldAfter),..})) => Ok(ConstraintGD::HoldAfter(self.literal()?, self.gd(true)?)),
        }, "Expected constraint expression.");
        expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        result
    }
    
        
    fn parse_type(&mut self) -> Result<Vec<&'a str>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Identifier, Keyword};
        use KeywordToken::Either;
        let mut result = Vec::new();
        let either_clause = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:OpenParenthesis,..}))).is_some();
        if either_clause {
            expect!(self, {Some(Ok(Token{kind:Keyword(Either),..}))=>Ok(())}, "Expected 'either'.")?;
        }
        while let Some(Ok(Token{kind:Identifier(s),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
            result.push(s);
        }
        if either_clause {
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }

        Ok(result)
    }

    /// ```ebnf
    /// <functions-def> ::= (:functions <function typed list (atomic function skeleton)>)
    /// ```
    /// atomic function skeleton and atomic formula skeleton are essentially the same
    /// and this parser calls it `callable_declaration`
    fn functions(&mut self) -> Result<Vec<TypedFunction<'a>>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis, Op};
        use OpToken::Minus;
        let mut result = Vec::new();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            let function = self.atomic_f_skeleton()?;
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
            let has_minus = if let Some(Ok(Token{kind:Op(Minus),..})) = self.lexer.peek() { true } else { false};
            let kind = if has_minus {
                let minus_token = self.lexer.next().unwrap().unwrap();
                if self.requirements.contains(Requirements::NumericFluents) {
                    Ok(FunctionTypeKind::Numeric(expect!(self, {Some(Ok(Token{kind:TokenKind::Literal(Literal::I(val)),..})) => Ok(val)}, "Expected a number - :numeric-fluents is required.")?))
                } else if self.requirements.contains(Requirements::Typing) && (self.requirements.contains(Requirements::ObjectFluents) || self.requirements.contains(Requirements::ActionCosts)) {
                    let r#type = self.parse_type()?;
                    if !self.requirements.contains(Requirements::ObjectFluents) {
                        if r#type.len() == 1 && r#type.eq(&vec!["number"]) {
                            Ok(FunctionTypeKind::Typed(r#type))
                        } else {
                            Err(Error::UnsetRequirement { t: minus_token, requirement: Requirements::ObjectFluents })
                        }
                    } else {
                        Ok(FunctionTypeKind::Typed(r#type))
                    }
                } else {
                    Err(Error::UnsetRequirement{t: minus_token, requirement:Requirements::Typing })
                }
            } else {
                Ok(FunctionTypeKind::None)
            }?;
            result.push(TypedFunction{function, kind});
        }
        Ok(result)
    }

    fn predicates(&mut self) -> Result<Vec<AtomicFSkeleton<'a>>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis};
        let mut predicates = Vec::new();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            predicates.push(self.atomic_f_skeleton()?);
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        Ok(predicates)
    }

    /// ```ebnf
    /// <atomic formula skeleton> ::= (<predicate> <typed list (variable)>)
    /// <atomic function skeleton> ::= (<function-symbol> <typed list (variable)>)
    /// <predicate> ::= <name>
    /// <function-symbol> ::= <name>
    /// ```
    fn atomic_f_skeleton(&mut self) -> Result<AtomicFSkeleton<'a>, Error<'a>> {
        use TokenKind::{Identifier, QuestionMark};
    
        let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
        let mut variables = Vec::new();
        while let Some(Ok(Token{kind:QuestionMark,..})) = self.lexer.peek() {
            variables.push(self.typed_list_variable()?);
        }
        Ok(AtomicFSkeleton{name, variables})

    }

    fn typed_list_variable(&mut self) -> Result<List<'a>, Error<'a>> {
        use TokenKind::{Op, QuestionMark, Identifier};
        use OpToken::Minus;
        let mut identifiers = Vec::new();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:QuestionMark,..}))).is_some() {
            identifiers.push(expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?);
        }
        // TODO: Both problem and domain specification uses typed_list, 
        // but it's possible to have domain with requirements and not problem. 
        // figure out how to deal with missing requirements for problem
        let has_minus = if let Some(Ok(Token{kind:Op(Minus),..})) = self.lexer.peek() { true } else { false};
        if self.requirements.contains(Requirements::Typing) || has_minus {
            expect!(self, {Some(Ok(Token{kind:Op(Minus),..})) => Ok(())}, ":typing is enabled - expected '-' at the end of typed list.")?;
            let kind = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
            Ok(List::Typed(identifiers, kind))
        } else {
            Ok(List::Basic(identifiers))
        }
    }

    fn typed_list_name(&mut self) -> Result<List<'a>, Error<'a>> {
        use TokenKind::{Op, Identifier};
        use OpToken::Minus;
        let mut identifiers = Vec::new();
        while let Some(Ok(Token{kind:Identifier(s),..})) = self.lexer.next_if(|t| matches!(t, Ok(Token{kind:Identifier(_),..}))) {
            identifiers.push(s);
        }
        let has_minus = if let Some(Ok(Token{kind:Op(Minus),..})) = self.lexer.peek() { true } else { false};
        if self.requirements.contains(Requirements::Typing) || has_minus {
            expect!(self, {Some(Ok(Token{kind:Op(Minus),..})) => Ok(())}, ":typing is enabled - expected '-' at the end of typed list.")?;
            let kind = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
            Ok(List::Typed(identifiers, kind))
        } else {
            Ok(List::Basic(identifiers))
        }
    }


    /// ```ebnf
    /// <types-def> ::= (:types <typed list (name)>)
    /// ```
    fn vec_typed_list(&mut self) -> Result<Vec<List<'a>>, Error<'a>> {
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
                Some(Ok(Token{kind:Identifier("equality"),..})) => Ok(r.insert(ast::Requirements::Equality)),
                Some(Ok(Token{kind:Identifier("existential-preconditions"),..})) => Ok(r.insert(ast::Requirements::ExistentialPreconditions)),
                Some(Ok(Token{kind:Identifier("universal-preconditions"),..})) => Ok(r.insert(ast::Requirements::UniversalPreconditions)),
                Some(Ok(Token{kind:Identifier("quantified-preconditions"),..})) => { r.insert_all(enum_set!(ast::Requirements::ExistentialPreconditions | 
                                                                                    ast::Requirements::UniversalPreconditions
                                                                                )); Ok(true)},
                Some(Ok(Token{kind:Identifier("conditional-effects"),..})) => Ok(r.insert(ast::Requirements::ConditionalEffects)),
                Some(Ok(Token{kind:Identifier("fluents"),..})) => { r.insert_all(enum_set!(ast::Requirements::ObjectFluents | 
                                                                                    ast::Requirements::NumericFluents
                                                                                )); Ok(true)},
                Some(Ok(Token{kind:Identifier("numeric-fluents"),..})) => Ok(r.insert(ast::Requirements::NumericFluents)),
                Some(Ok(Token{kind:Identifier("adl"),..})) => { r.insert_all(enum_set!(ast::Requirements::Strips | 
                                                                                    ast::Requirements::Typing | 
                                                                                    ast::Requirements::NegativePreconditions | 
                                                                                    ast::Requirements::DisjunctivePreconditions |
                                                                                    ast::Requirements::Equality |
                                                                                    ast::Requirements::ExistentialPreconditions |
                                                                                    ast::Requirements::UniversalPreconditions |
                                                                                    ast::Requirements::ConditionalEffects
                                                                                )); Ok(true)},
                Some(Ok(Token{kind:Identifier("durative-actions"),..})) => Ok(r.insert(ast::Requirements::DurativeActions)),
                Some(Ok(Token{kind:Identifier("duration-inequalities"),..})) => Ok(r.insert(ast::Requirements::DurationInequalities)),
                Some(Ok(Token{kind:Identifier("continuous-effects"),..})) => Ok(r.insert(ast::Requirements::ContinuousEffects)),
                Some(Ok(Token{kind:Identifier("derived-predicates"),..})) => Ok(r.insert(ast::Requirements::DerivedPredicates)),
                Some(Ok(Token{kind:Identifier("timed-initial-literals"),..})) => Ok(r.insert(ast::Requirements::TimedInitialLiterals)),
                Some(Ok(Token{kind:Identifier("preferences"),..})) => Ok(r.insert(ast::Requirements::Preferences)),
                Some(Ok(Token{kind:Identifier("constraints"),..})) => Ok(r.insert(ast::Requirements::Constraints)),
                Some(Ok(Token{kind:Identifier("action-costs"),..})) => Ok(r.insert(ast::Requirements::ActionCosts)),
            }, "Expected requirements.")?;
        }
        self.requirements = r;
        Ok(r)
    }

    fn init(&mut self) -> Result<Vec<Init<'a>>, Error<'a>> {
        use TokenKind::{Keyword, Op, Identifier, OpenParenthesis, CloseParenthesis};
        use KeywordToken::{At};
        use OpToken::Not;
        let mut vec = Vec::new();
        while matches!(self.lexer.peek(), Some(Ok(Token{kind:OpenParenthesis,..}))) {
            self.lexer.next();
            vec.push(expect!(self, {
                    Some(Ok(Token{kind:Keyword(At),..})) => Ok(Init::At(self.literal()?, self.vec_term(true)?))
                    Some(Ok(Token{kind:Identifier(i),..})) => Ok(Init::AtomicFormula(i, self.vec_term(false)?)),
                    Some(Ok(Token{kind:Op(Not),..})) => expect!(self, {
                        Some(Ok(Token{kind:Identifier(i),..})) => Ok(Init::NotAtomicFormula(i, self.vec_term(false)?)),
                        Some(Ok(t @ Token{kind:Keyword(At),..})) => check_requirements!(self, Requirements::TimedInitialLiterals, Ok(Init::NotAt(self.literal()?, self.vec_term(true)?)), t)
                    }, "Expected 'at' or predicate."),
                }, "Expected at, predicate, or not.")?
            );
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        Ok(vec)
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
        let mut constraints = None;
        let mut metric = None;
        let mut length = None;
        while self.lexer.next_if(|r| matches!(r, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            expect!(self, {Some(Ok(Token{kind:Colon,..})) => Ok(())}, EXPECTED_COLON)?;
            expect!(self, {
                Some(Ok(Token{kind:Keyword(Domain),..})) => Ok(domain = Some(expect!(self, {Some(Ok(Token{kind:Identifier(s),..}))=>Ok(s)}, EXPECTED_IDENTIFIER)?)),
                Some(Ok(Token{kind:Keyword(Requirements),..})) => Ok(requirements = self.requirements()?),
                Some(Ok(Token{kind:Keyword(Objects),..})) => Ok(objects = self.vec_typed_list()?),
                Some(Ok(Token{kind:Keyword(Init),..})) => Ok(init = Some(self.init()?)), 
                Some(Ok(Token{kind:Keyword(Goal),..})) => Ok(goal = Some(self.precondition_expr()?)),
                Some(Ok(Token{kind:Keyword(Constraints),..})) => Ok(constraints = Some(self.pref_constraint_gd()?)),
                Some(Ok(Token{kind:Keyword(Metric),..})) => Ok(metric = Some(self.metric()?)),
                Some(Ok(Token{kind:Keyword(Length),..})) => Ok(length = Some(self.length()?)),
            }, "Expected :domain, :requirements, :objects.")?;
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        let domain = domain.unwrap();
        let init = init.unwrap();
        let goal = goal.unwrap();
        // let constraints = constraints.unwrap();
        // let metric = metric.unwrap();
        // let length = length.unwrap();
        Ok(Stmt::Problem(ast::Problem{name, domain, requirements, objects, init, goal, constraints, metric, length}))
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
        let mut constants = Vec::new();
        let mut predicates = Vec::new();
        let mut functions = Vec::new();
        let mut constraints = None;
        let mut actions = Vec::new();
        while self.lexer.next_if(|r| matches!(r, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            expect!(self, {Some(Ok(Token{kind:Colon,..})) => Ok(())}, EXPECTED_COLON)?;
            expect!(self, {
                Some(Ok(Token{kind:Keyword(Requirements),..})) => Ok(requirements = self.requirements()?),
                Some(Ok(Token{kind:Keyword(Types),..})) => Ok(types = self.vec_typed_list()?),
                Some(Ok(Token{kind:Keyword(Constants),..})) => Ok(constants = self.vec_typed_list()?),
                Some(Ok(Token{kind:Keyword(Predicates),..})) => Ok(predicates = self.predicates()?),
                Some(Ok(Token{kind:Keyword(Functions),..})) => Ok(functions = self.functions()?),
                Some(Ok(Token{kind:Keyword(Constraints),..})) => Ok(constraints = Some(self.constraint_gd()?)),
                Some(Ok(Token{kind:Keyword(Action),..})) => Ok(actions.push(self.basic_action()?)),
                Some(Ok(t @ Token{kind:Keyword(DurativeAction),..})) => Ok(actions.push(self.durative_action(t)?)),
                Some(Ok(t @ Token{kind:Keyword(Derived),..})) => Ok(actions.push(self.derived_action(t)?)),
            }, "Expected :requirements, :types, :constants :predicates, :functions, :constraints: or domain body (actions).")?;
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..})) => Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        Ok(Stmt::Domain(ast::Domain{name, requirements, types, functions, constants, predicates, constraints, actions}))
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
mod parser_tests {
    use enumset::{EnumSet, enum_set};

    // use crate::htn::parser::{Parser, Error, statement::{Stmt, StmtKind, Block}, expression::{Expr, ExprKind}, tokens::{Span, Literal::*}};
    use super::Parser;
    use super::ast::*;
    fn assert_equals_or_print_compile_error(code:&str, stmt:Stmt) {
        let mut parser = Parser::new(code, None);
        let result = parser.next().unwrap();
        if result.is_ok() {
            assert_eq!(result, Ok(stmt));
            assert_eq!(parser.next(), None);
        } else {
            println!("{}", result.unwrap_err());
            assert!(false);
        }
    }
    #[test]
    fn test_domain() {
        let code = "(define (domain test) (:requirements :strips :typing) (:types hand - object water - beverage) (:predicates (warm ?o - object)) (:action test :parameters (?h - hand ?b - beverage) :precondition (cold ?h) :effect (warm ?b)))";
        assert_equals_or_print_compile_error(code, Stmt::Domain(Domain{
            name:"test", 
            requirements:enum_set!(Requirements::Strips | Requirements::Typing), 
            types:vec![List::Typed(vec!["hand"], "object"),
                       List::Typed(vec!["water"], "beverage")], 
            predicates:vec![AtomicFSkeleton{name:"warm", variables:vec![List::Typed(vec!["o"], "object")]}], 
            functions:Vec::new(),
            constraints:None,
            constants:Vec::new(),
            actions:vec![Action::Basic(BasicAction{
                name:"test", 
                parameters:vec![List::Typed(vec!["h"], "hand"), List::Typed(vec!["b"], "beverage")],
                precondition:Some(PreconditionExpr::GD(GD::AtomicFormula("cold", vec![Term::Variable("h")]))),
                effect:Some(Effect::AtomicFormula("warm", vec![Term::Variable("b")]))
            })]
        }));
    }

    #[test]
    fn test_problem() {
        let code = "(define (problem test) (:domain barman) (:objects shaker1 - shaker) (:init (ontable shaker1)) (:goal (and (contains shot1 cocktail1))))";
        assert_equals_or_print_compile_error(code, Stmt::Problem(Problem{
                name:"test",
                domain:"barman",
                requirements: EnumSet::empty(),
                objects:vec![List::Typed(vec!["shaker1"], "shaker")],
                init: vec![Init::AtomicFormula("ontable", vec![Term::Name("shaker1")])],
                goal: PreconditionExpr::And(vec![PreconditionExpr::GD(GD::AtomicFormula("contains", vec![Term::Name("shot1"), Term::Name("cocktail1")]))]),
                constraints: None,
                metric: None,
                length: None
            }))
    }
    
}

#[cfg(test)]
mod error_tests {
    use std::str::FromStr;

    use crate::parser::tokens::Span;

    use super::{Error, tokens::Token};

    #[test]
    fn test_errors() {
        println!("{}", Error::UnexpectedToken{t:Token::new(1, 13, 3, Some("test.pddl"), "    Wake up Neo.", super::tokens::TokenKind::Comma), suggestion: "knock knock knock" });
        println!("{}", Error::UnsetRequirement{t:Token::new(2, 10, 3, Some("test2.pddl"), "(:action def)", super::tokens::TokenKind::Comma), requirement: crate::parser::ast::Requirements::DurationInequalities });
        println!("{}", Error::OmitedRequiredStatement{t:Token::new(3, 10, 6, Some("test3.pddl"), "(:action figure)", super::tokens::TokenKind::Comma), suggestion: "Add :parameters statement."});
        println!("{}", Error::UnexpectedEOF{filename:None, suggestion:"Do something else."});
        println!("{}", Error::UnexpectedCharacter{filename:None, span:Span::new(4, 2, 1), line:"&^%$#"});
        if let Err(source) = i32::from_str_radix("a12", 10) {
            println!("{}", Error::ParseIntError{filename:None, span:Span::new(5, 3, 2), line:"&^%$#", source});
        }
        if let Err(source) = f32::from_str("a12") {
            println!("{}", Error::ParseFloatError{filename:Some("/dev/random"), span:Span::new(6, 4, 3), line:"&^%$#", source});
        }
    }

}