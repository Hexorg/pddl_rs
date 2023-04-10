pub mod tokens;
pub mod lexer;
pub mod ast;

use ast::Stmt;
use enumset::{EnumSet, enum_set};
use lexer::Lexer;


use self::ast::{BasicAction, TypedList, Requirements, TypedFunction, FunctionTypeKind, CallableDeclaration};

use tokens::{Token, Span, TokenKind, KeywordToken, BinOpToken, Literal};


use std::{fmt, num::{ParseFloatError, ParseIntError}};

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
                Some(Ok(Token{kind:Keyword(Objects),..})) => Ok(objects = self.typed_list_repeated()?),
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

    /// ```bnf 
    /// <action_def> ::= (:action <action-symbol> 
    ///                 :parameters (<typed list (variable)>) 
    ///                 [:precondition <emptyOr (pre-GD)>]
    ///                 [:effect <emptyOr (effect)>] 
    ///                 )
    /// <durative-action-def> ::= (:durative-action <da-symbol>
    ///                 :parameters (<typed list (variable)>)
    ///                 :duration <duration-constraint>
    ///                 :condition <emptyOr (da-GD)>
    ///                 :effect <emptyOr (da-effect)>
    ///                 )
    /// <derived-def> ::= (:derived <atomic formula skeleton> <GD>)
    /// ```
    fn action(&mut self, token:Token<'a>) -> Result<ast::Action<'a>, Error<'a>> {
        use TokenKind::{Keyword, Identifier, QuestionMark, Colon, OpenParenthesis, CloseParenthesis};
        use KeywordToken::{Parameters, Precondition, Condition, Duration, Effect, Derived};
        if let Token{kind:Keyword(Derived),..} = token {
            if self.requirements.contains(Requirements::DerivedPredicates) {
                let predicate = self.callable_declaration()?;
                let expr = self.expr()?;
                Ok(ast::Action::Derived {predicate, expr})
            } else {
                Err(Error::UnsetRequirement{t:token, requirement: Requirements::DerivedPredicates})
            }
        } else {
            let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
            let mut parameters = Vec::new();
            let mut precondition = None;
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
                    Some(Ok(Token{kind:Keyword(Precondition),..})) => Ok(precondition = Some(self.expr()?)),   
                    Some(Ok(Token{kind:Keyword(Condition),..})) => Ok(precondition = Some(self.expr()?)),   
                    Some(Ok(Token{kind:Keyword(Effect),..})) => Ok(effect = Some(self.expr()?)),  
                    Some(Ok(Token{kind:Keyword(Duration),..})) => Ok(duration = Some(self.expr()?)),   
                }, "Expected Action properties.")?;
            }
            let basic_action = BasicAction{name, parameters, precondition, effect};
            if let Token{kind:Keyword(KeywordToken::Action),..} = token {
                Ok(ast::Action::Basic(basic_action))
            } else if let Token{kind:Keyword(KeywordToken::DurativeAction),..} = token {
                if self.requirements.contains(Requirements::DurativeActions) {
                    if duration.is_some() {
                        Ok(ast::Action::Durative{a:basic_action, duration:duration.unwrap()})
                    } else {
                        Err(Error::OmitedRequiredStatement { t: token, suggestion: "Add :duration statement." })
                    }
                    
                } else {
                    Err(Error::UnsetRequirement{t:token, requirement: Requirements::DurativeActions})
                }
            } else {
                Err(Error::UnexpectedToken { t: token, suggestion: "Expected :action, :durative-action, or :derived." })
            }
        }
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
        use TokenKind::{OpenParenthesis, CloseParenthesis, BinOp};
        use BinOpToken::Minus;
        let mut result = Vec::new();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            let function = self.callable_declaration()?;
            let has_minus = if let Some(Ok(Token{kind:BinOp(Minus),..})) = self.lexer.peek() { true } else { false};
            let kind = if has_minus {
                let minus_token = self.lexer.next().unwrap().unwrap();
                if self.requirements.contains(Requirements::NumericFluents) {
                    FunctionTypeKind::Numeric(expect!(self, {Some(Ok(Token{kind:TokenKind::Literal(Literal::I(val)),..})) => Ok(val)}, "Expected a number - :numeric-fluents is required.")?)
                } else if self.requirements.contains(Requirements::Typing) && self.requirements.contains(Requirements::ObjectFluents) {
                    FunctionTypeKind::Typed(self.parse_type()?)
                } else {
                    return Err(Error::UnsetRequirement{t: minus_token, requirement:Requirements::Typing });
                }
            } else {
                FunctionTypeKind::None
            };
            result.push(TypedFunction{function, kind});
            expect!(self, {Some(Ok(Token{kind:CloseParenthesis,..}))=>Ok(())}, EXPECTED_CLOSE_PARENTHESIS)?;
        }
        Ok(result)
    }

    fn predicates(&mut self) -> Result<Vec<CallableDeclaration<'a>>, Error<'a>> {
        use TokenKind::{OpenParenthesis, CloseParenthesis};
        let mut predicates = Vec::new();
        while self.lexer.next_if(|t| matches!(t, Ok(Token{kind:OpenParenthesis,..}))).is_some() {
            predicates.push(self.callable_declaration()?);
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
    fn callable_declaration(&mut self) -> Result<CallableDeclaration<'a>, Error<'a>> {
        use TokenKind::{Identifier, QuestionMark};
    
        let name = expect!(self, {Some(Ok(Token{kind:Identifier(s),..})) => Ok(s)}, EXPECTED_IDENTIFIER)?;
        let mut variables = Vec::new();
        while let Some(Ok(Token{kind:QuestionMark,..})) = self.lexer.peek() {
            variables.push(self.typed_list_variable()?);
        }
        Ok(CallableDeclaration{name, variables})

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
    /// <types-def> ::= (:types <typed list (name)>)
    /// ```
    fn typed_list_repeated(&mut self) -> Result<Vec<TypedList<'a>>, Error<'a>> {
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
                Some(Ok(Token{kind:Keyword(Types),..})) => Ok(types = self.typed_list_repeated()?),
                Some(Ok(Token{kind:Keyword(Constants),..})) => Ok(constants = self.typed_list_repeated()?),
                Some(Ok(Token{kind:Keyword(Predicates),..})) => Ok(predicates = self.predicates()?),
                Some(Ok(Token{kind:Keyword(Functions),..})) => Ok(functions = self.functions()?),
                Some(Ok(Token{kind:Keyword(Constraints),..})) => Ok(constraints = Some(self.expr()?)),
                Some(Ok(t @ Token{kind:Keyword(Action | DurativeAction | Derived),..})) => Ok(actions.push(self.action(t)?)),
                // Some(Ok(t @ Token{kind:Keyword(DurativeAction),..})) => Ok(actions.push(self.durative_action(t)?)),
                // Some(Ok(t @ Token{kind:Keyword(Derived),..})) => Ok(actions.push(self.derived_action(t)?)),
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
    use super::ast::{Stmt, Domain, Problem, Requirements, TypedList, CallableDeclaration, Action, BasicAction, Expr};
    #[test]
    fn test_domain() {
        let code = "(define (domain test) (:requirements :strips :typing) (:types hand - object water - beverage) (:predicates (warm ?o - object)) (:action test :parameters (?h - hand ?b - beverage) :precondition (cold ?h) :effect (warm ?b)))";
        let mut parser = Parser::new(code, None);
        assert_eq!(parser.next(), Some(Ok(Stmt::Domain(Domain{
            name:"test", 
            requirements:enum_set!(Requirements::Strips | Requirements::Typing), 
            types:vec![TypedList{identifiers:vec!["hand"], kind:Some("object")},
                       TypedList{identifiers:vec!["water"], kind:Some("beverage")}], 
            predicates:vec![CallableDeclaration{name:"warm", variables:vec![TypedList{identifiers:vec!["o"], kind:Some("object")}]}], 
            functions:Vec::new(),
            constraints:None,
            constants:Vec::new(),
            actions:vec![Action::Basic(BasicAction{
                name:"test", 
                parameters:vec![TypedList{identifiers:vec!["h"], kind:Some("hand")}, TypedList{identifiers:vec!["b"], kind:Some("beverage")}],
                precondition:Some(Expr::Literal { name: "cold", variables: vec!["h"] }),
                effect:Some(Expr::Literal { name: "warm", variables: vec!["b"] })
            })]
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