use std::iter::Peekable;
use std::str::{CharIndices, Lines};

use super::tokens::{Token, Span, TokenKind, OpToken, KeywordToken, Literal};
use super::Error;
use TokenKind::*;
use OpToken::*;
use KeywordToken::*;


pub struct Lexer<'a> { 
    text:&'a str,
    filename: Option<&'a str>,
    lines: Peekable<Lines<'a>>,
    it: Peekable<CharIndices<'a>>,
    line: usize, // current source line, used for error reporting by Tokens
    col: usize, // current source column, used for error reporting by Tokens
    stash: Vec<Token<'a>>, // stash of tokens to return in leu of it.peek_two()
}

impl<'a> Lexer<'a> {
    pub fn new(text:&'a str, filename:Option<&'a str>) -> Self {
        Self{
            text,
            it:text.char_indices().peekable(), 
            line:1,
            lines:text.lines().peekable(),
            col:1,
            filename,
            stash:Vec::new(),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token<'a>, Error<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.stash.len() > 0 {
            Some(Ok(self.stash.pop().unwrap()))
        } else {
            if let Some((offset, c)) = self.next_char() {
                // println!("Consumed up to: line:{} col:{} offset:{} char:{:?}", self.line, self.col, offset, c);
                let new_token = match c {
                    ':' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Colon))),
                    '(' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), OpenParenthesis))),
                    ')' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), CloseParenthesis))),
                    ',' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Comma))),
                    '|' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Or)))),
                    '&' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(And)))),
                    '.' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Dot))),
                    '?' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), QuestionMark))),
                    '=' => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Equals)))),
                    '-' => match self.it.peek() {
                        Some((_, '=')) => {let t = Token::new(self.line, self.col, 2, self.filename.clone(), self.lines.peek().unwrap(), Op(SubtractFrom)); self.it.next(); Some(Ok(t))}
                        _ => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Minus)))),
                    },
                    '+' => match self.it.peek() {
                        Some((_, '=')) => {let t = Token::new(self.line, self.col, 2, self.filename.clone(), self.lines.peek().unwrap(), Op(AddTo)); self.it.next(); Some(Ok(t))}
                        _ => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Plus)))),
                    },
                    '/' => match self.it.peek() {
                        Some((_, '=')) => {let t = Token::new(self.line, self.col, 2, self.filename.clone(), self.lines.peek().unwrap(), Op(DivideBy)); self.it.next(); Some(Ok(t))}
                        _ => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Slash)))),
                    },
                    '*' => match self.it.peek() {
                        Some((_, '=')) => {let t = Token::new(self.line, self.col, 2, self.filename.clone(), self.lines.peek().unwrap(), Op(MultiplyBy)); self.it.next(); Some(Ok(t))}
                        _ => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Star)))),
                    },
                    '>' => match self.it.peek() {
                        Some((_, '=')) => {let t = Token::new(self.line, self.col, 2, self.filename.clone(), self.lines.peek().unwrap(), Op(GreaterOrEquals)); self.it.next(); Some(Ok(t))}
                        _ => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Greater)))),
                    },
                    '<' => match self.it.peek() {
                        Some((_, '=')) => {let t = Token::new(self.line, self.col, 2, self.filename.clone(), self.lines.peek().unwrap(), Op(SmallerOrEquals)); self.it.next(); Some(Ok(t))}
                        _ => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Smaller)))),
                    },
                    '!' => match self.it.peek() {
                        Some((_, '=')) => {let t = Token::new(self.line, self.col, 2, self.filename.clone(), self.lines.peek().unwrap(), Op(NotEquals)); self.it.next(); Some(Ok(t))},
                        _ => Some(Ok(Token::new(self.line, self.col, 1, self.filename.clone(), self.lines.peek().unwrap(), Op(Not))))
                    },
                    '"' => {Some(self.string(offset))},
                    c if c.is_whitespace() => { 
                        self.col += 1;
                        return self.next()
                    }
                    c if (c.is_alphabetic() || c == '_') => Some(self.identifier(offset)),
                    c if c.is_digit(10) => Some(self.number(offset)),
                    _ => Some(Err(Error::UnexpectedCharacter{filename:self.filename.clone(), span:Span::new(self.line, self.col, 1), line:self.lines.peek().unwrap()}))
                };
                if let Some(result) = &new_token {
                    match result {
                        Ok(t) => self.col += t.span.len,
                        Err(_) => self.col += 1,
                    }
                }
                new_token
            } else {
                None
            }
        }
    }
}

impl<'a> Lexer<'a> {
    fn next_char(&mut self) -> Option<(usize, char)> {
        let c = self.it.next();
        match c {
            // Newline handler:
            Some((_, '\n')) => {
                self.col = 1; 
                self.line += 1; 
                self.lines.next();
                self.next_char()},

            // Comments:
            Some((_, ';')) => {while let Some(_) = self.it.next_if(|(_,c)| *c != '\n') {}; self.next_char()},
            _ => c,
        }
    }

    fn string(&mut self, offset:usize) -> Result<Token<'a>, Error<'a>> {
        self.col += 1; // increment col for the first '"' since self.col += token.len() will only count the string itself
        let mut len = 0;
        let offset = offset + '"'.len_utf8();
        while let Some(_) = self.it.next_if(|(_,c)| *c != '"' ) { len += 1; }
        let slice = if let Some((string_end, _)) = self.it.next() { &self.text[offset..string_end] } else { &self.text[offset..]};
        let r = Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Literal(Literal::S(slice))));
        self.col += 1; // count the last '"'
        r
    }

    fn number(&mut self, offset:usize) -> Result<Token<'a>, Error<'a>> {
        let mut contains_dot = false;
        let mut len = 1;
        while let Some((_,c)) = self.it.next_if(|(_,c)| c.is_digit(10) || *c == '.') { len += 1; if c == '.' { contains_dot = true; }}
        let slice = if let Some((number_end, _)) = self.it.peek() { &self.text[offset..*number_end]} else { &self.text[offset..]};
        if contains_dot {
            match slice.parse::<f64>() {
                Ok(literal) => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Literal(Literal::F(literal)))),
                Err(source) => Err(Error::ParseFloatError{filename:self.filename.clone(), span:Span::new(self.line, self.col, 1), line:self.lines.peek().unwrap(), source}),
            }
        } else {
            match slice.parse::<i64>() {
                Ok(literal) => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Literal(Literal::I(literal)))),
                Err(source) => Err(Error::ParseIntError{filename:self.filename.clone(), span:Span::new(self.line, self.col, 1), line:self.lines.peek().unwrap(), source}),
            }
        }
    }

    fn identifier(&mut self, offset:usize) -> Result<Token<'a>, Error<'a>> {
        let mut len = 1;
        while let Some(_) = self.it.next_if(|(_,c)| (c.is_alphanumeric() || *c == '_' || *c == '-')) { len += 1; }
        let slice = if let Some((identifier_end,_)) = self.it.peek() { &self.text[offset..*identifier_end]} else { &self.text[offset..]};
        let token = match slice {
            "define" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Define))),
            "domain" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Domain))),
            "problem" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Problem))),

            "requirements" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Requirements))),
            "types" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Types))),
            "constants" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Constants))),
            "functions" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Functions))),
            "constraints" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Constraints))),
            "predicates" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Predicates))),

            "action" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Action))),
            "durative-action" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(DurativeAction))),
            "derived" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Derived))),
            "parameters" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Parameters))),
            "precondition" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Precondition))),
            "condition" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Condition))),
            "duration" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Duration))),
            "effect" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Effect))),
            "metric" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Metric))),
            "length" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Length))),
            "preference" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Preference))),

            "objects" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Objects))),
            "init" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Init))),
            "goal" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Goal))),
            
            "assign" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Assign))),
            "scaleUp" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(ScaleUp))),
            "scaleDown" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(ScaleDown))),
            "increase" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Increase))),
            "decrease" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Decrease))),
            "forall" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Forall))),
            "at" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(At))),
            "end" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(End))),
            "when" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(When))),
            "start" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Start))),
            "over" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Over))),
            "all" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(All))),
            "always" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Always))),
            "sometime" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Sometime))),
            "within" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Within))),
            "at-most-once" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(AtMostOnce))),
            "sometime-after" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(SometimeAfter))),
            "sometime-before" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(SometimeBefore))),
            "always-within" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(AlwaysWithin))),
            "hold-during" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(HoldDuring))),
            "hold-after" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(HoldAfter))),
            "either" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Either))),
            "imply" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Keyword(Imply))),

            "or" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Op(Or))),
            "not" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Op(Not))),
            "and" => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Op(And))),
        
            _ => Ok(Token::new(self.line, self.col, len, self.filename.clone(), self.lines.peek().unwrap(), Identifier(slice)))
        };
        token
    }
}

#[cfg(test)]
mod tests {
    use super::{Lexer, Token, TokenKind::*, OpToken::*};
    #[test]
    fn test_include() {
        let code = "((:operator (!drive ?x ?y ?z ?p ?time)\n))";
        let mut lines = code.lines().peekable();
        let mut l = Lexer::new(code, None);
        assert_eq!(l.next(), Some(Ok(Token::new(1, 1, 1, None, lines.peek().unwrap(), OpenParenthesis))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 2, 1, None, lines.peek().unwrap(), OpenParenthesis))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 3, 1, None, lines.peek().unwrap(), Colon))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 4, 8, None, lines.peek().unwrap(), Identifier("operator")))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 13, 1, None, lines.peek().unwrap(), OpenParenthesis))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 14, 1, None, lines.peek().unwrap(), Op(Not)))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 15, 5, None, lines.peek().unwrap(), Identifier("drive")))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 21, 1, None, lines.peek().unwrap(), QuestionMark))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 22, 1, None, lines.peek().unwrap(), Identifier("x")))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 24, 1, None, lines.peek().unwrap(), QuestionMark))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 25, 1, None, lines.peek().unwrap(), Identifier("y")))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 27, 1, None, lines.peek().unwrap(), QuestionMark))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 28, 1, None, lines.peek().unwrap(), Identifier("z")))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 30, 1, None, lines.peek().unwrap(), QuestionMark))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 31, 1, None, lines.peek().unwrap(), Identifier("p")))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 33, 1, None, lines.peek().unwrap(), QuestionMark))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 34, 4, None, lines.peek().unwrap(), Identifier("time")))));
        assert_eq!(l.next(), Some(Ok(Token::new(1, 38, 1, None, lines.peek().unwrap(), CloseParenthesis))));
        lines.next();
        assert_eq!(l.next(), Some(Ok(Token::new(2, 1, 1, None, lines.peek().unwrap(), CloseParenthesis))));
        assert_eq!(l.next(), Some(Ok(Token::new(2, 2, 1, None, lines.peek().unwrap(), CloseParenthesis))));
        assert_eq!(l.next(), None);
    }

}