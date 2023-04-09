pub mod pddl;
pub mod tokens;

use std::{fmt, num::{ParseFloatError, ParseIntError}};

use tokens::{Span, Token};


#[derive(PartialEq, Clone, Debug)]
pub enum Error<'a> {
    UnexpectedToken{t:Token<'a>, suggestion:&'static str},
    UnexpectedEOF{filename:Option<&'a str>, suggestion:&'static str},
    UnexpectedCharacter{filename:Option<&'a str>, span:Span, line: &'a str},
    ParseFloatError{filename:Option<&'a str>, span:Span, line: &'a str, source:ParseFloatError},
    ParseIntError{filename:Option<&'a str>, span:Span, line: &'a str, source:ParseIntError}
}

impl<'a> std::error::Error for Error<'a> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::UnexpectedToken{..} => None,
            Self::UnexpectedEOF{..} => None,
            Self::UnexpectedCharacter{..} => None,
            Self::ParseFloatError{source,..} => Some(source),
            Self::ParseIntError{source,..} => Some(source),
        }
    }
}

impl<'a> std::fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::parser::tokens::Span;

    use super::{Error, tokens::Token};

    #[test]
    fn test_errors() {
        println!("{}", Error::UnexpectedToken{t:Token::new(30, 13, 3, Some("test.pddl"), "    Wake up Neo.", super::tokens::TokenKind::Comma), suggestion: "knock knock knock" });
        println!("{}", Error::UnexpectedEOF{filename:None, suggestion:"Do something else."});
        println!("{}", Error::UnexpectedCharacter{filename:None, span:Span::new(1, 2, 1), line:"&^%$#"});
        if let Err(source) = i32::from_str_radix("a12", 10) {
            println!("{}", Error::ParseIntError{filename:None, span:Span::new(1, 3, 2), line:"&^%$#", source});
        }
        if let Err(source) = f32::from_str("a12") {
            println!("{}", Error::ParseFloatError{filename:Some("/dev/random"), span:Span::new(1, 4, 3), line:"&^%$#", source});
        }
    }

}