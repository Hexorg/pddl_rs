
pub mod parser;
//pub mod compiler;

#[cfg(test)]
mod tests {
    use ariadne::Source;
    use enumset::EnumSet;

    use crate::parser::{self, ast::Requirement};

    #[test]
    fn test_domain() {
        let filename = "problem_5_10_7.pddl";
        let code = std::fs::read_to_string(filename).unwrap();
        match parser::parse_problem(&code, 0, EnumSet::EMPTY) {
            Ok((_, domain)) => println!("{:?}", domain),
            Err(nom::Err::Incomplete(_)) => println!("Incomplete!"),
            Err(nom::Err::Failure(e)) |
            Err(nom::Err::Error(e)) => {e.report(&filename).eprint((filename, Source::from(&code)));},
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