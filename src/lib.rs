
pub mod parser;
pub mod compiler;

#[cfg(test)]
mod tests {
    use crate::parser;

    #[test]
    fn test_domain() {
        let filename = "problem_5_10_7.pddl";
        let code = std::fs::read_to_string(filename).unwrap();
        let mut parser = parser::Parser::new(code.as_str(), Some(filename));
        match parser.next() {
            Some(Ok(s)) => println!("{:?}", s),
            Some(Err(e)) => { println!("{}", e); assert!(false); },
            None => assert!(false),
        }
    }
}