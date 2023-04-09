
pub mod parser;

#[cfg(test)]
mod tests {
    use crate::parser;

    #[test]
    fn test_domain() {
        let filename = "domain.pddl";
        let code = std::fs::read_to_string(filename).unwrap();
        let mut parser = parser::pddl::Parser::new(code.as_str(), Some(filename));
        match parser.next() {
            Some(Ok(_)) => (),
            Some(Err(e)) => { println!("{}", e); assert!(false); },
            None => assert!(false),
        }
    }
}