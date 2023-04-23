use std::collections::{HashMap, HashSet};

use crate::parser::{ast::{Domain, Problem, List}, Error};

#[derive(Debug)]
pub struct Compiler {
    types: Vec<String>,
    type_parents: HashMap<String, u16>,
    variables: HashMap<String, u16>,
    type_map: Vec<u16>
}

impl<'a> Compiler {
    pub fn new(domain:Domain<'a>, problem:Problem<'a>) -> Result<Self, Error<'a>> {
        let mut compiler = Self{
            types:vec!["object".to_string()],
            type_parents:HashMap::from([("object".to_string(), 0 as u16)]),
            variables:HashMap::new(),
            type_map: Vec::new(),
        };
        compiler.build_type_map(&domain);
        Ok(compiler)
    }

    fn build_type_map(&mut self, domain:&Domain) {
        if domain.requirements.contains(crate::parser::ast::Requirements::Typing) {
            for r#type in &domain.types {
                match r#type {
                    List::Typed(identifiers, kind) => {
                        // TODO: Better search in type mapping
                        //    Currently using O(n) where n is amount of types.
                        let (kind_id, _) = self.types.iter().enumerate().find(|t| t.1 == kind).unwrap();
                        for subtype in identifiers {
                            if !self.type_parents.contains_key(*subtype) {
                                let size = self.types.len() as u16;
                                self.types.push((*subtype).to_owned());
                                self.type_parents.insert((*subtype).to_owned(), kind_id as u16);
                                size
                            } else {
                                panic!("Redeclared subtype")
                            };
                        }
                    },
                    _ => panic!("Unexpected AST in domain.types"),
                    
                }
                
            }
        }
    }
}

#[cfg(test)]
pub mod tests {
    use std::fs;

    use crate::parser::Parser;

    use super::Compiler;

    #[test]
    fn test_basic() {
        let domain = fs::read_to_string("domain.pddl").unwrap();
        let problem = fs::read_to_string("problem_5_10_7.pddl").unwrap();
        let mut parser = Parser::new(domain.as_str(), Some("domain.pddl"));
        let domain = parser.next().unwrap().unwrap().unwrap_domain();
        let mut parser = Parser::new(problem.as_str(), Some("problem_5_10_7.pddl"));
        let problem = parser.next().unwrap().unwrap().unwrap_problem();
        let compiler = match Compiler::new(domain, problem) {
            Ok(c) => c, 
            Err(e) => { println!("{}", e); return },
        };
        println!("{:?}", compiler);
    }
}