use std::fs;
use bnf::{Grammar, ParseTree};

fn print_lhs(tree:&ParseTree) {
    use bnf::Term::*;
    match tree.lhs {
        Terminal(s) => println!("Term::Terminal({})", s),
        Nonterminal(s) => println!("Term::Nonterminal({})", s)
    }
    for subtree in tree.rhs_iter() {
        use bnf::ParseTreeNode::*;
        match subtree {
            Terminal (s) => println!("Subtree::Terminal: {}", s),
            Nonterminal(t) => { println!("Subtree::Nonterminal!\n\t"); print_lhs(t);},
        }
    }
}

fn main() {;
    let grammar: Result<Grammar,_> = fs::read_to_string("pddl.bnf").unwrap().parse();
    if grammar.is_err() {
        println!("{}", grammar.unwrap_err());
        return;
    }
    let grammar = grammar.unwrap();
    let input = fs::read_to_string("domain.pddl").unwrap();
    println!("Parsing: {}", input);
    for tree in grammar.parse_input(input.as_str()) {
        print_lhs(&tree);
    }
    

}
