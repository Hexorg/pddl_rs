# pddl_rs

PDDL Parsing library based on [Daniel L. Kovacs' BNF definition](http://pddl4j.imag.fr/repository/wiki/BNF-PDDL-3.1.pdf) BNF Definition of PDDL. Future plans include adding planning algorithms to reflect [PDDL4J library](https://github.com/pellierd/pddl4j)

From PDDL4J's Readme:

> PDDL was originally developed by Drew McDermott and the 1998 planning competition committee. It was inspired by the need to encourage the empirical comparison of planning systems and the exchange of planning benchmarks within the community. Its development improved the communication of research results and triggered an explosion in performance, expressivity and robustness of planning systems.
> 
> PDDL has become a de facto standard language for describing planning domains, not only for the competition but more widely, as it offers an opportunity to carry out empirical evaluation of planning systems on a growing collection of generally adopted standard benchmark domains. The emergence of a language standard will have an impact on the entire field, influencing what is seen as central and what peripheral in the development of planning systems.

## Example

```rust
use std::fs;
use pddl_rs::{compiler::{CompiledProblem, compile_problem}, search::a_star, parser::{parse_domain, parse_problem}};
let domain_filename = "sample_problems/simple_domain.pddl";
let problem_filename = "sample_problems/simple_problem.pddl"
let domain_src = fs::read_to_string(domain_filename).unwrap();
let domain = match parse_domain(&domain_src) {
    Err(e) => {e.report(domain_filename).eprint((domain_filename, ariadne::Source::from(&domain_src))); panic!() },
    Ok(d) => d,
};
let problem_src = fs::read_to_string(problem_filename).unwrap();
let problem = match parse_problem(&problem_src, domain.requirements) {
    Err(e) => {e.report(problem_filename).eprint((problem_filename, ariadne::Source::from(&problem_src))); panic!() },
    Ok(p) => p
};
let c_problem = match compile_problem(&domain, &problem) {
    Err(e) => {e.report(problem_filename).eprint((problem_filename, ariadne::Source::from(&problem_src))); panic!() },
    Ok(cd) => cd,
};
println!("Compiled problem needs {} bits of memory and uses {} actions.", c_problem.memory_size, c_problem.actions.len());
let solution = a_star(&c_problem);
println!("Solution is {} actions long.", solution.len());
for action_id in &solution {
    let action = c_problem.actions.get(*action_id).unwrap();
    println!("\t{}{:?}", action.name.1, action.args.iter().map(|(_, s)| *s).collect::<Vec<&str>>());
}
```

The code is avilable on [GitHub](https://github.com/Hexorg/pddl_rs)