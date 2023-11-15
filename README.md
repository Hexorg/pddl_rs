[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Build status](https://github.com/Hexorg/pddl_rs/actions/workflows/workflow.yml/badge.svg)](https://github.com/Hexorg/pddl_rs/actions/workflows/workflow.yml)
[![crates.io Version](https://img.shields.io/crates/v/pddl_rs.svg)](https://crates.io/crates/pddl_rs)

# pddl_rs

PDDL Planner based on [Daniel L. Kovacs' BNF definition](http://pddl4j.imag.fr/repository/wiki/BNF-PDDL-3.1.pdf) BNF Definition of PDDL. Includes basic planning algorithms inspired by [PDDL4J library](https://github.com/pellierd/pddl4j). Can solve simple planning problems.

From PDDL4J's Readme:

> PDDL was originally developed by Drew McDermott and the 1998 planning competition committee. It was inspired by the need to encourage the empirical comparison of planning systems and the exchange of planning benchmarks within the community. Its development improved the communication of research results and triggered an explosion in performance, expressivity and robustness of planning systems.
> 
> PDDL has become a de facto standard language for describing planning domains, not only for the competition but more widely, as it offers an opportunity to carry out empirical evaluation of planning systems on a growing collection of generally adopted standard benchmark domains. The emergence of a language standard will have an impact on the entire field, influencing what is seen as central and what peripheral in the development of planning systems.

## Example

```rust
use std::fs;
use std::path::PathBuf;
use pddl_rs::{Sources, Objects, search::{a_star, AstarInternals}};
let domain_filename = PathBuf::from("sample_problems/simple_domain.pddl");
let problem_filename = PathBuf::from("sample_problems/simple_problem.pddl");
let sources = Sources::load(domain_filename, problem_filename);
let (domain, problem) = sources.parse();
let c_problem = sources.compile(&domain, &problem);
println!("Compiled problem needs {} bits of memory and uses {} actions.", c_problem.memory_size, c_problem.actions.len());
let mut args = AstarInternals::new(&c_problem.action_graph);
if let Some(solution) = a_star(&c_problem, Some(&domain), Some(&problem), &mut args) {
    println!("Solution is {} actions long.", solution.len());
    for action_id in &solution {
        let action = c_problem.actions.get(*action_id as usize).unwrap();
        println!("\t{}{:?}", domain.actions[action.domain_action_idx as usize].name(), action.args.iter().map(|(row, col)| problem.objects.get_object_name(*row,*col).1).collect::<Vec<&str>>());
}
}
```

The code is avilable on [GitHub](https://github.com/Hexorg/pddl_rs)