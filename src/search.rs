use std::{collections::{BinaryHeap, HashMap}, hash::Hash};
pub mod routing;
use crate::compiler::{CompiledProblem, Runnable};

#[derive(Debug, PartialEq, Eq, Clone)]
struct SolutionNode {
    action_id: Option<usize>,
    state: Vec<bool>,
    cost:i64,
    estimate:i64,
}

impl Ord for SolutionNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.estimate.cmp(&self.estimate)
    }
}

impl PartialOrd for SolutionNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for SolutionNode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.state.hash(state);
        self.cost.hash(state);
    }
}


impl SolutionNode {
    pub fn new(size:usize) -> Self {
        Self{action_id:None, cost:0, estimate:i64::MAX, state:vec![false;size]}
    }
}

pub fn a_star(problem:&CompiledProblem) -> Vec<usize> {
    let mut functions = vec![0];
    let mut start = SolutionNode::new(problem.memory_size);
    problem.init.run_mut(&mut start.state, &mut functions);
    // The set of discovered nodes that may need to be (re-)expanded.
    // Initially, only the start node is known.
    // This is usually implemented as a min-heap or priority queue
    let mut open_set = BinaryHeap::new();
    open_set.push(start.clone());

    // Cheapest path from start to node n
    let mut came_from:HashMap<SolutionNode, SolutionNode> = HashMap::new();
    let mut cheapest_path_to_map:HashMap<Vec<bool>, i64> = HashMap::new();
    // For node n, fScore[n] := gScore[n] + h(n). fScore[n] represents our current best guess as to
    // how cheap a path could be from start to finish if it goes through n.
    // let mut fScore = HashMap::new(); // default value of Infinity
    // fScore[&start] = h(&start_state[..]);

    while let Some(mut current) = open_set.pop() {
        functions[0] = current.cost;
        if problem.goal.run(&current.state, &functions) {
            let mut path = Vec::with_capacity(came_from.len());
            path.push(current.action_id.unwrap());
            while let Some(next) = came_from.get(&current) {
                if let Some(action_id) = (*next).action_id {
                    path.push(action_id);
                } else {
                    if came_from.get(next).is_some() {
                        panic!("Expected last node in a path.");
                    }
                }
                current = next.clone();
            }
            path.reverse();
            return path;
        }


        // for each applicable action
        for (i, action) in problem.actions.iter().enumerate() {
            if action.precondition.run(&current.state, &functions) {
                let mut new_node = SolutionNode{action_id:Some(i), cost:current.cost, estimate:current.estimate, state:current.state.clone()};
                functions[0] = new_node.cost;
                action.effect.run_mut(&mut new_node.state, &mut functions);
                new_node.cost = functions[0];
                new_node.estimate = new_node.cost + 1;
                if new_node.estimate < *cheapest_path_to_map.get(&new_node.state).unwrap_or(&i64::MAX) {
                    // print!("new state after {}. ", action.name.1);
                    came_from.insert(new_node.clone(), current.clone());
                    cheapest_path_to_map.insert(new_node.state.clone(), new_node.cost);
                    // fScore.insert(&new_state, h(&new_state));
                    open_set.push(new_node);
                }
            }
        }
    }
    println!("No solution found");
    Vec::new()
}

#[cfg(test)]
mod test {
    use crate::{compiler::{Instruction, CompiledProblem, CompiledAction, compile_problem}, search::a_star, parser::{parse_domain, parse_problem}};

    #[test]
    fn basic_search() {
        use Instruction::*;
        let p = CompiledProblem{ 
            memory_size: 1, 
            actions: vec![
                CompiledAction{ 
                    name: (0..0, "set"), args:vec![(1..1, "a"), (1..1, "a")], 
                    precondition: vec![ReadState(0), Not], 
                    effect: vec![And(0), SetState(0)] 
                }, CompiledAction{
                    name: (0..0, "unset"), args:vec![(1..1, "a"), (1..1, "a")], 
                    precondition: vec![ReadState(0)], 
                    effect: vec![And(0), Not, SetState(0)]
                }], 
            init: vec![And(0), Not, SetState(0)], 
            goal: vec![ReadState(0)]
        };
        assert_eq!(a_star(&p), vec![0])
    }

    #[test]
    #[ignore = "takes too long without optimizations"]
    fn barman_pddl_search() -> std::io::Result<()> {
        let solution = full_search("sample_problems/barman/domain.pddl", "sample_problems/barman/problem_5_10_7.pddl")?;
        assert_eq!(solution, vec![182, 6, 404]);
        Ok(())
    }

    #[test]
    fn simple_pddl_search() -> std::io::Result<()>{
        let solution = full_search("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl")?;
        assert_eq!(solution, vec![182, 219, 6, 404]);
        Ok(())
    }

    fn full_search(domain_filename:&'static str, problem_filename:&'static str) -> std::io::Result<Vec<usize>> {
        use std::{fs, env, path::Path};
        let workspace_path = match env::var("GITHUB_WORKSPACE ") {
            Ok(path) => path,
            Err(_) => match env::var("CARGO_MANIFEST_DIR") {
                Ok(path) => path,
                Err(_) => panic!("Neither GITHUB_WORKSPACE nor CARGO_MANIFEST_DIR is unset."),
            }
        };
        let p = Path::new(&workspace_path);
        let domain_src = fs::read_to_string(p.join(domain_filename))?;
        let problem_src = fs::read_to_string(p.join(problem_filename))?;
        let domain = match parse_domain(&domain_src) {
            Err(e) => {e.report(domain_filename).eprint((domain_filename, ariadne::Source::from(&domain_src)))?; panic!() },
            Ok(d) => d,
        };
        let problem = match parse_problem(&problem_src, domain.requirements) {
            Err(e) => {e.report(problem_filename).eprint((problem_filename, ariadne::Source::from(&problem_src)))?; panic!() },
            Ok(p) => p
        };
        let c_problem = match compile_problem(&domain, &problem) {
            Err(e) => {e.report(problem_filename).eprint((problem_filename, ariadne::Source::from(&problem_src)))?; panic!() },
            Ok(cd) => cd,
        };
        println!("Compiled problem needs {} bits of memory and uses {} actions.", c_problem.memory_size, c_problem.actions.len());
        let solution = a_star(&c_problem);
        println!("Solution is {} actions long.", solution.len());
        for action_id in &solution {
            let action = c_problem.actions.get(*action_id).unwrap();
            println!("\t{}{:?}", action.name.1, action.args.iter().map(|(_, s)| *s).collect::<Vec<&str>>());
        }
        Ok(solution)
    }
}