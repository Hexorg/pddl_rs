use std::{
    collections::{BinaryHeap, HashMap},
    hash::Hash, fmt::Debug,
};
pub mod routing;
use crate::compiler::{CompiledProblem, Runnable, CompiledAction};

#[derive(PartialEq, Eq, Clone)]
pub struct SolutionNode {
    action_id: Option<usize>,
    state: Vec<bool>,
    functions: [i64;1],
    cost: i64,
    estimate: i64,
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
        self.functions.hash(state);
        self.cost.hash(state);
    }
}

impl Debug for SolutionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SolutionNode").field("action_id", &self.action_id).field("cost", &self.cost).field("estimate", &self.estimate).finish()
    }
}

impl SolutionNode {
    pub fn new(size: usize) -> Self {
        Self {
            action_id: None,
            cost: 0,
            estimate: i64::MAX,
            state: vec![false; size],
            functions: [0],
        }
    }
}

pub struct AstarInternals {
    open_set:BinaryHeap<SolutionNode>,
    came_from:HashMap<SolutionNode, SolutionNode>,
    cheapest_path_to_map:HashMap<Vec<bool>, i64>
}
impl AstarInternals {
    pub fn new() -> Self {
        Self { open_set: BinaryHeap::new(), came_from: HashMap::new(), cheapest_path_to_map: HashMap::new() }
    }
}

pub fn a_star(problem: &CompiledProblem, args:&mut AstarInternals) -> Option<Vec<usize>> {
    fn _test_action(action_idx:usize, action:&CompiledAction, current:&SolutionNode, cheapest_path_to_map: &HashMap<Vec<bool>, i64>) -> Option<SolutionNode> {
        if action.precondition.run(&current.state, &current.functions) {
            let mut new_node = SolutionNode {
                action_id: Some(action_idx),
                cost: current.cost,
                estimate: current.estimate,
                state: current.state.clone(),
                functions: current.functions.clone(),
            };
            new_node.functions[0] = new_node.cost;
            action.effect.run_mut(&mut new_node.state, &mut new_node.functions);
            new_node.cost = new_node.functions[0];
            new_node.estimate = new_node.cost + 1;
            if new_node.estimate
                < *cheapest_path_to_map
                    .get(&new_node.state)
                    .unwrap_or(&i64::MAX)
            {
                Some(new_node)
            } else {
                None
            }
        } else {
            None
        }
    }
    println!("Entering A*");
    if args.open_set.is_empty() {
        let mut start = SolutionNode::new(problem.memory_size);
        problem.init.run_mut(&mut start.state, &mut start.functions);
        args.open_set.push(start.clone());

    }


    while let Some(mut current) = args.open_set.pop() {
        println!("Checking out {:?}.", current);
        if problem.goal.run(&current.state, &current.functions) {
            let mut path = Vec::with_capacity(args.came_from.len());
            path.push(current.action_id.unwrap());
            while let Some(next) = args.came_from.get(&current) {
                if let Some(action_id) = (*next).action_id {
                    path.push(action_id);
                } else {
                    if args.came_from.get(next).is_some() {
                        panic!("Expected last node in a path.");
                    }
                }
                current = next.clone();
            }
            path.reverse();
            return Some(path);
        }
        // if problem.action_graph.len() > 0 && current.action_id.is_some() {
        //     if let Some(last_action) = current.action_id {
        //         // println!("\tAction graph for {} is {:?}", last_action, problem.action_graph[last_action]);
        //         for try_action in &problem.action_graph[last_action] {
        //             match try_action {
        //                 TryNode::Action(i) => if let Some(new_node) = _test_action(*i, &problem.actions[*i], &current, &args.cheapest_path_to_map) {
        //                     println!("\t\tUsing Action Graph {} can be run after {}", new_node.action_id.unwrap(), current.action_id.unwrap());
        //                     args.came_from.insert(new_node.clone(), current.clone());
        //                     args.cheapest_path_to_map.insert(new_node.state.clone(), new_node.cost);
        //                     args.open_set.push(new_node);
        //                 } else { println!("\t\tUsing Action Graph {} can NOT be run after {}", *i, current.action_id.unwrap())},
        //                 TryNode::PreemptionPoint => // There's a good chance open_set now contains a state that gets us closer to the goal. Recurse in and try to explore that space first.
        //                 if let Some(solution) = a_star(problem, args) {
        //                     return Some(solution)
        //                 },
        //             }
        //         }
        //     }
        // } else {
            // first iteration - try all actions
            // println!("Action graph size: {}, last action: {:?}", problem.action_graph.len(), current.action_id);
            for (i, action) in problem.actions.iter().enumerate() {
                if let Some(new_node) = _test_action(i, action, &current, &args.cheapest_path_to_map) {
                    // println!("\tUnable to use action graph. Can run {} after {:?}. ", new_node.action_id.unwrap(), current.action_id);
                    args.came_from.insert(new_node.clone(), current.clone());
                    args.cheapest_path_to_map.insert(new_node.state.clone(), new_node.cost);
                    args.open_set.push(new_node);
                }
            }
        }
    // }
    println!("Leaving A*");
    None
}

#[cfg(test)]
mod test {

    use enumset::EnumSet;

    use crate::{
        compiler::{compile_problem, Action, CompiledAction, CompiledProblem, Instruction, Optimization, action_graph::ActionGraph},
        parser::{parse_domain, parse_problem},
        search::{a_star, AstarInternals}, ReportPrinter,
        lib_tests::load_repo_pddl,
    };

    #[test]
    fn basic_search() {
        use Instruction::*;
        let p = CompiledProblem {
            memory_size: 1,
            actions: vec![
                CompiledAction {
                    domain_action_idx: 0,
                    args: vec![(1..1, "a"), (1..1, "a")],
                    precondition: vec![ReadState(0), Not],
                    effect: vec![And(0), SetState(0)],
                },
                CompiledAction {
                    domain_action_idx: 1,
                    args: vec![(1..1, "a"), (1..1, "a")],
                    precondition: vec![ReadState(0)],
                    effect: vec![And(0), Not, SetState(0)],
                },
            ],
            init: vec![And(0), Not, SetState(0)],
            goal: vec![ReadState(0)],
            action_graph: ActionGraph::new(),
        };
        let mut args = AstarInternals::new();
        assert_eq!(a_star(&p, &mut args), Some(vec![0]))
    }

    #[test]
    #[ignore = "takes too long without optimizations"]
    fn barman_pddl_search() -> std::io::Result<()> {
        let solution = full_search(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
            Optimization::all()
        )?;
        assert_eq!(solution, vec![182, 6, 404]);
        Ok(())
    }

    #[test]
    fn simple_pddl_search() -> std::io::Result<()> {
        let solution = full_search(
            "sample_problems/simple_domain.pddl",
            "sample_problems/simple_problem.pddl",
            Optimization::none()
        )?;
        assert_eq!(solution, vec![112, 131, 5, 255]);
        Ok(())
    }
    #[test]
    #[ignore = "Waiting for optimizations to be done"]
    fn simple_pddl_optimized_search() -> std::io::Result<()> {
        let solution = full_search(
            "sample_problems/simple_domain.pddl",
            "sample_problems/simple_problem.pddl",
            Optimization::all()
        )?;
        assert_eq!(solution, vec![18, 6, 14]);
        Ok(())
    }

    fn full_search(
        domain_filename: &'static str,
        problem_filename: &'static str,
        optimizations:EnumSet<Optimization>,
    ) -> std::io::Result<Vec<usize>> {
        let (domain_src, problem_src) = load_repo_pddl(domain_filename, problem_filename);
        let domain = parse_domain(&domain_src).unwrap_or_print_report(domain_filename, &domain_src);
        let problem = parse_problem(&problem_src, domain.requirements).unwrap_or_print_report(problem_filename, &problem_src);
        let c_problem = compile_problem(&domain, &problem, optimizations).unwrap_or_print_report(problem_filename, &problem_src);
        println!(
            "Compiled problem needs {} bits of memory and uses {} actions.",
            c_problem.memory_size,
            c_problem.actions.len()
        );
        println!("Action map:");
        for (idx, action) in c_problem.actions.iter().enumerate() {
            println!("\t{}: {}({})", idx, domain.actions[action.domain_action_idx].name().1, action.args.iter().map(|(_, i)| *i).collect::<Vec<&str>>().join(","));
        }
        let mut args = AstarInternals::new();
        let solution = a_star(&c_problem, &mut args).unwrap();
        println!("Solution is {} actions long.", solution.len());
        for action_id in &solution {
            let action = c_problem.actions.get(*action_id).unwrap();
            println!(
                "\t{}{:?}",
                match &domain.actions[action.domain_action_idx] {
                    Action::Basic(ba) => ba.name.1,
                    _ => "",
                },
                action.args.iter().map(|(_, s)| *s).collect::<Vec<&str>>()
            );
        }
        Ok(solution)
    }
}
