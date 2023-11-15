use std::{
    collections::{BinaryHeap, HashMap},
    fmt::Debug,
    hash::Hash,
};

use crate::{
    compiler::{
        action_graph::ActionGraph, CompiledAction, CompiledActionUsize, CompiledProblem, Domain,
        Instruction, IntValue, Problem, Runnable, StateUsize,
    },
    Objects,
};

#[derive(Clone)]
pub struct SolutionNode {
    action_id: Option<CompiledActionUsize>,
    state: Vec<bool>,
    functions: [IntValue; 1],
    cost: IntValue,
    estimate: IntValue,
    visited_neighbor_idx: CompiledActionUsize,
}

impl Ord for SolutionNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let estimate_order = other.estimate.cmp(&self.estimate);
        if estimate_order.is_eq() {
            // TODO: If two estimates after actions are equal,
            // what is the better last action to choose?
            // currently ordering by action_id so it explores first action first.
            // Maybe try depth first?
            let cost_order = other.cost.cmp(&self.cost);
            if cost_order.is_eq() {
                other.action_id.cmp(&self.action_id)
            } else {
                cost_order
            }
        } else {
            estimate_order
        }
    }
}

impl PartialOrd for SolutionNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for SolutionNode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        //Only came_from is using SolutionNode as a key.
        // Hash by state and last performed action.
        self.state.hash(state);
        self.functions.hash(state);
        self.action_id.hash(state);
    }
}

impl PartialEq for SolutionNode {
    fn eq(&self, other: &Self) -> bool {
        self.action_id == other.action_id
            && self.state == other.state
            && self.functions == other.functions
    }
}

impl Eq for SolutionNode {}

impl Debug for SolutionNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SolutionNode")
            .field("action_id", &self.action_id)
            .field("cost", &self.cost)
            .field("estimate", &self.estimate)
            .finish()
    }
}

impl SolutionNode {
    pub fn new(size: StateUsize) -> Self {
        Self {
            action_id: None,
            cost: 0,
            estimate: i64::MAX,
            state: vec![false; size as usize],
            functions: [0],
            visited_neighbor_idx: 0,
        }
    }
}

pub struct AstarInternals<'src> {
    open_set: BinaryHeap<SolutionNode>,
    came_from: HashMap<SolutionNode, SolutionNode>,
    cheapest_path_to_map: HashMap<Vec<bool>, i64>,
    dynamic_action_graph: ActionGraph<'src>,
}
impl<'src> AstarInternals<'src> {
    pub fn new(action_graph: &ActionGraph<'src>) -> Self {
        Self {
            open_set: BinaryHeap::new(),
            came_from: HashMap::new(),
            cheapest_path_to_map: HashMap::new(),
            dynamic_action_graph: action_graph.clone(),
        }
    }
}

pub fn a_star(
    problem: &CompiledProblem,
    domain: Option<&Domain>,
    past: Option<&Problem>,
    args: &mut AstarInternals,
) -> Option<Vec<CompiledActionUsize>> {
    fn _test_action(
        action_idx: CompiledActionUsize,
        action: &CompiledAction,
        current: &SolutionNode,
        goal: &[Instruction],
        args: &mut AstarInternals,
    ) -> Option<SolutionNode> {
        // print!("Checking: {}", action.precondition.disasm());
        if action.precondition.run(&current.state, &current.functions) {
            // println!("Can run!");
            let mut new_node = SolutionNode {
                action_id: Some(action_idx),
                cost: current.cost,
                estimate: current.estimate,
                state: current.state.clone(),
                functions: current.functions.clone(),
                visited_neighbor_idx: 0,
            };
            new_node.functions[0] = new_node.cost;
            action
                .effect
                .run_mut(&mut new_node.state, &mut new_node.functions);
            new_node.cost = new_node.functions[0];
            let wrong_states = goal.state_miss_count(&new_node.state);
            new_node.estimate = new_node.cost + wrong_states;
            if goal.len() > 5 {
                // TODO Generalize problem subdivision
                if let Instruction::ReadState(n) = goal[5] {
                    // println!("Goal: {}", goal.disasm());
                    if new_node.state[n as usize] && wrong_states != 0 {
                        new_node.estimate += wrong_states;
                    }
                }
            }
            if new_node.estimate
                < *args
                    .cheapest_path_to_map
                    .get(&new_node.state)
                    .unwrap_or(&i64::MAX)
            {
                Some(new_node)
            } else {
                // We reached a state we already saw before
                let mut path = Vec::new();
                let mut current = new_node;
                path.push(current.action_id.unwrap());
                while let Some(next) = args.came_from.get(&current) {
                    next.action_id.and_then(|p| Some(path.push(p)));
                    current = next.clone();
                }
                if path.len() >= 2 {
                    path.reverse();
                    println!("Decreasing path priority.");
                    args.dynamic_action_graph.add_low_priority_path(path);
                }
                None
            }
        } else {
            // println!("Cannot run.");
            None
        }
    }
    let mut iterations = 0;
    let mut smallest_missed_problem_states = IntValue::MAX;
    if args.open_set.is_empty() {
        let mut start = SolutionNode::new(problem.memory_size);
        // println!("Init: {}", problem.init.disasm());
        problem.init.run_mut(&mut start.state, &mut start.functions);
        start.estimate = problem.goal.state_miss_count(&start.state);
        smallest_missed_problem_states = start.estimate;
        args.cheapest_path_to_map
            .insert(start.state.clone(), start.estimate);
        args.open_set.push(start.clone());
    }
    let mut largest_cost = 0;
    while let Some(mut current) = args.open_set.pop() {
        if problem.goal.run(&current.state, &current.functions) {
            println!("Solved in {} iterations", iterations);
            let mut path = Vec::new();
            path.push(current.action_id.unwrap());
            while let Some(next) = args.came_from.get(&current) {
                next.action_id.and_then(|p| Some(path.push(p)));
                current = next.clone();
            }
            path.reverse();
            return Some(path);
        }
        if current.estimate - current.cost < smallest_missed_problem_states {
            println!(
                "Achieved required goal state in {} iterations. Node cost:{} estimate: {}",
                iterations, current.cost, current.estimate
            );
            let mut path = vec![current.action_id.unwrap()];
            let mut tmp = current.clone();
            while let Some(next) = args.came_from.get(&tmp) {
                let action_id = tmp.action_id.unwrap();
                path.push(action_id);
                let action_id = action_id as usize;
                let domain_action_id = problem.actions[action_id].domain_action_idx as usize;
                let args = problem.actions[action_id]
                    .args
                    .iter()
                    .map(|(row, col)| past.unwrap().objects.get_object_name(*row, *col).1)
                    .collect::<Vec<_>>();
                print!(
                    "{}({}), ",
                    domain.unwrap().actions[domain_action_id].name(),
                    args.join(",")
                );
                tmp = next.clone();
            }
            path.reverse();
            println!("\nFlushing states.");
            args.open_set.clear();
            args.dynamic_action_graph.add_high_priority_path(
                problem,
                past.unwrap(),
                domain.unwrap(),
                path,
            );
            println!("Increasing path priority.");
            smallest_missed_problem_states = current.estimate - current.cost;
        }

        let max_iterations = if let Some(last) = current.action_id {
            args.dynamic_action_graph.priority[last as usize].len()
        } else {
            problem.actions.len()
        } as CompiledActionUsize;

        let mut upper_bound = current.visited_neighbor_idx
            + (if current.action_id.is_some() {
                3
            } else {
                max_iterations
            });
        if upper_bound > max_iterations {
            upper_bound = max_iterations;
        }

        for neighbor_idx in current.visited_neighbor_idx..upper_bound {
            iterations += 1;
            let i = if current.action_id.is_some() {
                args.dynamic_action_graph.priority[current.action_id.unwrap() as usize]
                    [neighbor_idx as usize]
            } else {
                neighbor_idx as CompiledActionUsize
            };
            let action = &problem.actions[i as usize];
            if let Some(new_node) = _test_action(i, action, &current, &problem.goal, args) {
                if new_node.cost > largest_cost {
                    largest_cost = new_node.cost;
                    println!(
                        "Reached new depth of cost {}, open_set has {} states",
                        largest_cost,
                        args.open_set.len()
                    );
                }
                args.came_from.insert(new_node.clone(), current.clone());
                args.cheapest_path_to_map
                    .insert(new_node.state.clone(), new_node.cost);
                args.open_set.push(new_node);
            }
        }
        current.visited_neighbor_idx = upper_bound;
        if upper_bound != max_iterations {
            args.open_set.push(current)
        } else {
            // println!(
            //     "Finished exploring all neighbors of {:?}",
            //     current.action_id
            // );
        }
    }
    println!("Leaving A* after {} iterations", iterations);
    None
}

#[cfg(test)]
mod test {

    use std::time::SystemTime;

    use crate::{
        compiler::{
            action_graph::ActionGraph, compile_problem, Action, CompiledAction,
            CompiledActionUsize, CompiledProblem, Instruction, Objects, Runnable,
        },
        lib_tests::load_repo_pddl,
        parser::{parse_domain, parse_problem},
        search::{a_star, AstarInternals},
        ReportPrinter,
    };

    #[test]
    fn basic_search() {
        use Instruction::*;
        let p = CompiledProblem {
            memory_size: 1,
            constants_size: 0,
            domain_action_ranges: Vec::new(),
            actions: vec![
                CompiledAction {
                    domain_action_idx: 0,
                    args: vec![(0, 0), (0, 0)],
                    precondition: vec![ReadState(0), Not],
                    effect: vec![And(0), SetState(0)],
                },
                CompiledAction {
                    domain_action_idx: 1,
                    args: vec![(0, 0), (0, 0)],
                    precondition: vec![ReadState(0)],
                    effect: vec![And(0), Not, SetState(0)],
                },
            ],
            init: vec![And(0), Not, SetState(0)],
            goal: vec![ReadState(0)],
            action_graph: ActionGraph {
                priority: vec![vec![], vec![]],
                variable_inertia: Vec::new(),
            },
        };
        let mut args = AstarInternals::new(&p.action_graph);
        assert_eq!(a_star(&p, None, None, &mut args), Some(vec![0]))
    }

    #[test]
    // #[ignore = "Takes too long without optimizations; Reached cost 42 before running out of ram"]
    #[ignore = "Takes too long without optimizations; Reached cost 61 in 10 Minutes and found first drink!"]
    fn barman_pddl_search() -> std::io::Result<()> {
        // was able to figure out how to make one cocktail in ~2 minutes
        // grasp(left,shot5)
        // fill-shot(shot5,ingredient7,left,right,dispenser7),
        // pour-shot-to-clean-shaker(shot5,ingredient7,shaker1,left,l0,l1),
        // clean-shot(shot5,ingredient7,left,right),
        // fill-shot(shot5,ingredient5,left,right,dispenser5),
        // pour-shot-to-used-shaker(shot5,ingredient5,shaker1,left,l1,l2),
        // leave(left,shot5),
        // grasp(left,shaker1),
        // shake(cocktail3,ingredient7,ingredient5,shaker1,left,right),
        // pour-shaker-to-shot(cocktail3,shot1,left,shaker1,l2,l1),
        let solution = full_search(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
        )?;
        assert_eq!(solution, vec![182, 6, 404]);
        Ok(())
    }

    #[test]
    fn simple_pddl_search() -> std::io::Result<()> {
        let solution = full_search(
            "sample_problems/simple_domain.pddl",
            "sample_problems/simple_problem.pddl",
        )?;
        assert_eq!(solution, vec![2, 1, 12]);
        Ok(())
    }

    fn full_search(
        domain_filename: &'static str,
        problem_filename: &'static str,
    ) -> std::io::Result<Vec<CompiledActionUsize>> {
        let start = SystemTime::now();
        let sources = load_repo_pddl(domain_filename, problem_filename);
        let domain = parse_domain(&sources.domain_src).unwrap_or_print_report(&sources);
        let problem = parse_problem(&sources.problem_src, domain.requirements)
            .unwrap_or_print_report(&sources);
        let c_problem = compile_problem(&domain, &problem).unwrap_or_print_report(&sources);
        println!(
            "Compiled problem needs {} bits of memory and uses {} actions.",
            c_problem.memory_size,
            c_problem.actions.len()
        );

        let mut precondition_instructions = 0;
        let mut effect_instructions = 0;
        if c_problem.actions.len() < 100 {
            println!("Action map:");
        }
        for (idx, action) in c_problem.actions.iter().enumerate() {
            precondition_instructions += action.precondition.len();
            effect_instructions += action.effect.len();
            if c_problem.actions.len() < 100 {
                println!(
                    "\t{}: {}({}) if {} effect {}",
                    idx,
                    domain.actions[action.domain_action_idx as usize].name().1,
                    action
                        .args
                        .iter()
                        .map(|(row, col)| problem.objects.get_object_name(*row, *col).1)
                        .collect::<Vec<&str>>()
                        .join(","),
                    action.precondition.disasm(),
                    action.effect.disasm()
                );
            }
        }
        println!(
            "Total precondition instructions: {}",
            precondition_instructions
        );
        println!("Total effect instructions: {}", effect_instructions);
        if c_problem.actions.len() < 100 {
            println!("Action graph:\n{}", c_problem.action_graph);
        }
        let mut args = AstarInternals::new(&c_problem.action_graph);
        let solution = a_star(&c_problem, Some(&domain), Some(&problem), &mut args).unwrap();
        let end = SystemTime::now();
        let duration = end.duration_since(start).unwrap();
        println!("Time taken: {}", duration.as_secs_f32());
        println!("Solution is {} actions long.", solution.len());
        for action_id in &solution {
            let action = c_problem.actions.get(*action_id as usize).unwrap();
            println!(
                "\t{}{:?}",
                match &domain.actions[action.domain_action_idx as usize] {
                    Action::Basic(ba) => ba.name.1,
                    _ => "",
                },
                action
                    .args
                    .iter()
                    .map(|(row, col)| problem.objects.get_object_name(*row, *col).1)
                    .collect::<Vec<&str>>()
            );
        }
        Ok(solution)
    }
}
