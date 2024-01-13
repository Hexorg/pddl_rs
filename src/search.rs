
use std::{
    collections::{BinaryHeap, HashMap},
    fmt::Debug,
    hash::Hash, fs::File, io::Write, time::SystemTime, default,
};

use rustworkx_core::petgraph::{Graph, visit::GetAdjacencyMatrix, dot::Config};

use crate::{
    compiler::{
        action_graph::{ActionGraph, self}, CompiledAction, CompiledActionUsize, CompiledProblem,
        // inertia::DomainInertia,
        Instruction, IntValue, Runnable, StateUsize,
    },
};

pub trait AStarNode<S> {
    type PathType: Copy+Debug;
    type CostType: Into<i64> + PartialOrd + Copy;

    fn node_state(&self) -> &S;
    fn state_size(&self) -> usize;
    fn path_id(&self) -> Option<Self::PathType>;
    fn estimate(&self) -> Self::CostType;
    fn cost(&self) -> Self::CostType;
}
pub trait ASTarProblem<N, S, A> where N:AStarNode<S> {
    fn first_node(&self) -> N;
    fn action_neighbors(&self, from:Option<N::PathType>) -> std::slice::Iter<'_, N::PathType>;
    fn new_node_if_possible(&self, action_idx:N::PathType, from:&N, args:&mut A) -> Option<N>;
    fn is_meets_goal(&self, node:&N, args:&mut A) -> bool;
}

#[derive(Clone)]
pub struct SolutionNode {
    pub action_id: Option<CompiledActionUsize>,
    state: Vec<bool>,
    functions: [IntValue; 1],
    cost: IntValue,
    estimate: IntValue,
}

impl AStarNode<Vec<bool>> for SolutionNode {
    type PathType = CompiledActionUsize;

    type CostType = i64;

    fn node_state(&self) -> &Vec<bool> {
        &self.state
    }

    fn state_size(&self) -> usize {
        std::mem::size_of::<bool>()*self.state.len()+std::mem::size_of::<SolutionNode>()
    }

    fn path_id(&self) -> Option<Self::PathType> {
        self.action_id
    }

    fn estimate(&self) -> Self::CostType {
        self.estimate
    }

    fn cost(&self) -> Self::CostType {
        self.cost
    }
}

impl<'ast, 'src> ASTarProblem<SolutionNode, Vec<bool>, ExecStacks> for CompiledProblem<'ast, 'src> {
    // fn action_count(&self) -> usize {
    //     self.actions.len()
    // }

    fn new_node_if_possible(&self, action_idx:CompiledActionUsize, from:&SolutionNode, args:&mut ExecStacks) -> Option<SolutionNode> {
        let action = &self.actions[action_idx as usize];
        if action.precondition.run(&from.state, &from.functions, &mut args.state, &mut args.function) {
            let mut new_node = SolutionNode {
                action_id: Some(action_idx as CompiledActionUsize),
                cost: from.cost,
                estimate: from.estimate,
                state: from.state.clone(),
                functions: from.functions.clone(),
            };
            new_node.functions[0] = new_node.cost;
            action
                .effect
                .run_mut(&mut new_node.state, &mut new_node.functions, &mut args.state, &mut args.function);
            new_node.cost = new_node.functions[0];
            Some(new_node)
        } else {
            None
        }
    }

    fn is_meets_goal(&self, node:&SolutionNode, stack: &mut ExecStacks) -> bool {
        self.goal.run(&node.state, &node.functions, &mut stack.state, &mut stack.function)
    }

    fn first_node(&self) -> SolutionNode {
            let mut start = SolutionNode::new(self.memory_size);
            let mut stacks = ExecStacks::default();
            self.init.run_mut(&mut start.state, &mut start.functions, &mut stacks.state, &mut stacks.function);
            start.estimate = self.goal.state_miss_count(&start.state, &mut stacks.state);
            start
    }

    fn action_neighbors(&self, from:Option<CompiledActionUsize>) -> std::slice::Iter<'_, CompiledActionUsize> {
        self.action_graph.get_priority(from)
    }
}

#[derive(Default)]
struct ExecStacks {
    state: Vec<bool>,
    function: Vec<IntValue>
}


impl Ord for SolutionNode {
    // #[inline]
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
    // #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        //Only came_from is using SolutionNode as a key.
        // Hash by state and last performed action.
        self.state.hash(state);
        self.functions.hash(state);
        self.action_id.hash(state);
    }
}

impl PartialEq for SolutionNode {
    // #[inline]
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
            // visited_priority: Priority::None,
            // has_spawned_states: false,
            // spawned_children: Vec::new()
        }
    }
}

struct Statistics {
    iterations:usize,
    explored_states: usize,
    action_graph_links: usize,
    largest_cost:i64,
    smallest_cost:i64,
    start_time: SystemTime,
    last_statistics_print_time: SystemTime,
    longest_path: Vec<CompiledActionUsize>,
    detected_inverses:usize,
    detected_alternative_branches:usize,
}

impl Statistics {
    pub fn new() -> Self {
        Self {  
            iterations: 0,
            largest_cost: 0,
            smallest_cost: i64::MAX,
            explored_states: 0,
            action_graph_links: 0,
            start_time: SystemTime::now(),
            last_statistics_print_time: SystemTime::now(),
            longest_path: Vec::new(),
            detected_inverses: 0,
            detected_alternative_branches: 0,
        }
    }
}



pub struct AstarInternals<S, N> where N: AStarNode<S>{
    open_set: BinaryHeap<N>,
    came_from: HashMap<N, N>,
    cheapest_path_to_map: HashMap<S, N::CostType>,
    path_buf: Vec<N::PathType>,
    multipaths: Vec<Vec<N::PathType>>,
    stats: Statistics,
    log_file: File,
}
impl<S, N> AstarInternals<S, N> where N: AStarNode<S> + Ord + Hash{
    pub fn new() -> Self {
        Self {
            open_set: BinaryHeap::new(),
            came_from: HashMap::new(),
            cheapest_path_to_map: HashMap::new(),
            stats: Statistics::new(),
            path_buf: Vec::with_capacity(128),
            multipaths: Vec::new(),
            log_file: File::create("solver.log").unwrap(),
        }
    }

    pub fn all_discovered_paths(&self) -> &[Vec<N::PathType>] {
        self.multipaths.as_slice()
    }

    pub fn print_statistics(&self) {
        let end = SystemTime::now();
        let duration = end.duration_since(self.stats.start_time).unwrap().as_secs_f32();
        println!("***** STATISTICS ******");
        println!("Duration: {}s.", duration);
        println!("Total iterations: {}", self.stats.iterations);
        println!("Total states: {}", self.stats.explored_states);
        println!("TotaL links: {}", self.stats.action_graph_links);
        println!("Iterations per second: {}", self.stats.iterations as f32 / duration);
        println!("States per second: {}", self.stats.explored_states as f32 / duration);
        println!("Largest cost: {}", self.stats.largest_cost);
        println!("Smallest cost: {}", self.stats.smallest_cost);
        println!("Detected:");
        println!("\tInverses: {}", self.stats.detected_inverses);
        println!("\tAlternative paths: {}", self.stats.detected_alternative_branches);
        let state_size = if let Some(n) = self.open_set.peek() {
            n.state_size()
        } else {
            0
        };
        println!("open_set contains: {} states ({} MB).", self.open_set.len(), (self.open_set.len()*(std::mem::size_of::<N>()+state_size)) as f64 /1e6)
    }
    pub fn build_path<'a>(&'a mut self, mut node: &'a N) -> &[N::PathType] {
        if let Some(id) = node.path_id() {
            self.path_buf.push(id);
        }
        while let Some(next) = self.came_from.get(node) {
            if let Some(id) = next.path_id() {
                self.path_buf.push(id);
            } else {
                break;
            }
            node = next;
        }
        self.path_buf.reverse();
        self.path_buf.as_slice()
    }
}

/// Generic problem solving A*.
/// P - Problem type
/// N - Node type
/// S - State type
/// A - Additional data that may be needed by ASTarProblem. Generally it's just an optimization to not create and destroy a ton of tiny Vec's
pub fn a_star<'p, P, N, S, A>(problem:&'p P, is_search_all:bool, args: &mut AstarInternals<S, N>) -> Vec<N::PathType> 
where 
    A: Default,
    P: ASTarProblem<N, S, A>,
    N: AStarNode<S> + Ord + PartialOrd + Hash + Clone,
    S: PartialEq + Eq + Hash + Clone
{
    println!("Starting A*");
    let start = problem.first_node();
    args.cheapest_path_to_map
    .insert(start.node_state().clone(), start.estimate());
    args.open_set.push(start);
    let mut stacks = Default::default();


    while let Some(mut current) = args.open_set.pop() {
        if problem.is_meets_goal(&current, &mut stacks) {
            // println!("Found solution");
            if is_search_all {
                let path = args.build_path(&current).to_owned();
                args.multipaths.push(path);
                args.path_buf.clear();
                continue;
            } else {
                return args.build_path(&current).to_owned()
            }
        }

        let now = SystemTime::now();
        args.stats.smallest_cost = current.cost().into();
        if now.duration_since(args.stats.last_statistics_print_time).unwrap().as_secs() > 10 {
            args.stats.last_statistics_print_time = now;
            args.print_statistics();
        }

        for try_action_idx in problem.action_neighbors(current.path_id()) {
            args.stats.iterations += 1;
            if let Some(new_node) = problem.new_node_if_possible(*try_action_idx, &current, &mut stacks) {
                args.stats.explored_states += 1;
                if args.cheapest_path_to_map.contains_key(new_node.node_state()) {
                    // println!("Adding {:?} after {:?} to open set because it gets us to a cheaper cost", new_node.path_id(), current.path_id());
                    // print!("SEARCH: I have already seen this state. ");
                    let cost_to_state = args.cheapest_path_to_map.get_mut(new_node.node_state()).unwrap();
                    if *cost_to_state > new_node.cost() {
                        // println!("This path is cheaper.");
                        *cost_to_state = new_node.cost();
                        args.came_from.insert(new_node.clone(), current.clone());
                        args.open_set.push(new_node);
                        if (*cost_to_state).into() > args.stats.largest_cost {
                            args.stats.largest_cost = (*cost_to_state).into();
                        }
                    } else {
                        // println!("This path is useless.");
                    }
                } else {
                    // println!("Adding {:?} after {:?} to open set because it gets us to a new state", new_node.path_id(), current.path_id());
                    if new_node.cost().into() > args.stats.largest_cost {
                        args.stats.largest_cost = new_node.cost().into();
                    }
                    args.came_from.insert(new_node.clone(), current.clone());
                    args.cheapest_path_to_map
                        .insert(new_node.node_state().clone(), new_node.cost());
                    args.open_set.push(new_node);

                }
            }
        }
    }
    println!("A* explored the whole graph.");
    Vec::new()
}

#[cfg(test)]
mod test {

    use std::time::SystemTime;

    use crate::{
        compiler::{
            action_graph::ActionGraph, compile_problem, CompiledAction,
            CompiledActionUsize, CompiledProblem, Instruction, Runnable,
        },
        lib_tests::load_repo_pddl,
        parser::{parse_domain, parse_problem},
        search::{a_star, AstarInternals},
        ReportPrinter,
    };



    #[test]
    // #[ignore = "Takes too long without optimizations; Reached cost 42 before running out of ram"]
    // #[ignore = "Takes too long without optimizations; Reached cost 61 in 10 Minutes and found first drink!"]
    fn barman_pddl_search() -> std::io::Result<()> {
        // was able to figure out how to make one cocktail in ~2 minutes 0, 2, 6, 5, 2, 7, 1, 0, 10, 11
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
        // without action graph:
        //         ***** STATISTICS ******
        // Duration: 268.95462s.
        // Total iteartions: 6327770378
        // Total states: 3478371
        // Iterations per second: 23527280
        // States per second: 12932.929
        // Largest cost: 37
        // Smallest cost: 27
        // Detected:
        //         Inverses: 4660173
        //         Alternative paths: 8563632
        // with action graph:
        //         ***** STATISTICS ******
        // Duration: 30.415234s.
        // Total iterations: 263518275
        // Total states: 1474622
        // Iterations per second: 8664023
        // States per second: 48483.008
        // Largest cost: 37
        // Smallest cost: 27
        // Detected:
        //         Inverses: 0
        //         Alternative paths: 622116
        // open_set contains: 1052951 states (366.426948 MB).
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
        let (domain, problem) = sources.parse();
        let c_problem = sources.compile(&domain, &problem);
        println!(
            "Compiled problem needs {} bits of memory and uses {} actions with {} links",
            c_problem.memory_size,
            c_problem.actions.len(),
            c_problem.action_graph.total_links()
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
                        .map(|object_idx| c_problem.maps.id_object_map[*object_idx as usize].1)
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
        // if c_problem.actions.len() < 100 {
        //     println!("Action graph:\n{}", c_problem.action_graph);
        // }
        let mut args = AstarInternals::new();
        let solution = a_star(&c_problem, false, &mut args);
        println!("A* complete.");
        args.print_statistics();
        let end = SystemTime::now();
        let duration = end.duration_since(start).unwrap();
        println!("Time taken: {}", duration.as_secs_f32());
        println!("Solution is {} actions long.", solution.len());
        for action_idx in &solution {
            println!("\t{}", c_problem.get_action_string(*action_idx));
        }
        Ok(solution)
    }
}
