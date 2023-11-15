use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashSet};
use std::{fmt::Display, hash::Hash};

use super::inertia::DomainInertia;
use super::{inertia::Inertia, CompiledActionUsize};
use super::{CompiledProblem, Domain, PredicateUsize, Problem, Term};

// use rand::thread_rng;
// use rand::seq::SliceRandom;

#[derive(PartialEq, Eq)]
struct ActionVecOrd(pub Vec<usize>);

impl Ord for ActionVecOrd {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.len().cmp(&other.0.len()) {
            Ordering::Equal => self.0.cmp(&other.0),
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl PartialOrd for ActionVecOrd {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, PartialEq, Clone)]
/// A graph of actions to be executed in sequence to speed up domain planning.
pub struct ActionGraph<'src> {
    /// The priority matrix of actions - a square matrix where N is the number of actions in domain
    /// (unexpanded to objects in a problem) The offset is the current action index,
    /// which points to a vector of which actions to try first. E.g. priority[4][0] will tell you the most likely action be tried right after
    /// action#4. priority[4][1] will tell you the second most likely action.
    pub priority: Vec<Vec<CompiledActionUsize>>,
    pub variable_inertia: Vec<Inertia<'src, Term<'src>>>,
}

impl<'src> ActionGraph<'src> {
    pub fn new(variable_inertia: Vec<Inertia<'src, Term<'src>>>) -> Self {
        Self {
            priority: Vec::with_capacity(variable_inertia.len()),
            variable_inertia,
        }
    }

    /// Re-initializes the priority matrix to be action-index based. And `size`by`size` long.
    // pub fn set_size(&mut self, size: usize) {
    //     self.priority.clear();
    //     for _ in 0..size {
    //         let inner_vec: Vec<CompiledActionUsize> =
    //             (0..size).map(|u| u as CompiledActionUsize).collect();
    //         // inner_vec.shuffle(&mut thread_rng());
    //         self.priority.push(inner_vec)
    //     }
    // }

    /// Re-arrange action priorities to try actions that are enabled by this action first
    /// And actions that are disabled by this action - last
    pub fn apply_inertia<O>(&mut self, inertia: &Vec<Inertia<'src, O>>)
    where
        O: Eq + PartialEq + Hash,
    {
        for from in 0..inertia.len() {
            self.priority.push(Vec::new());
            let mut unrelated_actions = Vec::new();
            for to in 0..inertia.len() {
                if inertia.is_enables(from, to) && !inertia.is_disables(from, to) {
                    self.priority[from].push(to as CompiledActionUsize);
                }
                if !inertia.is_enables(from, to) && !inertia.is_disables(from, to) {
                    unrelated_actions.push(to as CompiledActionUsize);
                }
            }
            self.priority[from].extend(unrelated_actions);
        }
    }

    pub fn apply_dijkstra(&mut self) {
        let mut heap = BinaryHeap::with_capacity(self.priority.len());
        for i in 0..self.priority.len() {
            let vec = self.dijkstra(i as CompiledActionUsize);
            heap.push(ActionVecOrd(vec));
        }
        while let Some(sequence) = heap.pop() {
            for action_idx in 1..sequence.0.len() {
                self.prioritize(
                    action_idx as CompiledActionUsize - 1,
                    sequence.0[action_idx] as CompiledActionUsize,
                )
            }
        }
    }

    pub fn dijkstra(&self, from: CompiledActionUsize) -> Vec<usize> {
        let mut unvisited_set = (0..self.priority.len())
            .map(|i| i as CompiledActionUsize)
            .collect::<HashSet<CompiledActionUsize>>();
        let mut distances = vec![CompiledActionUsize::MAX; self.priority.len()];
        let mut path_back = vec![from; self.priority.len()];
        distances[from as usize] = 0;
        let mut current = from as usize;
        let mut current_cost;
        let mut min_cost;
        let mut longest_path_start = 0;

        while unvisited_set.len() > 0 && unvisited_set.contains(&(current as CompiledActionUsize)) {
            current_cost = distances[current];
            for neighbor in &self.priority[current] {
                if current_cost + 1 < distances[*neighbor as usize] {
                    distances[*neighbor as usize] = current_cost + 1;
                    path_back[*neighbor as usize] = current as CompiledActionUsize;
                    longest_path_start = *neighbor as CompiledActionUsize;
                }
            }
            unvisited_set.remove(&(current as CompiledActionUsize));

            min_cost = CompiledActionUsize::MAX;
            for node in &unvisited_set {
                let node = *node as usize;
                if distances[node] < min_cost {
                    min_cost = distances[node];
                    current = node;
                }
            }
        }

        let mut result = Vec::with_capacity(distances[longest_path_start as usize] as usize + 1);
        current = longest_path_start as usize;
        while current != from as usize {
            result.push(current);
            // print!("{}, ", current);
            current = path_back[current] as usize;
        }
        result.push(current);
        result.reverse();
        result
    }

    pub fn to_string(&self, domain: &Domain, problem: Option<&CompiledProblem>) -> String {
        let mut result = String::new();
        fn _get_name<'src>(
            priority_len: usize,
            idx: usize,
            domain: &Domain<'src>,
            problem: Option<&CompiledProblem>,
        ) -> &'src str {
            if priority_len > domain.actions.len() {
                if priority_len != problem.unwrap().actions.len() {
                    panic!()
                } else {
                    domain.actions[problem.unwrap().actions[idx].domain_action_idx as usize]
                        .name()
                        .1
                }
            } else {
                domain.actions[idx].name().1
            }
        }
        let plen = self.priority.len();
        for idx in 0..plen {
            result.push_str(&format!(
                "Action {} (path length: {}): {}\n",
                _get_name(plen, idx, domain, problem),
                self.priority[idx].len(),
                self.priority[idx]
                    .iter()
                    .map(|i| _get_name(plen, *i as usize, domain, problem))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        result.pop();
        result
    }

    pub fn add_high_priority_path(
        &mut self,
        problem: &CompiledProblem,
        past: &Problem,
        domain: &Domain,
        path: Vec<CompiledActionUsize>,
    ) {
        // this path is easy. The hard part is to figure out all action-objects
        // that follow this pattern
        let mut count = 0;
        for idx in 0..(path.len() - 1) {
            let from_compiled_action_idx = path[idx];
            let to_compiled_action_idx = path[idx + 1];
            println!(
                "Prioritizing from {} to {}",
                from_compiled_action_idx, to_compiled_action_idx
            );
            self.prioritize(from_compiled_action_idx, to_compiled_action_idx);
            count += 1;
            let from_domain_action_idx =
                problem.actions[from_compiled_action_idx as usize].domain_action_idx as usize;
            let to_domain_action_idx =
                problem.actions[to_compiled_action_idx as usize].domain_action_idx as usize;
            let from_args: HashSet<(PredicateUsize, PredicateUsize)> = problem.actions
                [from_compiled_action_idx as usize]
                .args
                .iter()
                .cloned()
                .collect();
            let to_args: HashSet<(PredicateUsize, PredicateUsize)> = problem.actions
                [to_compiled_action_idx as usize]
                .args
                .iter()
                .cloned()
                .collect();
            let mutual_arg_count = from_args.intersection(&to_args).count();
            for different_args_from_compiled_action_idx in
                problem.domain_action_ranges[from_domain_action_idx].clone()
            {
                if different_args_from_compiled_action_idx != from_compiled_action_idx {
                    // different_args_from_compiled_action_idx is index of all actions like path[idx], but with different args.
                    let from_args: HashSet<(PredicateUsize, PredicateUsize)> = problem.actions
                        [different_args_from_compiled_action_idx as usize]
                        .args
                        .iter()
                        .cloned()
                        .collect();
                    for different_args_to_compiled_action_idx in
                        problem.domain_action_ranges[to_domain_action_idx].clone()
                    {
                        if different_args_to_compiled_action_idx != to_compiled_action_idx {
                            let to_args: HashSet<(PredicateUsize, PredicateUsize)> =
                                problem.actions[different_args_to_compiled_action_idx as usize]
                                    .args
                                    .iter()
                                    .cloned()
                                    .collect();
                            if from_args.intersection(&to_args).count() == mutual_arg_count {
                                let from_name = domain.actions[problem.actions
                                    [different_args_from_compiled_action_idx as usize]
                                    .domain_action_idx
                                    as usize]
                                    .name();
                                let from_args = problem.actions
                                    [different_args_from_compiled_action_idx as usize]
                                    .args
                                    .iter()
                                    .map(|(row, col)| {
                                        crate::Objects::get_object_name(&past.objects, *row, *col).1
                                    })
                                    .collect::<Vec<_>>();
                                let to_name = domain.actions[problem.actions
                                    [different_args_to_compiled_action_idx as usize]
                                    .domain_action_idx
                                    as usize]
                                    .name();
                                let to_args = problem.actions
                                    [different_args_to_compiled_action_idx as usize]
                                    .args
                                    .iter()
                                    .map(|(row, col)| {
                                        crate::Objects::get_object_name(&past.objects, *row, *col).1
                                    })
                                    .collect::<Vec<_>>();
                                println!(
                                    "Prioritizing {}({}) to {}({})",
                                    from_name,
                                    from_args.join(", "),
                                    to_name,
                                    to_args.join(", ")
                                );
                                self.prioritize(
                                    different_args_from_compiled_action_idx,
                                    different_args_to_compiled_action_idx,
                                );
                                count += 1;
                                // if count == 3 { panic!() }
                            }
                        }
                    }
                }
            }
        }
        println!("Prioritized {} actions.", count)
    }

    pub fn add_low_priority_path(&mut self, path: Vec<CompiledActionUsize>) {
        let half_actions = self.priority.len() / 2;
        for idx in (path.len() - 1)..1 {
            let from = path[idx - 1];
            let to = path[idx];
            if let Some(idx) = self.deprioritize(from, to) {
                if idx < half_actions {
                    // move all nodes in the path to low priority
                    // until we find a node that wasn't. Because we don't know
                    // which node in the path cause "bad" path.
                    break;
                }
            }
        }
    }

    /// Given the action pair - modify the priority matrix to get the search algorithm
    /// to check the `to` action right after `from` action.
    fn prioritize(&mut self, from: CompiledActionUsize, to: CompiledActionUsize) {
        let vec = &mut self.priority[from as usize];
        if let Some((idx, _)) = vec.iter().enumerate().find(|(_, dst)| (**dst) == to) {
            let id = vec.remove(idx);
            vec.insert(0, id);
        }
    }

    /// Given the action pair - modify the priority matrix to get the search algorithm
    /// to check the `to` action as the last one after `from` action.
    fn deprioritize(
        &mut self,
        from: CompiledActionUsize,
        to: CompiledActionUsize,
    ) -> Option<usize> {
        let vec = &mut self.priority[from as usize];
        if let Some((idx, _)) = vec.iter().enumerate().find(|(_, dst)| (**dst) == to) {
            let id = vec.remove(idx);
            vec.push(id);
            Some(idx)
        } else {
            None
        }
    }
}

impl<'src> Display for ActionGraph<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in 0..self.priority.len() {
            f.write_fmt(format_args!("{}: {:?}\n", i, self.priority[i]))?
        }
        Ok(())
    }
}
