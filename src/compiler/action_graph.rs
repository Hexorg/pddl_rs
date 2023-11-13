use std::cmp::Ordering;
use std::collections::{HashSet, BinaryHeap};
use std::{fmt::Display, hash::Hash};

use super::{Domain, CompiledAction, AtomicFormula, Term};
use super::inertia::DomainInertia;
use super::{inertia::Inertia, CompiledActionUsize};

// use rand::thread_rng;
// use rand::seq::SliceRandom;

#[derive(PartialEq, Eq)]
struct ActionVecOrd(pub Vec<usize>);

impl Ord for ActionVecOrd {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.len().cmp(&other.0.len()) {
            Ordering::Equal => self.0.cmp(&other.0),
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater
        }
    }
}

impl PartialOrd for ActionVecOrd {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, PartialEq)]
/// A graph of actions to be executed in sequence to speed up domain planning.
pub struct ActionGraph {
    /// The priority matrix of actions - a square matrix where N is the number of actions in domain
    /// (unexpanded to objects in a problem) The offset is the current action index,
    /// which points to a vector of which actions to try first. E.g. priority[4][0] will tell you the most likely action be tried right after
    /// action#4. priority[4][1] will tell you the second most likely action.
    pub priority: Vec<Vec<CompiledActionUsize>>,
}

impl ActionGraph {
    pub fn new() -> Self {
        Self {
            priority: Vec::new(),
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
    pub fn apply_inertia<'src, O>(&mut self, inertia: &Vec<Inertia<O>>)
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
                self.prioritize(action_idx as CompiledActionUsize-1, sequence.0[action_idx] as CompiledActionUsize)
            }
        }
    }

    pub fn dijkstra(&self, from:CompiledActionUsize) -> Vec<usize> {
        let mut unvisited_set = (0..self.priority.len()).map(|i| i as CompiledActionUsize).collect::<HashSet<CompiledActionUsize>>();
        let mut distances = vec![CompiledActionUsize::MAX; self.priority.len()];
        let mut path_back = vec![from; self.priority.len()];
        distances[from as usize] = 0;
        let mut current = from as usize;
        let mut current_cost = 0;
        let mut min_cost = CompiledActionUsize::MAX;
        let mut longest_path_start = 0;

        while unvisited_set.len() > 0 && unvisited_set.contains(&(current as CompiledActionUsize)) {
            current_cost = distances[current];
            for neighbor in &self.priority[current] {
                if current_cost+1 < distances[*neighbor as usize] {
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

        let mut result = Vec::with_capacity(distances[longest_path_start as usize] as usize +1);
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
    fn deprioritize(&mut self, from: CompiledActionUsize, to: CompiledActionUsize) {
        let vec = &mut self.priority[from as usize];
        if let Some((idx, _)) = vec.iter().enumerate().find(|(_, dst)| (**dst) == to) {
            let id = vec.remove(idx);
            vec.push(id)
        }
    }
}

impl Display for ActionGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in 0..self.priority.len() {
            f.write_fmt(format_args!("{}: {:?}\n", i, self.priority[i]))?
        }
        Ok(())
    }
}
