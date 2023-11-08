use std::{fmt::Display, hash::Hash};

use super::inertia::DomainInertia;
use super::{inertia::Inertia, CompiledActionUsize};

// use rand::thread_rng;
// use rand::seq::SliceRandom;

#[derive(Debug, PartialEq)]
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

    pub fn set_size(&mut self, size: usize) {
        for _ in 0..size {
            let inner_vec: Vec<CompiledActionUsize> =
                (0..size).map(|u| u as CompiledActionUsize).collect();
            // inner_vec.shuffle(&mut thread_rng());
            self.priority.push(inner_vec)
        }
    }

    pub fn apply_inertia<'src, O>(&mut self, inertia: &Vec<Inertia<O>>)
    where
        O: Eq + PartialEq + Hash,
    {
        for from in 0..inertia.len() {
            for to in 0..inertia.len() {
                // if action_idx != next_action_idx {
                if inertia.is_enables(from, to) && !inertia.is_disables(from, to) {
                    self.prioritize(from as CompiledActionUsize, to as CompiledActionUsize)
                } else if inertia.is_disables(from, to) && !inertia.is_enables(from, to) {
                    self.deprioritize(from as CompiledActionUsize, to as CompiledActionUsize)
                }
                // }
            }
        }
    }

    fn prioritize(&mut self, from: CompiledActionUsize, to: CompiledActionUsize) {
        let vec = &mut self.priority[from as usize];
        if let Some((idx, _)) = vec.iter().enumerate().find(|(_, dst)| (**dst) == to) {
            let id = vec.remove(idx);
            vec.insert(0, id);
        }
    }

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
