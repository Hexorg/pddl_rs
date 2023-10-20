use std::{collections::{BinaryHeap, HashMap}, fs};
pub mod routing;
use crate::compiler::{CompiledProblem, Runnable};

struct SolutionNode {
    action_id: Option<usize>,
    state: Vec<bool>,
}

impl Ord for SolutionNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.action_id.cmp(&self.action_id).then_with(|| other.state.cmp(&self.state))
    }
}

impl PartialOrd for SolutionNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SolutionNode {
    fn eq(&self, other: &Self) -> bool {
        self.action_id == other.action_id && self.state == other.state
    }
}

impl Eq for SolutionNode {}

impl SolutionNode {
    pub fn new(size:usize) -> Self {
        Self{action_id:None, state:vec![false;size]}
    }
}

pub fn a_star<H>(problem:&CompiledProblem, mut h:H)
    where H:FnMut(&[bool]) -> i64 {
    let mut start = SolutionNode::new(problem.memory_size);
    problem.init.run(&mut start.state);
    // The set of discovered nodes that may need to be (re-)expanded.
    // Initially, only the start node is known.
    // This is usually implemented as a min-heap or priority queue
    let mut open_set = BinaryHeap::new();
    open_set.push(start);

    // Cheapest path from start to node n
    let mut came_from = HashMap::new();

    // gScore[n] is the cost of the cheapest path from start to n currently known.
    let mut gScore = HashMap::new(); // default value of Infinity
    gScore.insert(start_state, 0);

    // For node n, fScore[n] := gScore[n] + h(n). fScore[n] represents our current best guess as to
    // how cheap a path could be from start to finish if it goes through n.
    let mut fScore = HashMap::new(); // default value of Infinity
    fScore[&start_state] = h(&start_state[..]);

    while let Some(mut current_state) = open_set.pop() {
        if problem.goal.run(&mut current_state) {
            // We're done
            todo!("A* found path")
        }

        let current_cost = gScore[&current_state];

        // for each applicable action
        for action in problem.actions {
            if action.precondition.run(&mut current_state) {
                let mut new_state = current_state.clone();
                action.effect.run(&mut new_state);
                let tentative_gScore = current_cost + 1;
                if tentative_gScore < gScore[&new_state] {
                    came_from.insert(&new_state, &current_state);
                    gScore.insert(new_state, tentative_gScore);
                    fScore.insert(&new_state, h(&new_state));
                    open_set.push(new_state);
                }
            }
        }

    }
}