use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashSet, HashMap};
use std::fs::File;
use std::io::{Write, Read};
use std::path::{PathBuf, Path};
use std::{fmt::Display, hash::Hash};

use serde::de::Visitor;
use serde::de::value::SeqDeserializer;

use crate::compiler::AtomicFormula;
use crate::search::SolutionNode;

// use super::inertia::DomainInertia;
use super::{CompiledActionUsize};
use super::{CompiledProblem, Domain, PredicateUsize, Problem, Name, CompiledAction};

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



#[derive(Clone)]
struct PriorityVector{
    /// first index is  from compiled action index
    /// second index is to domain action index
    /// value is to compiled action index.
    priority: Vec<Vec<CompiledActionUsize>>,
}

// struct NeighborIterator<'i> {
//     pub iter: std::collections::hash_set::Iter<'i, CompiledActionUsize>,
// }

// impl<'i> Iterator for NeighborIterator<'i> {
//     type Item = CompiledActionUsize;

//     fn next(&mut self) -> Option<Self::Item> {
//         if let Some(i) = self.iter.next() {
//             Some(*i)
//         } else {
//             None
//         }
//     }
// }

/// A graph of actions to be executed in sequence to speed up domain planning.
#[derive(Clone)]
pub struct ActionGraph {
    pub priority: Vec<Vec<Vec<CompiledActionUsize>>>,
    filename:Option<PathBuf>,
    
}

impl serde::Serialize for ActionGraph{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
        use serde::ser::SerializeSeq;
        // let mut s = serializer.serialize_seq(Some(self.priority.len()))?;
        //     for action_priority in &self.priority {
        //         s.serialize_element(action_priority)?;
        //     }
        // s.end()
        todo!()
    }
}

impl<'de> Visitor<'de> for ActionGraph {
    type Value = ActionGraph;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "Action graph file")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: serde::de::SeqAccess<'de>, {
            todo!();
            // let mut priority = Vec::with_capacity(seq.size_hint().unwrap());
            // while let Some(vec) = seq.next_element()? {
            //     priority.push(vec);
            // }
            // Ok(ActionGraph{priority, variable_inertia:self.variable_inertia, filename:self.filename})
    }
}

impl<'de> serde::Deserialize<'de> for ActionGraph {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
        // deserializer.deserialize_seq(Router::new())
        todo!()
    }
}

impl ActionGraph {
    pub fn get_priority(&self, from:Option<CompiledActionUsize>) -> std::slice::Iter<'_, CompiledActionUsize> {
        todo!()
    }
    pub fn apply_inertia(&mut self, problem:&CompiledProblem) {
        for from_domain_action_idx in 0..problem.domain.actions.len() {
            for from_compiled_action_idx in problem.domain_action_ranges[from_domain_action_idx].clone() {
                let from_arity = problem.actions[from_compiled_action_idx as usize].args.len();
                let mut domain_destination = Vec::new();
                for to_domain_action_idx in 0..problem.domain.actions.len() {
                    // let mut low_priority = Vec::new();
                    // let mut unrelated = Vec::new();
                    // let mut bins = vec![Vec::new(); from_arity];
                    let mut destination_vector = Vec::new();
                    for to_compiled_action_idx in problem.domain_action_ranges[to_domain_action_idx].clone() {

                
                        if from_compiled_action_idx != to_compiled_action_idx {
                            let to_arity = problem.actions[to_compiled_action_idx as usize].args.len();
                            // let shared_wants = problem.action_inertia.as_slice().shared_wants(from_compiled_action_idx, to_compiled_action_idx);
                            // let enables = problem.action_inertia.as_slice().enables_positive(from_compiled_action_idx, to_compiled_action_idx) + problem.action_inertia.as_slice().enables_negative(from_compiled_action_idx, to_compiled_action_idx);
                            // let disables = problem.action_inertia.as_slice().disables_positive(from_compiled_action_idx, to_compiled_action_idx) + problem.action_inertia.as_slice().disables_negative(from_compiled_action_idx, to_compiled_action_idx);
                            // // if from_domain_action_idx == 5 && to_domain_action_idx == 2 && enables > 0 {
                            // //     println!("{} to {}: from_arity:{from_arity}, to_arity:{to_arity}, shared_wants:{shared_wants}, enables{enables}, disables{disables}, is_inverse:{}",
                            // //         problem.get_action_string(from_compiled_action_idx),
                            // //         problem.get_action_string(to_compiled_action_idx),
                            // //         inertia.is_inverse(from_compiled_action_idx, to_compiled_action_idx)
                            // //     );
                            // // }
                            // if problem.action_inertia.as_slice().is_inverse(from_compiled_action_idx, to_compiled_action_idx) {
                                
                            // } else {
                            //     if enables > 0 && disables == 0 {
                            //         if enables >= from_arity || enables >= to_arity {
                            //             destination_vector.push(to_compiled_action_idx);
                            //         } else if enables > shared_wants {
                            //             bins[enables-1].push(to_compiled_action_idx);
                            //         } else {
                            //             low_priority.push(to_compiled_action_idx)
                            //         }
                            //     } else if enables > 0 && disables > 0 {
                            //         low_priority.push(to_compiled_action_idx);
                            //     } else if enables == 0 && disables == 0 {
                            //         unrelated.push(to_compiled_action_idx);
                            //     }
                            // }
                        }
                    }
                    // while let Some(bin) = bins.pop() {
                    //     destination_vector.extend(bin);
                    // }
                    // destination_vector.extend(low_priority);
                    domain_destination.push(destination_vector);
                }
                self.priority.push(domain_destination);
            }
        }
        // let mut filename = PathBuf::from(problem.problem.file.parent().unwrap());
        // filename.push(format!("{}.ag", problem.problem.file.file_stem().unwrap().to_str().unwrap()));
        // self.filename = Some(filename);
        // println!("Starting reverse search...");
        // let came_from = inertia.a_star(&problem.problem_inertia);
        // let mut current = 2;
        // println!("Inertia path:");
        // let mut iter = 0;
        // while came_from.contains_key(&current) && iter < 10 {
        //     iter += 1;
        //     print!("{} -> ", problem.actions[current].to_string(problem.domain, problem.problem));
        //     current = *came_from.get(&current).unwrap()
        // }
        // print!("{}", problem.actions[current].to_string(problem.domain, problem.problem));
    }

    pub fn new() -> Self {
        Self{priority:Vec::new(), filename:None}
    }

    pub fn save(&mut self, filename:Option<&Path>) {
        let filename:&Path = if let Some(f) = filename {
            self.filename = Some(f.to_owned());
            f
        } else if let Some(f) = &self.filename {
            f
        } else {
            panic!()
        };
        let content = bincode::serialize(&self.priority).unwrap();
        let mut file = File::create(filename).unwrap();
        file.write_all(&content).unwrap();

    }

    pub fn load(filename:&Path) -> Option<ActionGraph> {
        if let Ok(mut file) = File::open(filename) {
            let mut content = Vec::with_capacity(file.metadata().unwrap().len() as usize);
            file.read_to_end(&mut content).unwrap();
            Some(ActionGraph{priority:bincode::deserialize(&mut content).unwrap(), filename:Some(filename.to_owned())})
        } else {
              None
        }
    }


    // /// Re-initializes the priority matrix to be action-index based. And `size`by`size` long.
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
    // pub fn apply_inertia<'src, O>(&mut self, inertia: &Vec<Inertia<'src, O>>)
    // where
    //     O: Eq + PartialEq + Hash,
    // {
    //     for from in 0..inertia.len() {
    //         self.priority.push(Vec::new());
    //         let mut unrelated_actions = Vec::new();
    //         for to in 0..inertia.len() {
    //             if inertia.is_enables(from, to) && !inertia.is_disables(from, to) {
    //                 self.priority[from].push(to as CompiledActionUsize);
    //             }
    //             if !inertia.is_enables(from, to) && !inertia.is_disables(from, to) {
    //                 unrelated_actions.push(to as CompiledActionUsize);
    //             }
    //         }
    //         self.priority[from].extend(unrelated_actions);
    //     }
    // }

    pub fn apply_dijkstra(&mut self, problem:&CompiledProblem) {
        let mut heap = BinaryHeap::with_capacity(self.priority.len());
        for i in 0..self.priority.len() {
            let vec = self.dijkstra(i as CompiledActionUsize, problem);
            heap.push(ActionVecOrd(vec));
        }
        let mut first_time = true;
        while let Some(sequence) = heap.pop() {
            if first_time {
                first_time = false; 
                // println!("longest shortest path: {}", problem.action_path_to_string(&sequence.0.iter().map(|i| *i as CompiledActionUsize).collect::<Vec<_>>(), ", "));
            }
            for action_idx in 1..sequence.0.len() {
                let from_compiled = action_idx-1;
                let to_domain = problem.actions[action_idx].domain_action_idx as usize;
                let to_compiled = action_idx as CompiledActionUsize;
                let vec = &mut  self.priority[from_compiled][to_domain];
                vec.reverse();
                if let Some(idx) = vec.iter().enumerate().rev().find_map(|(idx, action)| if *action == to_compiled { Some(idx) } else { None }) {
                    let a = vec.remove(idx);
                    vec.push(a);
                }
                vec.reverse();
            }
        }
    }

    pub fn dijkstra(&self, from: CompiledActionUsize, problem:&CompiledProblem) -> Vec<usize> {
        let mut unvisited_set = (0..problem.actions.len())
            .map(|i| i as CompiledActionUsize)
            .collect::<HashSet<CompiledActionUsize>>();
        let mut distances = vec![CompiledActionUsize::MAX; problem.actions.len()];
        let mut path_back = vec![from; problem.actions.len()];
        distances[from as usize] = 0;
        let mut current = from as usize;
        let mut current_cost;
        let mut min_cost;
        let mut longest_path_start = 0;

        while unvisited_set.len() > 0 && unvisited_set.contains(&(current as CompiledActionUsize)) {
            current_cost = distances[current];
            for domain_action_idx in 0..problem.domain.actions.len() {
                for neighbor in &self.priority[current][domain_action_idx] {
                    // TODO: This is all wrong - actions aren't check to be compatible.
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

    // pub fn to_string(&self, problem: &CompiledProblem) -> String {
    //     let mut result = String::new();
    //     for idx in 0..problem.actions.len() {
    //         let path_vector = &self.router[idx].priority;
    //         result.push_str(&format!(
    //             "Action {} (path length: {}):\n{}\n",
    //             problem.get_action_string(idx as CompiledActionUsize),
    //             path_vector.len(),
    //             path_vector.to_string(problem)
    //         ));
    //     }
    //     result
    // }

    pub fn total_links(&self) -> usize {
        self.priority.iter().map(|r| r.iter().map(|v| v.len()).sum::<usize>()).sum()
    }

    pub fn get_inverse(&self, action_idx:CompiledActionUsize, problem: &CompiledProblem) -> Option<CompiledActionUsize> {
        let my_args = &problem.actions[action_idx as usize].args;
        let range = problem.domain_action_ranges[match problem.actions[action_idx as usize].domain_action_idx {
            1 => 0,
            0 => 1,
            _ => return None
        }].clone();
        for dst in range { 
            if my_args.eq(&problem.actions[dst as usize].args) {
                return Some(dst)
            }
        }
        None
    }

    pub fn add_high_priority_path(
        &mut self,
        problem: &CompiledProblem,
        path: &Vec<CompiledActionUsize>,
    ) {
        // todo!()
        // println!("High priority path: {:?}", path);
    }

    pub fn add_low_priority_path(&mut self, path: &Vec<CompiledActionUsize>) {
        // println!("Adding low priority path: {:?}", path);
        // let router = &mut self.router[*path.last().unwrap() as usize];
        // for pos in 1..path.len() {
        //     if router.remove(path[pos]) {
        //         break;
        //     }
        // }
    }

    pub fn add_medium_priority_path(&mut self, path:&Vec<CompiledActionUsize>) {
        // println!("Medium priority path: {:?}", path);

    }

    // pub fn destination_len(&self, path:&Vec<CompiledActionUsize>) -> usize {
    //     self.router[*path.last().unwrap() as usize].destination_len()
    // }

    // pub fn next_hop(&mut self, path:&Vec<CompiledActionUsize>, idx:CompiledActionUsize) -> CompiledActionUsize {
    //     // println!("Getting next hop for {:?}", path);
    //     if path.len() > 1 {
    //         self.add_medium_priority_path(path);
    //     }
    //     self.router[*path.last().unwrap() as usize].next_hop(idx)
    // }

    // pub fn route<'i>(&'i self, node:&SolutionNode) -> std::iter::Cloned<std::collections::hash_set::Iter<'i, u32>> {
    //     if let Some(action_id) = node.action_id {
    //         let priority = &self.router[action_id as usize].priority;
    //         // match node.visited_priority {
    //         //     Priority::None => priority.high_priority.iter().cloned(),
    //         //     Priority::High => priority.medium_priority.iter().cloned(),
    //         //     Priority::Medium => priority.low_priority.iter().cloned(),
    //         //     Priority::Low => priority.unprioritized.iter().cloned(),
    //         //     Priority::Unprioritized => panic!(),
    //         // }
    //     } else {
    //         self.all_actions_set.iter().cloned()

    //     }
    // }

    // /// Given the action pair - modify the priority matrix to get the search algorithm
    // /// to check the `to` action right after `from` action.
    // fn prioritize(&mut self, from: CompiledActionUsize, to: CompiledActionUsize) {
    //     let vec = &mut self.priority[from as usize];
    //     if let Some((idx, _)) = vec.iter().enumerate().find(|(_, dst)| (**dst) == to) {
    //         let id = vec.remove(idx);
    //         vec.insert(0, id);
    //     }
    // }

    // /// Given the action pair - modify the priority matrix to get the search algorithm
    // /// to check the `to` action as the last one after `from` action.
    // fn deprioritize(
    //     &mut self,
    //     from: CompiledActionUsize,
    //     to: CompiledActionUsize,
    // ) -> Option<usize> {
    //     let vec = &mut self.priority[from as usize];
    //     if let Some((idx, _)) = vec.iter().enumerate().find(|(_, dst)| (**dst) == to) {
    //         let id = vec.remove(idx);
    //         vec.push(id);
    //         Some(idx)
    //     } else {
    //         None
    //     }
    // }
}

// impl Display for ActionGraph {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         for i in 0..self.priority.len() {
//             f.write_fmt(format_args!("{}: {:?}\n", i, self.priority[i]))?
//         }
//         Ok(())
//     }
// }

#[cfg(test)]
mod test {
    use crate::{lib_tests::load_repo_pddl, compiler::{passes::Compiler, maps::map_objects}};



    #[test]
    fn experiment() {
        // let sources = load_repo_pddl(
        //     "sample_problems/barman/domain.pddl",
        //     "sample_problems/barman/problem_5_10_7.pddl",
        // );
        let sources = load_repo_pddl(
            "sample_problems/simple_domain.pddl",
            "sample_problems/simple_problem.pddl",
        );
        // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let compiled_problem = sources.compile(&domain, &problem);
        // println!("{}", compiled_problem.action_graph.to_string(&compiled_problem));
        // println!("Problem Inertia:\n{}", compiled_problem.problem_inertia);
    }
}