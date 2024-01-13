
use std::{hash::Hash, collections::{BinaryHeap, HashMap, HashSet}, marker::PhantomData};
use crate::{compiler::CompiledActionUsize, search::{AStarNode, ASTarProblem, a_star, AstarInternals}, Problem, parser::ast::list::TypedList};

use super::{inertia::{Inertia, Relationship::*, ActionInertia, ExpressionInertia}, CompiledProblem, Name, domain::{CompiledAtomicFormula, ArgKind}, IntValue, ASTActionUsize, Domain, PredicateUsize, action_graph, maps::Maps};

// pub struct NGram (HashMap<usize, usize>);


fn accept(maps:&Maps, state:&mut Vec<CompiledAtomicFormula>, f:&CompiledAtomicFormula, parameters:Option<&TypedList>) -> Option<usize> {
    if let Some(parameters) = parameters {
        let args = f.args.iter().map(|a| parameters.get_type(*a as usize).to_id(maps)).collect::<Vec<_>>();
        let f = CompiledAtomicFormula{predicate_idx:f.predicate_idx, args};
        state.binary_search(&f).ok()
    } else {
        state.binary_search(f).ok()
    }
}

struct InertiaProblem<'inertia, 'ast, 'src> where 'inertia:'ast {
    to_task: usize,
    domain: &'ast Domain<'src>,
    maps: &'ast Maps<'src>,
    problem_init: State,
    inertia: &'inertia Inertia,
    action_graph: Vec<Vec<ASTActionUsize>>,
    try_all_actions: Vec<ASTActionUsize>,
    constant_predicate_ids: HashSet<PredicateUsize>,
}

impl<'inertia, 'ast, 'src> InertiaProblem<'inertia, 'ast, 'src> where 'inertia:'src {
    pub fn new(to_task:usize, domain:&'ast Domain<'src>, problem:&Problem, inertia:&'inertia Inertia, maps:&'ast Maps<'src>, constant_predicate_ids:HashSet<PredicateUsize>) -> Self {
        let mut action_graph = vec![Vec::new(); domain.actions.len()];
        for to in 0..domain.actions.len() {
            let mut unrelated = Vec::new();
            for from in 0..domain.actions.len() {
                match inertia.cmp(from, to, maps) {
                    Enables => action_graph[to].push(from as ASTActionUsize),
                    Unrelated => unrelated.push(from as ASTActionUsize),
                    Disables => (),
                }
            }
            action_graph[to].extend(unrelated);
        }
        let try_all_actions = (0..domain.actions.len() as ASTActionUsize).collect::<Vec<ASTActionUsize>>();
        
        Self { to_task, domain, inertia, maps, action_graph, try_all_actions, problem_init:(&inertia.problem_init).into(), constant_predicate_ids}
    }


    pub fn remove_states(&self, state:&mut Vec<CompiledAtomicFormula>, inverse_state: &mut Vec<CompiledAtomicFormula>, mutator: &[CompiledAtomicFormula], parameters:Option<&TypedList>, is_filter_problem_constants:bool) -> Result<usize, ()> {
        // let state_string = state.iter().map(|p| p.decompile(self.maps)).collect::<Vec<_>>().join(" & ");
        // println!("\t{}", if state_string.len() > 0 { state_string.as_str() } else { "[]" });
        let mut count = 0;
        for p in mutator {
            if is_filter_problem_constants {
                if self.constant_predicate_ids.contains(&p.predicate_idx) {
                    continue;
                }
                // println!("\t\tPredicate {} is problem-constant.", self.maps.id_predicate_map[p.predicate_idx as usize])
            }
            if accept(self.maps, inverse_state, p, parameters).is_some() {
                return Err(())
            }
            if let Some(idx) = accept(self.maps, state, p, parameters) {
                state.remove(idx);
                count += 1;
            }
        }
        Ok(count)
    }

    pub fn add_states(&self, state:&mut Vec<CompiledAtomicFormula>, mutator: &[CompiledAtomicFormula], parameters:&TypedList) {
        for p in mutator {
            let args = p.args.iter().map(|a| parameters.get_type(*a as usize).to_id(self.maps)).collect::<Vec<_>>();
            let f = CompiledAtomicFormula{predicate_idx:p.predicate_idx, args}; 
            match state.binary_search(&f) {
                Ok(_) => (),
                // Err(idx) => {println!("\t\tAdding {}", p.decompile(self.maps)); state.insert(idx, p.clone()); }
                Err(idx) => { state.insert(idx, f); }
            }
            // if state.negative.binary_search(p).is_ok() { panic!(); }
        }
    }

    /// Applies action's wants and provides to current state. 
    /// Panics if action is not compatible
    pub fn apply_action(&self, state:&State, mutator_action:ASTActionUsize) -> Result<State, ()> {
        let mut result = state.clone();
        let wants = &self.inertia.actions[mutator_action as usize].precondition;
        let provides = &self.inertia.actions[mutator_action as usize].effect;
        let parameters = match &self.domain.actions[mutator_action as usize] {
            crate::parser::ast::Action::Basic(ba) => Some(&ba.parameters),
            crate::parser::ast::Action::Durative(_) => todo!(),
            crate::parser::ast::Action::Derived(_, _) => todo!(),
        };
        // println!("\tRemoving provides from positive state:");
        self.remove_states(&mut result.positive, &mut result.negative, &provides.positive, parameters, false)?;
        // println!("\tRemoving provides from negative state:");
        self.remove_states(&mut result.negative, &mut result.positive, &provides.negative, parameters, false)?;
        // println!("\tAdding wants to positive state:");
        self.add_states(&mut result.positive, &wants.positive, parameters.unwrap());
        // println!("\tAdding wants to negative state:");
        self.add_states(&mut result.negative, &wants.negative, parameters.unwrap());
        // println!("\tRemoving problem constants from positive state:");
        self.remove_states(&mut result.positive, &mut result.negative, &self.inertia.problem_init.positive, None, true)?;
        // println!("\tRemoving problem constants from negative state:");
        self.remove_states(&mut result.negative, &mut result.positive, &self.inertia.problem_goal.negative, None, true)?;
        Ok(result)
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
struct State {
    positive: Vec<CompiledAtomicFormula>,
    negative: Vec<CompiledAtomicFormula>,
}

impl State {
    pub fn new() -> Self {
        Self { positive: Vec::new(), negative: Vec::new() }
    }
    pub fn len(&self) -> usize {
        self.positive.len() + self.negative.len()
    }

    pub fn decompile(&self, maps:&Maps) -> String {
        let positive = self.positive.iter().map(|p| p.decompile(maps, None, ArgKind::Type)).collect::<Vec<_>>().join(" & ");
        let negative = self.negative.iter().map(|p| format!("!{}", p.decompile(maps, None, ArgKind::Type))).collect::<Vec<_>>().join(" & ");
        if negative.len() == 0 {
            positive
        } else if positive.len() == 0 {
            negative
        } else {
            format!("{} & {}", positive, negative)
        }
    }
}

impl From<&ExpressionInertia> for State {
    fn from(value: &ExpressionInertia) -> Self {
        let positive = value.positive.clone();
        let negative = value.negative.clone();
        Self { positive, negative }
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
struct SolutionNode {
    cost: i64,
    action: ASTActionUsize,
    original_predicates: State,
    state: State
}

impl<'inertia, 'ast, 'src> ASTarProblem<SolutionNode, State, PhantomData<bool>> for InertiaProblem<'inertia, 'ast, 'src> {
    fn first_node(&self) -> SolutionNode {
        let mut original_predicates: State = (&self.inertia.actions[self.to_task].precondition).into();
        // println!("\tRemoving problem-constants from original positive state:");
        debug_assert!(self.remove_states(&mut original_predicates.positive, &mut original_predicates.negative, &self.inertia.problem_init.positive, None, true).is_ok());
        // println!("\tRemoving problem-constants from original negative state:");
        debug_assert!(self.remove_states(&mut original_predicates.negative, &mut original_predicates.positive, &self.inertia.problem_init.negative, None, true).is_ok());
        let state = original_predicates.clone();
        // println!("Initial state: {}", state.decompile(self.maps));
        SolutionNode { cost: 0, action: self.to_task as ASTActionUsize, state, original_predicates}
    }

    fn new_node_if_possible(&self, action_idx:ASTActionUsize, from:&SolutionNode, _:&mut PhantomData<bool>) -> Option<SolutionNode> {
        match self.inertia.cmp(action_idx as usize, from.action as usize, self.maps) {
            Enables => (),
            Unrelated => (),
            Disables => panic!(),
        }
        if action_idx == self.to_task as ASTActionUsize {
            return None
        }
        // println!("Running from {} to {}\n\tTo state {}\n\tOriginal states to: {}", 
        //     self.domain.get_action_name(action_idx as usize), 
        //     self.domain.get_action_name(from.action as usize), 
        //     from.state.decompile(&self.maps), 
        //     from.original_predicates.decompile(&self.maps), 
        // );
        
        if let Ok(state) = self.apply_action(&from.state, action_idx) {
            let parameters = match &self.domain.actions[action_idx as usize] {
                crate::parser::ast::Action::Basic(ba) => Some(&ba.parameters),
                crate::parser::ast::Action::Durative(_) => todo!(),
                crate::parser::ast::Action::Derived(_, _) => todo!(),
            };
            let mut original_predicates = from.original_predicates.clone();
            // println!("Action is possible. Removing same provides from the original positive state:");
            let mut count = match self.remove_states(&mut original_predicates.positive, &mut original_predicates.negative, &self.inertia.actions[action_idx as usize].effect.positive, parameters, false) {
                Ok(c) => c,
                // Err(_) => {println!("Action impossible"); return None },
                Err(_) => return None,
            };
            // println!("Action is possible. Removing same provides from the original negative state:");
            count += match self.remove_states(&mut original_predicates.negative, &mut original_predicates.positive, &self.inertia.actions[action_idx as usize].effect.negative, parameters, false) {
                Ok(c) => c,
                // Err(()) => {println!("Action impossible"); return None },
                Err(_) => return None,
            };
            // if count > 0 {
                // println!("Leftover original states: {}", original_predicates.decompile(self.maps));
                // println!("Node state: {}", state.decompile(self.maps));
                Some(SolutionNode{cost:if original_predicates.len() > 0 { from.cost+1 } else { 0 }, action:action_idx as ASTActionUsize, state, original_predicates})
            // } else {
            //     None
            // }
        } else {
            None
        }
    }

    fn is_meets_goal(&self, node:&SolutionNode, args:&mut PhantomData<bool>) -> bool {
        // inertia search meets goal, when none of the original action wants are wanted anymore.
        node.original_predicates.len() == 0
    }

    fn action_neighbors(&self, from:Option<ASTActionUsize>) -> std::slice::Iter<'_, ASTActionUsize> {
        if let Some(idx) = from {
            self.action_graph[idx as usize].iter()
        } else {
            self.try_all_actions.iter()
        }
    }
}



impl Ord for SolutionNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let my_states = self.original_predicates.len() + self.state.len();
        let other_states = other.original_predicates.len() + other.state.len();
        other_states.cmp(&my_states)
    }
}
impl PartialOrd for SolutionNode  {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl AStarNode<State> for SolutionNode {
    type PathType = ASTActionUsize;

    type CostType = i64;

    fn node_state(&self) -> &State {
        &self.state
    }

    fn state_size(&self) -> usize {
        std::mem::size_of::<u8>()*self.state.len()+std::mem::size_of::<Vec<u8>>()
    }

    fn path_id(&self) -> Option<Self::PathType> {
        Some(self.action)
    }

    fn estimate(&self) -> Self::CostType {
        self.cost+(self.original_predicates.len() as IntValue)
    }

    fn cost(&self) -> Self::CostType {
        self.cost
    }
}


#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{lib_tests::load_repo_pddl, search::{AstarInternals, a_star}, compiler::{solution_estimation::{SolutionNode, State}, inertia::{ActionInertia, Relationship}, ASTActionUsize, domain::CompiledAtomicFormula}};

    use super::InertiaProblem;

    // #[test]
    // fn test_removing_wants() {
    //     let sources = load_repo_pddl(
    //         "sample_problems/barman/domain.pddl",
    //         "sample_problems/barman/problem_5_10_7.pddl",
    //     );
    //     // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
    //     let (domain, problem) = sources.parse();
    //     let c_problem = sources.compile(&domain, &problem);
    //     let problem = InertiaProblem::new(2, &domain, &problem, &c_problem.inertia, &c_problem.maps, c_problem.constant_predicate_ids.clone());
    //     let mut state = vec![CompiledAtomicFormula{ predicate_idx: 0, args:vec![0]}];
    //     let mut inverse_state = vec![CompiledAtomicFormula{ predicate_idx: 1, args:vec![0] }];
    //     let mutator = vec![CompiledAtomicFormula{predicate_idx:0, args:vec![1]}];
    //     let result = problem.remove_states(&mut state, &mut inverse_state, &mutator, false);
    //     assert_eq!(state.len(), 0);
    //     assert_eq!(inverse_state.len(), 1);
    //     assert_eq!(result, Ok(1));

    //     let mut state = vec![CompiledAtomicFormula{ predicate_idx: 0, args:vec![1] }];
    //     let mut inverse_state = vec![CompiledAtomicFormula{ predicate_idx: 1, args:vec![1] }];
    //     let mutator = vec![CompiledAtomicFormula{predicate_idx:0, args:vec![1]}];
    //     let result = problem.remove_states(&mut state, &mut inverse_state, &mutator, false);
    //     assert_eq!(state.len(), 0);
    //     assert_eq!(inverse_state.len(), 1);
    //     assert_eq!(result, Ok(1));

    //     let mut state = vec![CompiledAtomicFormula{ predicate_idx: 0, args:vec![1] }];
    //     let mut inverse_state = vec![CompiledAtomicFormula{ predicate_idx: 1, args:vec![1] }];
    //     let mutator = vec![CompiledAtomicFormula{predicate_idx:0, args:vec![1]}];
    //     let result = problem.remove_states(&mut state, &mut inverse_state, &mutator, false);
    //     assert_eq!(state.len(), 1);
    //     assert_eq!(inverse_state.len(), 1);
    //     assert_eq!(result, Ok(0));
    // }

    #[test]
    fn test_inertia_ngrams() {
        let sources = load_repo_pddl(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
        );
        // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let c_problem = sources.compile(&domain, &problem);
        
        let mut args = AstarInternals::new();
        let problem = InertiaProblem::new(11, &domain, &problem, &c_problem.inertia, &c_problem.maps, c_problem.constant_predicate_ids.clone());
        println!("Searching for paths to {}", domain.get_action_string(problem.to_task));
        let mut result = a_star(&problem, true, &mut args);
        args.print_statistics();
        if result.len() == 0 {
            let all_paths = args.all_discovered_paths();
            println!("Found {} possible paths", all_paths.len());
            let mut histogram: HashMap<ASTActionUsize, usize> = HashMap::new();
            for (i, path) in all_paths.iter().enumerate() {
                if path.ends_with(&[5, 6, 2, 0]) {
                    let mut p = path.clone();
                    p.reverse();
                    println!("{}: {}", i, p.iter().map(|a| domain.get_action_name(*a as usize).1).collect::<Vec<_>>().join(", "))
                }
                for action in path {
                    if *action != problem.to_task as ASTActionUsize {
                        if let Some(count) = histogram.get_mut(action) {
                            *count += 1;
                        } else {
                            histogram.insert(*action, 1);
                        }
                    }
                }
            }
            for (action, count) in histogram.drain() {
                let percent = (count as f32)*100.0 / all_paths.len() as f32;
                if percent >= 100.0 && problem.inertia.cmp(action as usize, problem.to_task, problem.maps) == Relationship::Enables {
                    println!("{}: {:.2}% {:?} {}", domain.actions[action as usize].name(), percent, problem.inertia.cmp(action as usize, problem.to_task, problem.maps), domain.get_action_name(problem.to_task).1);
                }
            }
        } else {
            result.reverse();
            let s = result.iter().map(|idx| domain.get_action_name(*idx as usize).1).collect::<Vec<_>>().join(", ");
                println!("{}", s);

        }
    }
}