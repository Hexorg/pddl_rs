use std::collections::{HashSet, HashMap};

use crate::{Error, compiler::domain_data};

use super::{domain_data::DomainData, CompiledAction, Instruction, Runnable};

/// Inertia encoded from the perspective of a state bit.
/// Each field is a list of actions that effect this bit.
#[derive(Debug, PartialEq, Clone)]
pub struct Inertia {
    pub wants_negative: HashSet<usize>,
    pub wants_positive: HashSet<usize>,
    pub provides_negative: HashSet<usize>,
    pub provides_positive: HashSet<usize>,
}
impl Inertia {
    pub fn new() -> Self {
        Self {
            wants_negative: HashSet::new(),
            wants_positive: HashSet::new(),
            provides_negative: HashSet::new(),
            provides_positive: HashSet::new(),
        }
    }
}


fn remove_unused(remove_action_vector:Vec<usize>, unused_bit:&HashSet<usize>, actions:&mut Vec<CompiledAction>, action_inertia:&mut Vec<Inertia>, state_inertia:&mut Vec<Inertia>, domain_data:&mut DomainData) {
    /// If history is [None, None, None, None, None, None]
    /// Remove action # 4
    /// History is [None, None, None, None, None, Some(4)] because 5th action is not at index 4
    /// Remove action # 3
    /// History is [None, None, None, None, Some(3), Some(4)]
    /// That means action #5 is now at offset 3
    fn _find_new_offset(mut old_index:usize, history:&Vec<Option<usize>>) -> usize {
        while let Some(next_idx) = history[old_index] {
            old_index = next_idx;
        }
        old_index
    }
    let mut last_removed_idx:usize = 0; // since the vector is sorted - just keep track of the last removed action idx to remove duplicates
    let mut remove_action_history = vec![None;actions.len()];
    let mut removed_actions = HashSet::new();
    for idx in remove_action_vector.iter().rev() {
        if *idx != last_removed_idx { // ignore duplicates
            removed_actions.insert(*idx);
            // *idx needs to be removed
            actions.swap_remove(*idx); // actions.len()-1 gets moved to *idx
            action_inertia.swap_remove(*idx);
            remove_action_history[actions.len()] = Some(*idx);
            last_removed_idx = *idx;
        }
    }

    let mut new_predicate_map = HashMap::new();
    let mut remove_predicate_history = vec![None; domain_data.predicate_memory_map.len()];
    let mut unused_bit_vector:Vec<usize> = unused_bit.iter().map(|i| *i).collect();
    unused_bit_vector.sort();
    for bit in unused_bit_vector.iter().rev() {
        state_inertia.swap_remove(*bit);
        remove_predicate_history[state_inertia.len()] = Some(*bit);
    }
    for (vec, idx) in domain_data.predicate_memory_map.drain() {
        if !unused_bit.contains(&idx) {
            new_predicate_map.insert(vec, _find_new_offset(idx, &remove_predicate_history));
        } else {
            println!("Predicate {:?} is never used - removing it.", vec);
        }
    }
    domain_data.predicate_memory_map.extend(new_predicate_map);

    for idx in 0..actions.len() {
        // Patch actions to point at proper predicate locations.
        for instr_idx in 0..actions[idx].effect.len() {
            match actions[idx].effect[instr_idx] {
                Instruction::SetState(i) => actions[idx].effect[instr_idx] = Instruction::SetState(_find_new_offset(i, &remove_predicate_history)),
                _ => (),
            }
        }
        for instr_idx in 0..actions[idx].precondition.len() {
            match actions[idx].precondition[instr_idx] {
                Instruction::ReadState(i) => actions[idx].precondition[instr_idx] = Instruction::ReadState(_find_new_offset(i, &remove_predicate_history)),
                _ => (),
            }
        }
        // patch action inertia to point at the right actions.
        let inertia = &mut action_inertia[idx];
        inertia.provides_negative = inertia.provides_negative.difference(&unused_bit).map(|idx| _find_new_offset(*idx, &remove_predicate_history)).collect();
        inertia.provides_positive = inertia.provides_positive.difference(&unused_bit).map(|idx| _find_new_offset(*idx, &remove_predicate_history)).collect();
        inertia.wants_negative = inertia.wants_negative.difference(&unused_bit).map(|idx| _find_new_offset(*idx, &remove_predicate_history)).collect();
        inertia.wants_positive = inertia.wants_positive.difference(&unused_bit).map(|idx| _find_new_offset(*idx, &remove_predicate_history)).collect();
    }
    for bit in 0..state_inertia.len() {
        let inertia = &mut state_inertia[bit];
        inertia.provides_negative = inertia.provides_negative.difference(&removed_actions).map(|idx| _find_new_offset(*idx, &remove_action_history)).collect();
        inertia.provides_positive = inertia.provides_positive.difference(&removed_actions).map(|idx| _find_new_offset(*idx, &remove_action_history)).collect();
        inertia.wants_negative = inertia.wants_negative.difference(&removed_actions).map(|idx| _find_new_offset(*idx, &remove_action_history)).collect();
        inertia.wants_positive = inertia.wants_positive.difference(&removed_actions).map(|idx| _find_new_offset(*idx, &remove_action_history)).collect();
    }
}

pub fn process_inertia<'src>(mut state_inertia:Vec<Inertia>, mut action_inertia:Vec<Inertia>, init:&[Instruction], actions:&mut Vec<CompiledAction<'src>>, domain_data:&mut DomainData<'src>, ) -> Result<(), Error<'src>> {
    let (unused_bit, unread_bit, unset_bit) = unsused_bits(&state_inertia);
    if unread_bit.len() > 0 {
        for bit in unread_bit {
            let (vec, _) = domain_data.predicate_memory_map.iter().find(|(_, idx)| (**idx) == bit).unwrap();
            // TODO: Better error handling
            return Err(Error {input: None, kind:crate::ErrorKind::UnreadPredicate(vec[0]), chain:None, range:0..0 })
        }
    }
    let remove_action_vector = unused_actions(&state_inertia, init, &unset_bit);
    remove_unused(remove_action_vector, &unused_bit, actions, &mut action_inertia, &mut state_inertia, domain_data);

    let mut max_next_len = 0;
    for action_idx in 0..actions.len() {
        // let priority = domain_data.action_graph.priority.get_mut(action_idx).unwrap();

        // for bit in &action_inertia[action_idx].wants_negative {
        //     state_inertia[*bit].provides_negative
        // }
        // for bit in &action_inertia[action_idx].wants_positive {
        //     next_actions.extend(state_inertia[*bit].provides_positive.iter().map(|i| TryNode::Action(*i)));
        // }
        // if next_actions.len() > max_next_len {
        //     max_next_len = next_actions.len();
        // }
        // for bit in 0..domain_data.predicate_memory_map.len() {
        //     if !
        // }
        // next_actions.push(TryNode::PreemptionPoint);
    }
    println!("Out of {} actions each time we only need to call at most {}", actions.len(), max_next_len);
    Ok(())
}

fn unsused_bits(inertia:&Vec<Inertia>) -> (HashSet<usize>, HashSet<usize>, HashSet<usize>) {
    let mut unused_bit = HashSet::new();
    let mut unread_bit = HashSet::new();
    let mut unset_bit = HashSet::new();
    
    // Tally up the unused/unread/unset offsets
    for (offset, inertia) in inertia.iter().enumerate() {
        let mut neither_used = true;
        if inertia.wants_negative.len() == 0 && inertia.wants_positive.len() == 0 {
            unread_bit.insert(offset);
        } else {
            neither_used = false;
        }
        if inertia.provides_negative.len() == 0 && inertia.provides_positive.len() == 0 {
            unset_bit.insert(offset);
        } else {
            neither_used = false;
        }
        if neither_used {
            unset_bit.remove(&offset);
            unread_bit.remove(&offset);
            unused_bit.insert(offset);
        }
    }
    (unused_bit, unread_bit, unset_bit)
}

fn unused_actions(inertia:&Vec<Inertia>, init:&[Instruction], unset_bit:&HashSet<usize>) -> Vec<usize> {
        // Run the problem init to generate entry state
        let mut state = vec![false; inertia.len()];
        let mut functions = vec![0];
        init.run_mut(&mut state, &mut functions);
    
        // Figure out which compiled actions can never be applied because 
        // They are disabled by problem init.
        let mut remove_action_vector = Vec::new(); // Technically needs to be a set of unique actions but we're going to sort it anyway so it becomes easy to filter dupes
        for offset in unset_bit {
            if state[*offset] {
                remove_action_vector.extend(&inertia[*offset].wants_negative);
            } else {
                remove_action_vector.extend(&inertia[*offset].wants_positive);
            }
        }
        // Sort the list of actions to remove because it's more efficient to remove actions from the end
        // instead of removing an action, shifting the whole action array, and recalculating new offsets.
        remove_action_vector.sort();
        remove_action_vector
}

#[cfg(test)]
mod test {
    use enumset::EnumSet;

    use crate::{lib_tests::load_repo_pddl, compiler::{parse_domain, parse_problem, domain_data::{preprocess, DomainData}, final_pass::final_pass, Optimization, inertia::Inertia, CompiledAction, action_graph::ActionGraph}, ReportPrinter, Requirement};
    use std::collections::{HashSet, HashMap};
    use super::remove_unused;

    #[test]
    fn test_remove_unused() {
        let remove_action_vector = vec![2];
        let unused_bit = HashSet::from([1]);
        let mut actions = vec![CompiledAction::new();3];
        let mut action_inertia = vec![Inertia::new();3];
        action_inertia[0].provides_negative.insert(2); // 0th action provices negative 2nd bit
        action_inertia[2].wants_negative.insert(2); // 2nd action wants negative 2nd bit
        let mut state_inertia = vec![Inertia::new();3];
        state_inertia[2].provides_negative.insert(0); 
        state_inertia[2].provides_negative.insert(2);
        let mut domain_data = DomainData{
            requirements: EnumSet::EMPTY,
            type_tree: HashMap::new(),
            type_src_pos: HashMap::new(),
            object_to_type_map: HashMap::new(),
            type_to_objects_map: HashMap::new(),
            object_src_pos: HashMap::new(),
            predicate_memory_map: HashMap::from([(vec!["p_one", "a"], 0), (vec!["p_one", "b"], 1), (vec!["p_one", "c"], 2)]),
            action_graph: ActionGraph::new(),
        };
        assert_eq!(state_inertia[2].provides_negative, HashSet::from([0, 2]));
        assert_eq!(action_inertia[0].provides_negative, HashSet::from([2]));
        remove_unused(remove_action_vector, &unused_bit, &mut actions, &mut action_inertia, &mut state_inertia, &mut domain_data);
        assert_eq!(domain_data.predicate_memory_map, HashMap::from([(vec!["p_one", "a"], 0), (vec!["p_one", "c"], 1)]));
        assert_eq!(state_inertia.len(), 2);
        assert_eq!(state_inertia[0].wants_negative, HashSet::new());
        assert_eq!(state_inertia[1].provides_negative, HashSet::from([0]));
        assert_eq!(actions.len(), 2);
        assert_eq!(action_inertia.len(), 2);
        assert_eq!(action_inertia[0].provides_negative, HashSet::from([1]));

    }
    #[test]
    fn test_inertia() {
        let domain_filename = "sample_problems/simple_domain.pddl";
        let problem_filename = "sample_problems/simple_problem.pddl";
        let (domain_src, problem_src) = load_repo_pddl(domain_filename, problem_filename);
        let domain = parse_domain(&domain_src).unwrap_or_print_report(domain_filename, &domain_src);
        let problem = parse_problem(&problem_src, Requirement::Typing.into()).unwrap_or_print_report(problem_filename, &problem_src);
        let preprocess = preprocess(&domain, &problem).unwrap();
        let c_problem = final_pass(preprocess, &domain, &problem, Optimization::Inertia.into()).unwrap_or_print_report(problem_filename, &problem_src);
        println!("Compiled problem uses {} bits of memory and has {} actions.", c_problem.memory_size, c_problem.actions.len());
        
    }
}