#[derive(Debug, PartialEq)]
/// Node in the action graph representing order of actions to try or a preemtion point
/// when it's more likely that the tried actions lead to the goal.
pub enum TryNode {
    /// Index of the next action in the [`CompiledProblem`]`.actions` vector.
    Action(usize),
    /// Dispatch previously seen actions to an inner loop of the search algorithm
    /// As the chances one of them is the one needed is high.
    PreemptionPoint,
}

/// A list of next actions to try
pub type TryNodeList = Vec<TryNode>;
