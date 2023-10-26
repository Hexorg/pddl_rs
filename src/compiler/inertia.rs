/// Inertia encoded from the perspective of a state bit.
/// Each field is a list of actions that effect this bit.
#[derive(Debug, PartialEq, Clone)]
pub struct StateInertia {
    pub wants_negative: Vec<usize>,
    pub wants_positive: Vec<usize>,
    pub provides_negative: Vec<usize>,
    pub provides_positive: Vec<usize>,
}
impl StateInertia {
    pub fn new() -> Self {
        Self {
            wants_negative: Vec::new(),
            wants_positive: Vec::new(),
            provides_negative: Vec::new(),
            provides_positive: Vec::new(),
        }
    }
}
