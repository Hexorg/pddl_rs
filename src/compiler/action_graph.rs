#[derive(Debug, PartialEq)]
pub struct ActionGraph {
    /// The priority matrix of actions - a square matrix where N is the number of actions in domain
    /// (unexpanded to objects in a problem) The offset is the current action index, 
    /// which points to a vector of which actions to try first. E.g. priority[4][0] will tell you the most likely action be tried right after
    /// action#4. priority[4][1] will tell you the second most likely action.
    /// The order item is u16 instead of usize to save some memory as I don't expect to 
    /// have more than 65535 typed actions in a domain.
    pub priority: Vec<Vec<u16>>
}

impl ActionGraph {
    pub fn new() -> Self {
        Self { priority: Vec::new() }
    }

    pub fn set_size(&mut self, size:usize) {
        for _ in 0..size {
            self.priority.push(Vec::new())
        }
    }

    pub fn fill(&mut self) {
        for i in 0..self.priority.len() {
            let mut inner_vec = Vec::with_capacity(self.priority.len());
            for x in 0..self.priority.len() {
                inner_vec.push(x as u16);
            }
            self.priority.push(inner_vec);
        }
    }
}