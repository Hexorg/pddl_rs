use std::{collections::HashMap, marker::PhantomData};


use super::{StateUsize, domain::CompiledAtomicFormula};


pub struct AtomicFormulaMap {
    map: HashMap<CompiledAtomicFormula, StateUsize>,
    reverse: Vec<CompiledAtomicFormula>,
}

impl AtomicFormulaMap {
    pub fn new() -> Self {
        Self { map: HashMap::new(), reverse:Vec::new() }
    }

    pub fn allocate(&mut self, formula:CompiledAtomicFormula) {
        let len = self.map.len() as StateUsize;
        self.map.insert(formula.clone(), len);
        self.reverse.push(formula);
    }

    pub fn get(&self, formula:&CompiledAtomicFormula) -> Option<StateUsize> {
        self.map.get(formula).copied()
    }

    pub fn len(&self) -> usize {
        self.reverse.len()
    }
}