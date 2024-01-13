use crate::compiler::PredicateUsize;

use super::{name::Name, r#type::Type};


#[derive(PartialEq, Eq, Debug, Clone)]
pub struct List<'src> {
    pub items: Vec<Name<'src>>,
    pub kind: Type<'src>,
}

#[derive(PartialEq, Eq, Debug, Clone, Default)]
pub struct TypedList<'src>(Vec<List<'src>>);

impl<'src> From<Vec<List<'src>>> for TypedList<'src> {
    fn from(value: Vec<List<'src>>) -> Self {
        Self(value)
    }
}

impl<'src> IntoIterator for TypedList<'src> {
    type Item = List<'src>;
    type IntoIter = std::vec::IntoIter<List<'src>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, 'src> IntoIterator for &'a TypedList<'src> {
    type Item = &'a List<'src>;
    type IntoIter = std::slice::Iter<'a, List<'src>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}


impl<'src> TypedList<'src> {
    pub fn len(&self) -> usize {
        self.0.iter().fold(0, |acc,l| acc+l.items.len())
    }

    pub fn find<F>(&self, f:F) -> Option<PredicateUsize> where F:Fn(&Name<'src>)->bool{
        let mut idx = 0;
        for List { items, .. } in self {
            for item in items {
                if f(item) {
                    return Some(idx);
                }
                idx += 1;
            }
        }
        None
    }
    pub fn get_name(&self, mut idx:usize) -> Name<'src> {
        let mut type_pos = 0;
        while idx >= self.0[type_pos].items.len() {
            idx -= self.0[type_pos].items.len();
            type_pos+=1;
        }
        self.0[type_pos].items[idx]
    }

    pub fn get_type(&self, mut idx:usize) -> &Type<'src> {
        let mut type_pos = 0;
        while idx >= self.0[type_pos].items.len() {
            idx -= self.0[type_pos].items.len();
            type_pos+=1;
        }
        &self.0[type_pos].kind
    }
    pub fn to_string(&self) -> String {
        self.0.iter().map(|List { items, kind }| items.iter().map(|_| format!("{}", kind)).collect::<Vec<_>>().join(", ")).collect::<Vec<_>>().join(", ")
    }
}
