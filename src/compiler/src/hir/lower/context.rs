use std::collections::HashMap;

use simple_parser::ast::Mutability;

use super::super::types::{LocalVar, TypeId};

pub(super) struct FunctionContext {
    pub locals: Vec<LocalVar>,
    pub local_map: HashMap<String, usize>,
    #[allow(dead_code)]
    pub return_type: TypeId,
}

impl FunctionContext {
    pub fn new(return_type: TypeId) -> Self {
        Self {
            locals: Vec::new(),
            local_map: HashMap::new(),
            return_type,
        }
    }

    pub fn add_local(&mut self, name: String, ty: TypeId, mutability: Mutability) -> usize {
        let index = self.locals.len();
        self.locals.push(LocalVar {
            name: name.clone(),
            ty,
            mutability,
        });
        self.local_map.insert(name, index);
        index
    }

    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.local_map.get(name).copied()
    }
}
