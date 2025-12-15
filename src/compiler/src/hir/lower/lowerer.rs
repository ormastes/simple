use std::collections::HashMap;

use simple_parser::Pattern;

use super::super::types::{HirModule, TypeId};

pub struct Lowerer {
    pub(super) module: HirModule,
    pub(super) globals: HashMap<String, TypeId>,
}

impl Lowerer {
    pub fn new() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
        }
    }

    pub(super) fn extract_pattern_name(pattern: &Pattern) -> Option<String> {
        match pattern {
            Pattern::Identifier(n) => Some(n.clone()),
            Pattern::MutIdentifier(n) => Some(n.clone()),
            Pattern::Typed { pattern: inner, .. } => Self::extract_pattern_name(inner),
            _ => None,
        }
    }
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}
