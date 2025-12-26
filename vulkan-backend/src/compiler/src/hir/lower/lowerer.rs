use std::collections::{HashMap, HashSet};

use simple_parser::Pattern;

use super::super::types::{HirModule, TypeId};

pub struct Lowerer {
    pub(super) module: HirModule,
    pub(super) globals: HashMap<String, TypeId>,
    /// Set of function names that are marked with #[pure] (CTR-031)
    /// These functions can be called from contract expressions
    pub(super) pure_functions: HashSet<String>,
    /// Current class/struct type being lowered (for Self resolution)
    pub(super) current_class_type: Option<TypeId>,
}

impl Lowerer {
    pub fn new() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
        }
    }

    /// Check if a function is marked as pure
    pub fn is_pure_function(&self, name: &str) -> bool {
        self.pure_functions.contains(name)
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
