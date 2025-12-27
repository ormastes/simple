use std::collections::HashMap;

use simple_parser::ast::Mutability;

use super::super::types::{LocalVar, TypeId};

/// Context for contract expression lowering
#[derive(Debug, Clone, Default)]
pub(super) struct ContractLoweringContext {
    /// Postcondition binding name (e.g., "ret" in out(ret):)
    pub postcondition_binding: Option<String>,
    /// Error postcondition binding name (e.g., "err" in out_err(err):)
    pub error_binding: Option<String>,
}

pub(super) struct FunctionContext {
    pub locals: Vec<LocalVar>,
    pub local_map: HashMap<String, usize>,
    pub return_type: TypeId,
    /// Contract context for binding names (None when not in contract lowering)
    pub contract_ctx: Option<ContractLoweringContext>,
}

impl FunctionContext {
    pub fn new(return_type: TypeId) -> Self {
        Self {
            locals: Vec::new(),
            local_map: HashMap::new(),
            return_type,
            contract_ctx: None,
        }
    }

    pub fn add_local(&mut self, name: String, ty: TypeId, mutability: Mutability) -> usize {
        self.add_local_with_inject(name, ty, mutability, false)
    }

    /// Add a local variable with optional inject flag (for parameters) (#1013)
    pub fn add_local_with_inject(&mut self, name: String, ty: TypeId, mutability: Mutability, inject: bool) -> usize {
        self.add_local_full(name, ty, mutability, inject, false)
    }

    /// Add a local variable with all options (inject, ghost)
    pub fn add_local_full(&mut self, name: String, ty: TypeId, mutability: Mutability, inject: bool, is_ghost: bool) -> usize {
        let index = self.locals.len();
        self.locals.push(LocalVar {
            name: name.clone(),
            ty,
            mutability,
            inject,
            is_ghost,
        });
        self.local_map.insert(name, index);
        index
    }

    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.local_map.get(name).copied()
    }

    /// Check if the given name is the postcondition binding
    pub fn is_postcondition_binding(&self, name: &str) -> bool {
        if let Some(ref ctx) = self.contract_ctx {
            if let Some(ref binding) = ctx.postcondition_binding {
                return binding == name;
            }
        }
        false
    }

    /// Check if the given name is the error postcondition binding
    pub fn is_error_binding(&self, name: &str) -> bool {
        if let Some(ref ctx) = self.contract_ctx {
            if let Some(ref binding) = ctx.error_binding {
                return binding == name;
            }
        }
        false
    }
}
