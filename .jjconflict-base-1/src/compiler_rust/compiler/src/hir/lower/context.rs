use std::collections::HashMap;

use simple_parser::ast::{Mutability, ReferenceCapability};

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
    /// Capability tracking for each local variable (local_id -> capability)
    pub local_capabilities: HashMap<usize, ReferenceCapability>,
    /// Whether this function has an implicit self parameter (is a method)
    pub has_self: bool,
    /// Whether this is a mutable method (uses `me` keyword instead of `fn`)
    /// Mutable methods can modify self and the changes persist
    pub is_me_method: bool,
}

impl FunctionContext {
    pub fn new(return_type: TypeId) -> Self {
        Self {
            locals: Vec::new(),
            local_map: HashMap::new(),
            return_type,
            contract_ctx: None,
            local_capabilities: HashMap::new(),
            has_self: false,
            is_me_method: false,
        }
    }

    /// Create a new function context for a method
    pub fn new_method(return_type: TypeId, is_me_method: bool) -> Self {
        Self {
            locals: Vec::new(),
            local_map: HashMap::new(),
            return_type,
            contract_ctx: None,
            local_capabilities: HashMap::new(),
            has_self: true,
            is_me_method,
        }
    }

    pub fn add_local(&mut self, name: String, ty: TypeId, mutability: Mutability) -> usize {
        self.add_local_with_inject(name, ty, mutability, false)
    }

    /// Add a local variable with optional inject flag (for parameters) (#1013)
    pub fn add_local_with_inject(&mut self, name: String, ty: TypeId, mutability: Mutability, inject: bool) -> usize {
        self.add_local_full(name, ty, None, mutability, inject, false)
    }

    pub fn add_local_with_inject_and_type_hint(
        &mut self,
        name: String,
        ty: TypeId,
        type_name_hint: Option<String>,
        mutability: Mutability,
        inject: bool,
    ) -> usize {
        self.add_local_full(name, ty, type_name_hint, mutability, inject, false)
    }

    /// Add a local variable with all options (inject, ghost)
    pub fn add_local_full(
        &mut self,
        name: String,
        ty: TypeId,
        type_name_hint: Option<String>,
        mutability: Mutability,
        inject: bool,
        is_ghost: bool,
    ) -> usize {
        let index = self.locals.len();
        self.locals.push(LocalVar {
            name: name.clone(),
            ty,
            type_name_hint,
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

    /// Restore a NAME->slot mapping to what it was before a scoped binding.
    ///
    /// `add_local_full` does `local_map.insert(name, index)`, which OVERWRITES
    /// any outer binding of that name permanently — there is no scope stack
    /// here. For a construct whose binding is supposed to be scoped (a `for`
    /// loop variable), the lowerer snapshots `lookup(name)` first and calls this
    /// afterwards to put the mapping back.
    ///
    /// Only the NAME MAPPING is restored. The `locals` slot itself is
    /// deliberately left in place: slot indices are already embedded in the
    /// lowered body, so removing or reusing the slot would invalidate them.
    /// Leaving a dead slot allocated is correct and costs one entry per loop.
    ///
    /// See doc/08_tracking/bug/for_loop_variable_leaks_into_enclosing_scope_2026-08-04.md
    pub fn restore_name_binding(&mut self, name: &str, previous: Option<usize>) {
        match previous {
            Some(index) => {
                self.local_map.insert(name.to_string(), index);
            }
            None => {
                self.local_map.remove(name);
            }
        }
    }

    /// Get a local variable by index
    pub fn get_local(&self, index: usize) -> Option<&LocalVar> {
        self.locals.get(index)
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

    /// Set the capability for a local variable
    pub fn set_local_capability(&mut self, local_index: usize, capability: ReferenceCapability) {
        self.local_capabilities.insert(local_index, capability);
    }

    /// Get the capability for a local variable (defaults to Shared if not set)
    pub fn get_local_capability(&self, local_index: usize) -> ReferenceCapability {
        self.local_capabilities
            .get(&local_index)
            .copied()
            .unwrap_or(ReferenceCapability::Shared)
    }

    /// Check if a local variable has mutation capability (Exclusive or Isolated)
    pub fn has_mut_capability(&self, local_index: usize) -> bool {
        self.get_local_capability(local_index).allows_mutation()
    }
}
