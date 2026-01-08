// Static Polymorphism: Interface Binding Resolution
//
// This module handles:
// - Interface binding lookup for static dispatch
// - Trait type resolution through bindings
// - Dispatch mode determination (static vs dynamic)

/// Dispatch mode for trait method calls
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchMode {
    /// Static dispatch: monomorphized, direct call (when binding exists)
    Static,
    /// Dynamic dispatch: vtable lookup (when no binding exists)
    Dynamic,
}

impl TypeChecker {
    /// Look up interface binding for a trait
    /// Returns Some(impl_type) if bound, None if not bound (dynamic dispatch)
    pub fn lookup_binding(&self, trait_name: &str) -> Option<&Type> {
        self.interface_bindings.get(trait_name)
    }

    /// Resolve a trait type through interface binding
    /// If bound: returns the implementation type (for static dispatch)
    /// If not bound: returns DynTrait (for dynamic dispatch)
    pub fn resolve_trait_type(&self, trait_name: &str) -> Type {
        match self.interface_bindings.get(trait_name) {
            Some(impl_type) => impl_type.clone(),
            None => Type::DynTrait(trait_name.to_string()),
        }
    }

    /// Determine dispatch mode for a trait
    /// Static if binding exists, Dynamic otherwise
    pub fn get_dispatch_mode(&self, trait_name: &str) -> DispatchMode {
        if self.interface_bindings.contains_key(trait_name) {
            DispatchMode::Static
        } else {
            DispatchMode::Dynamic
        }
    }

    /// Check if a binding is valid (implementation type actually implements the trait)
    pub fn is_valid_binding(&self, trait_name: &str) -> bool {
        if let Some(_impl_type) = self.interface_bindings.get(trait_name) {
            // Check that impl_type implements trait_name
            // For now, assume bindings are valid if the trait exists
            self.env.contains_key(trait_name)
        } else {
            false
        }
    }

    /// Get all interface bindings (for code generation)
    pub fn get_all_bindings(&self) -> &HashMap<String, Type> {
        &self.interface_bindings
    }
}
