//! Type checker for Simple language
//!
//! This module implements bidirectional type checking with a focus on:
//! - Promise auto-wrapping for async functions
//! - Function signature validation
//! - Return type checking
//!
//! ## Architecture
//!
//! The type checker operates in multiple passes:
//! 1. Collect function signatures (already done in HIR lowering)
//! 2. Check function bodies match signatures
//! 3. Apply Promise auto-wrapping for async functions
//!
//! ## Promise Auto-Wrapping
//!
//! Functions with suspension operators (`~=`, `if~`, etc.) are async.
//! If such a function declares return type `T`, the type checker
//! automatically wraps it to `Promise<T>`.
//!
//! Example:
//! ```simple
//! fn fetch_user(id: i64) -> User:  # Declared as User
//!     val resp ~= http.get(url)
//!     return parse(resp)
//! # Auto-wrapped to: -> Promise<User>
//! ```

use crate::hir::{HirFunction, HirModule, HirType, LowerError, LowerResult, TypeId, TypeRegistry};
use std::collections::HashMap;

/// Type checker context
pub struct TypeChecker {
    /// Function return types (for checking calls)
    function_types: HashMap<String, TypeId>,
}

impl TypeChecker {
    /// Create a new type checker
    pub fn new() -> Self {
        Self {
            function_types: HashMap::new(),
        }
    }

    /// Register a function's signature
    pub fn register_function(&mut self, name: String, return_type: TypeId) {
        self.function_types.insert(name, return_type);
    }

    /// Check if a function needs Promise wrapping
    ///
    /// A function needs Promise wrapping if:
    /// 1. It has suspension operators (has_suspension = true)
    /// 2. Its return type is NOT already a Promise
    pub fn needs_promise_wrapping(&self, func: &HirFunction, types: &TypeRegistry) -> bool {
        // Only async functions need wrapping
        if !func.has_suspension {
            return false;
        }

        // Check if return type is already a Promise
        if let Some(ty) = types.get(func.return_type) {
            if ty.is_promise() {
                return false; // Already wrapped
            }
        }

        // Void functions don't need wrapping (they return Promise<()> implicitly)
        if func.return_type == TypeId::VOID {
            return false;
        }

        true
    }

    /// Wrap a function's return type in Promise<T>
    ///
    /// Transforms: fn() -> T  to  fn() -> Promise<T>
    pub fn wrap_return_in_promise(
        &self,
        func: &mut HirFunction,
        types: &mut TypeRegistry,
    ) -> LowerResult<()> {
        let inner_type = func.return_type;
        let promise_type = types.register(HirType::promise(inner_type));
        func.return_type = promise_type;
        Ok(())
    }

    /// Apply Promise auto-wrapping to all async functions in a module
    ///
    /// This is the main entry point for the type checker.
    /// Called after HIR lowering to auto-wrap async function returns.
    pub fn apply_promise_wrapping(
        &mut self,
        module: &mut HirModule,
    ) -> LowerResult<()> {
        // Collect all function signatures first
        for func in &module.functions {
            self.register_function(func.name.clone(), func.return_type);
        }

        // Apply Promise wrapping where needed
        for func in &mut module.functions {
            if self.needs_promise_wrapping(func, &module.types) {
                self.wrap_return_in_promise(func, &mut module.types)?;
            }
        }

        Ok(())
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{ConcurrencyMode, VerificationMode};

    #[test]
    fn test_promise_type_helpers() {
        let promise = HirType::promise(TypeId::I64);
        assert!(promise.is_promise());
        assert_eq!(promise.promise_inner(), Some(TypeId::I64));

        let not_promise = HirType::Bool;
        assert!(!not_promise.is_promise());
        assert_eq!(not_promise.promise_inner(), None);
    }

    #[test]
    fn test_needs_promise_wrapping() {
        let checker = TypeChecker::new();
        let mut types = TypeRegistry::new();

        // Sync function - no wrapping
        let sync_func = HirFunction {
            name: "sync_fn".to_string(),
            span: None,
            params: vec![],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![],
            visibility: simple_parser::ast::Visibility::Public,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: VerificationMode::default(),
            is_ghost: false,
            is_sync: true,
            has_suspension: false,
        };
        assert!(!checker.needs_promise_wrapping(&sync_func, &types));

        // Async function - needs wrapping
        let async_func = HirFunction {
            name: "async_fn".to_string(),
            span: None,
            params: vec![],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![],
            visibility: simple_parser::ast::Visibility::Public,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: VerificationMode::default(),
            is_ghost: false,
            is_sync: false,
            has_suspension: true,
        };
        assert!(checker.needs_promise_wrapping(&async_func, &types));

        // Async function with Promise return - no wrapping
        let promise_type = types.register(HirType::promise(TypeId::I64));
        let already_wrapped = HirFunction {
            name: "wrapped_fn".to_string(),
            span: None,
            params: vec![],
            locals: vec![],
            return_type: promise_type,
            body: vec![],
            visibility: simple_parser::ast::Visibility::Public,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: VerificationMode::default(),
            is_ghost: false,
            is_sync: false,
            has_suspension: true,
        };
        assert!(!checker.needs_promise_wrapping(&already_wrapped, &types));
    }
}
