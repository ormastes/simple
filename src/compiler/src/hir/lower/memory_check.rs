//! Memory safety violation detection during HIR lowering
//!
//! This module provides helper functions to detect memory safety violations
//! and emit appropriate warnings (W1001-W1006).

use simple_parser::ast::Mutability;
use simple_parser::Span;

use super::super::types::{HirExpr, HirExprKind, HirType, PointerKind, TypeId};
use super::context::FunctionContext;
use super::lowerer::Lowerer;
use super::memory_warning::{MemoryWarning, MemoryWarningCode};

impl Lowerer {
    /// Check if a type is a shared pointer (*T)
    pub(super) fn is_shared_pointer(&self, ty: TypeId) -> bool {
        if let Some(hir_type) = self.module.types.get(ty) {
            matches!(
                hir_type,
                HirType::Pointer {
                    kind: PointerKind::Shared,
                    ..
                }
            )
        } else {
            false
        }
    }

    /// Check if a type is a unique pointer (&T)
    pub(super) fn is_unique_pointer(&self, ty: TypeId) -> bool {
        if let Some(hir_type) = self.module.types.get(ty) {
            matches!(
                hir_type,
                HirType::Pointer {
                    kind: PointerKind::Unique,
                    ..
                }
            )
        } else {
            false
        }
    }

    /// Check if a type is any pointer type
    pub(super) fn is_pointer_type(&self, ty: TypeId) -> bool {
        if let Some(hir_type) = self.module.types.get(ty) {
            matches!(hir_type, HirType::Pointer { .. })
        } else {
            false
        }
    }

    /// Get the pointer kind for a type, if it's a pointer
    pub(super) fn get_pointer_kind(&self, ty: TypeId) -> Option<PointerKind> {
        if let Some(HirType::Pointer { kind, .. }) = self.module.types.get(ty) {
            Some(*kind)
        } else {
            None
        }
    }

    /// Check if a type is a reference type (pointer/borrow that has lifetime concerns)
    /// This includes unique pointers (&T), borrows (&T, &mut T), but NOT shared pointers (*T)
    /// as shared pointers are reference counted and don't have lifetime issues
    pub(super) fn is_reference_type(&self, ty: TypeId) -> bool {
        if let Some(hir_type) = self.module.types.get(ty) {
            matches!(
                hir_type,
                HirType::Pointer {
                    kind: PointerKind::Unique
                        | PointerKind::Borrow
                        | PointerKind::BorrowMut
                        | PointerKind::RawConst
                        | PointerKind::RawMut,
                    ..
                }
            )
        } else {
            false
        }
    }

    /// Get type name for error messages
    pub(super) fn get_type_name(&self, ty: TypeId) -> String {
        if let Some(hir_type) = self.module.types.get(ty) {
            match hir_type {
                HirType::Pointer { kind, inner, .. } => {
                    let prefix = match kind {
                        PointerKind::Unique => "&",
                        PointerKind::Shared => "*",
                        PointerKind::Weak => "-",
                        PointerKind::Handle => "+",
                        PointerKind::Borrow => "&",
                        PointerKind::BorrowMut => "&mut ",
                        PointerKind::RawConst => "*const ",
                        PointerKind::RawMut => "*mut ",
                    };
                    format!("{}{}", prefix, self.get_type_name(*inner))
                }
                HirType::Struct { name, .. } => name.clone(),
                HirType::Enum { name, .. } => name.clone(),
                HirType::Int { bits, .. } => format!("i{}", bits),
                HirType::Float { bits } => format!("f{}", bits),
                HirType::Bool => "bool".to_string(),
                HirType::String => "String".to_string(),
                HirType::Void => "void".to_string(),
                HirType::Array { element, size } => {
                    if let Some(s) = size {
                        format!("[{}; {}]", self.get_type_name(*element), s)
                    } else {
                        format!("[{}]", self.get_type_name(*element))
                    }
                }
                _ => format!("{:?}", hir_type),
            }
        } else {
            format!("TypeId({})", ty.0)
        }
    }

    /// W1001: Check for shared pointer mutation
    /// Called when we see an assignment to a field through a pointer
    pub(super) fn check_shared_mutation(&mut self, target: &HirExpr, span: Span) {
        // Check if the target is a field access through a shared pointer
        if let HirExprKind::FieldAccess { receiver, field_index } = &target.kind {
            if self.is_shared_pointer(receiver.ty) {
                let type_name = self.get_type_name(receiver.ty);
                let field_name = format!("field_{}", field_index);
                self.memory_warnings.warn(
                    MemoryWarning::new(MemoryWarningCode::W1001, span)
                        .with_type(&type_name)
                        .with_name(&field_name)
                        .with_context("shared pointers (*T) are read-only; use COW pattern"),
                );
            }
        }
    }

    /// W1002: Check for implicit unique pointer copy
    /// Called when we see a variable being assigned without explicit move
    pub(super) fn check_unique_copy(&mut self, value: &HirExpr, span: Span, is_explicit_move: bool) {
        if is_explicit_move {
            return; // Explicit move is fine
        }

        if self.is_unique_pointer(value.ty) {
            // Check if the value is a variable reference (potential copy)
            if let HirExprKind::Local(_) | HirExprKind::Global(_) = &value.kind {
                let type_name = self.get_type_name(value.ty);
                self.memory_warnings.warn(
                    MemoryWarning::new(MemoryWarningCode::W1002, span)
                        .with_type(&type_name)
                        .with_context("unique pointers (&T) are move-only; use explicit `move` or `.clone()`"),
                );
            }
        }
    }

    /// W1003: Check for mutable binding with shared pointer type
    /// Called when we see `var x: *T = ...`
    pub(super) fn check_mutable_shared_binding(
        &mut self,
        var_name: &str,
        ty: TypeId,
        mutability: Mutability,
        span: Span,
    ) {
        if mutability == Mutability::Mutable && self.is_shared_pointer(ty) {
            let type_name = self.get_type_name(ty);
            self.memory_warnings.warn(
                MemoryWarning::new(MemoryWarningCode::W1003, span)
                    .with_name(var_name)
                    .with_type(&type_name)
                    .with_context("shared pointers cannot be reassigned; use `val` instead of `var`"),
            );
        }
    }

    /// W1006: Check for mutation without mut capability
    /// Called when we see an assignment and need to verify the target has mut
    pub(super) fn check_mutation_capability(&mut self, target: &HirExpr, span: Span, has_mut_capability: bool) {
        if has_mut_capability {
            return; // Has mut, all good
        }

        // Check if target is a field access or similar that requires mutation
        match &target.kind {
            HirExprKind::FieldAccess { field_index, .. } => {
                let field_name = format!("field_{}", field_index);
                self.memory_warnings.warn(
                    MemoryWarning::new(MemoryWarningCode::W1006, span)
                        .with_name(&field_name)
                        .with_context("mutation requires `mut` capability on the receiver"),
                );
            }
            HirExprKind::Index { .. } => {
                self.memory_warnings.warn(
                    MemoryWarning::new(MemoryWarningCode::W1006, span)
                        .with_context("mutation requires `mut` capability"),
                );
            }
            _ => {}
        }
    }

    /// W1005: Check for potential reference cycles in struct definitions
    /// Called when lowering struct definitions
    pub(super) fn check_potential_cycle(&mut self, struct_name: &str, field_type: TypeId, span: Span) {
        // Check if the field type contains a shared pointer to a type that could form a cycle
        if let Some(HirType::Pointer {
            kind: PointerKind::Shared,
            inner,
            ..
        }) = self.module.types.get(field_type)
        {
            // Check if inner type references back to the struct (simplified check)
            if let Some(HirType::Struct { name, .. }) = self.module.types.get(*inner) {
                if name == struct_name {
                    self.memory_warnings.warn(
                        MemoryWarning::new(MemoryWarningCode::W1005, span)
                            .with_type(&format!("*{}", struct_name))
                            .with_context("self-referential shared pointer creates cycle; use weak pointer (-T)"),
                    );
                }
            }
        }
    }

    /// Check if an expression has mutation capability
    ///
    /// Returns true if the expression can be legally mutated based on:
    /// - Local variable mutability (var vs val)
    /// - Pointer capability (Exclusive, Isolated allow mutation)
    /// - Receiver capability for field access
    pub(super) fn expr_has_mut_capability(&self, expr: &HirExpr, ctx: &FunctionContext) -> bool {
        match &expr.kind {
            // Local variable: check mutability and capability
            HirExprKind::Local(idx) => {
                // First check if the local is declared as mutable (var)
                if let Some(local) = ctx.get_local(*idx) {
                    if local.mutability == Mutability::Mutable {
                        return true;
                    }
                }
                // Also check if it has a mutable capability
                ctx.has_mut_capability(*idx)
            }

            // Field access: check receiver's capability
            HirExprKind::FieldAccess { receiver, .. } => self.expr_has_mut_capability(receiver, ctx),

            // Index access: check receiver's capability
            HirExprKind::Index { receiver, .. } => self.expr_has_mut_capability(receiver, ctx),

            // Deref: check the pointer's capability
            HirExprKind::Deref(inner) => {
                // Check if the inner type is a pointer with mut capability
                if let Some(HirType::Pointer { capability, .. }) = self.module.types.get(inner.ty) {
                    capability.allows_mutation()
                } else {
                    false
                }
            }

            // Global variables are generally mutable (for now)
            HirExprKind::Global(_) => true,

            // Other expressions: check if they are pointers with mut capability
            _ => {
                if let Some(HirType::Pointer { capability, .. }) = self.module.types.get(expr.ty) {
                    capability.allows_mutation()
                } else {
                    // Non-pointer types: value semantics, mutability depends on binding
                    // This case shouldn't typically be reached for assignment targets
                    false
                }
            }
        }
    }

    /// Get the reference ID for an expression (for aliasing tracking)
    /// Returns Some(id) if the expression represents a trackable reference
    pub(super) fn get_expr_ref_id(&self, expr: &HirExpr) -> Option<usize> {
        match &expr.kind {
            HirExprKind::Local(idx) => Some(*idx),
            HirExprKind::FieldAccess { receiver, field_index } => {
                // Combine receiver ID with field index for unique identification
                self.get_expr_ref_id(receiver)
                    .map(|base_id| base_id * 1000 + field_index)
            }
            HirExprKind::Index { receiver, .. } => {
                // For array indexing, just use the receiver ID
                // (we can't statically determine the index)
                self.get_expr_ref_id(receiver)
            }
            HirExprKind::Deref(inner) => self.get_expr_ref_id(inner),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    // Tests are in memory_warning.rs
}
