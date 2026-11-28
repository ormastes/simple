//! Rewrite unresolved bare receiver-field reads in method bodies.
//!
//! A plain `fn` class method may read a receiver field bare (`kind` meaning
//! `self.kind`). HIR lowering's lenient branch leaves such a name as
//! `HirExprKind::Global(name)` typed ANY, which every compiled lane rejected
//! as an unresolved `GlobalLoad`
//! (doc/08_tracking/bug/implicit_self_field_read_unresolved_in_plain_fn_method_2026-09-03.md).
//! The pure-Simple frontend resolves the same idiom to the receiver's field;
//! this pass rewrites the HIR body the same way BEFORE lowering, so the read
//! becomes an ordinary, CONCRETELY typed `self.<field>` field access.
//!
//! Typing is the point: with the read typed ANY, parent expressions take
//! runtime tag-dispatched paths (`rt_any_add`, boxed equality) that
//! misinterpret the raw field word. Re-typing the read to the field's
//! declared type reproduces exactly what an explicit `self.<field>` spelling
//! produces in every consumer.
//!
//! The pass only fires when all of these hold:
//! - the function's first parameter is the `self`/`me` receiver,
//! - the receiver type resolves to a struct/class with a field of that name,
//! - the name is not a known global/function/import (those keep the
//!   `GlobalLoad` path).
//!
//! Lambda bodies are deliberately NOT rewritten: a lambda is lowered as its
//! own function whose local 0 is not the receiver. A bare read there has no
//! receiver to resolve against and keeps the old fail-closed behavior.
//! Containers the walker does not enumerate keep the same fail-closed
//! behavior (the read stays a `Global` and codegen rejects it), matching the
//! pre-existing `expr_mentions_array` walker idiom.

use crate::hir::{HirExpr, HirExprKind, HirFunction, HirStmt, HirType, TypeId, TypeRegistry};
use std::collections::{HashMap, HashSet};

/// Per-function rewrite context: the receiver's fields plus the module-level
/// symbol tables that guard the rewrite (a name that positively resolves to
/// a global/function/import keeps its `GlobalLoad` path).
pub(super) struct ReceiverFieldRewrite<'a> {
    registry: &'a TypeRegistry,
    receiver_ty: TypeId,
    fields: &'a [(String, TypeId)],
    global_types: &'a HashMap<String, TypeId>,
    available_functions: &'a HashSet<String>,
    function_value_globals: &'a HashSet<String>,
    imported_function_names: &'a HashSet<String>,
}

impl<'a> ReceiverFieldRewrite<'a> {
    /// Resolve the rewrite context for a method body: `Some(..)` when the
    /// function's first parameter is the `self`/`me` receiver and its type
    /// declares fields.
    pub(super) fn for_function(
        func: &'a HirFunction,
        registry: &'a TypeRegistry,
        global_types: &'a HashMap<String, TypeId>,
        available_functions: &'a HashSet<String>,
        function_value_globals: &'a HashSet<String>,
        imported_function_names: &'a HashSet<String>,
    ) -> Option<Self> {
        let param = func.params.first()?;
        if param.name != "self" && param.name != "me" {
            return None;
        }
        let receiver_ty = param.ty;
        let mut ty = registry.get(receiver_ty);
        if let Some(HirType::Pointer { inner, .. }) = ty {
            // Classes are commonly pointer-wrapped at the MIR boundary;
            // follow one layer exactly like TypeRegistry::get_type_name.
            if *inner != receiver_ty {
                ty = registry.get(*inner);
            }
        }
        let Some(HirType::Struct { fields, .. }) = ty else {
            return None;
        };
        Some(Self {
            registry,
            receiver_ty,
            fields,
            global_types,
            available_functions,
            function_value_globals,
            imported_function_names,
        })
    }

    /// A `Global` name is rewritten only when it matches a receiver field and
    /// is not a known module-level symbol.
    fn resolve(&self, name: &str) -> Option<(usize, TypeId)> {
        if self.global_types.contains_key(name)
            || self.available_functions.contains(name)
            || self.function_value_globals.contains(name)
            || self.imported_function_names.contains(name)
        {
            return None;
        }
        self.fields
            .iter()
            .position(|(field, _)| field == name)
            .map(|index| (index, self.fields[index].1))
    }

    /// Cheap read-only probe with early exit: does the body contain any
    /// rewrite candidate? Avoids cloning method bodies that have none.
    pub(super) fn body_has_candidate(&self, body: &[HirStmt]) -> bool {
        body.iter().any(|stmt| self.stmt_has_candidate(stmt))
    }

    fn stmt_has_candidate(&self, stmt: &HirStmt) -> bool {
        match stmt {
            HirStmt::Let { value: Some(value), .. }
            | HirStmt::Expr(value)
            | HirStmt::Return(Some(value))
            | HirStmt::Assert { condition: value, .. }
            | HirStmt::Assume { condition: value, .. }
            | HirStmt::Admit { condition: value, .. } => self.expr_has_candidate(value),
            HirStmt::Assign { target: _, value } => self.expr_has_candidate(value),
            HirStmt::If {
                condition,
                then_block,
                else_block,
                ..
            } => {
                self.expr_has_candidate(condition)
                    || self.body_has_candidate(then_block)
                    || else_block.as_ref().is_some_and(|body| self.body_has_candidate(body))
            }
            HirStmt::While { condition, body, .. } => {
                self.expr_has_candidate(condition) || self.body_has_candidate(body)
            }
            HirStmt::For { iterable, body, .. } => {
                self.expr_has_candidate(iterable) || self.body_has_candidate(body)
            }
            HirStmt::Loop { body, .. } | HirStmt::Defer { body } => self.body_has_candidate(body),
            _ => false,
        }
    }

    fn expr_has_candidate(&self, expr: &HirExpr) -> bool {
        match &expr.kind {
            HirExprKind::Global(name) => self.resolve(name).is_some(),
            HirExprKind::Binary { left, right, .. } => {
                self.expr_has_candidate(left) || self.expr_has_candidate(right)
            }
            HirExprKind::Unary { operand, .. }
            | HirExprKind::FieldAccess { receiver: operand, .. }
            | HirExprKind::Ref(operand)
            | HirExprKind::Deref(operand)
            | HirExprKind::Cast { expr: operand, .. }
            | HirExprKind::ContractOld(operand)
            | HirExprKind::NeighborAccess { array: operand, .. } => self.expr_has_candidate(operand),
            HirExprKind::Call { func, args } => {
                self.expr_has_candidate(func) || args.iter().any(|arg| self.expr_has_candidate(arg))
            }
            HirExprKind::MethodCall { receiver, args, .. } => {
                self.expr_has_candidate(receiver) || args.iter().any(|arg| self.expr_has_candidate(arg))
            }
            HirExprKind::TypeParamStaticCall { args, .. } | HirExprKind::GpuIntrinsic { args, .. } => {
                args.iter().any(|arg| self.expr_has_candidate(arg))
            }
            HirExprKind::Index { receiver, index } => {
                self.expr_has_candidate(receiver) || self.expr_has_candidate(index)
            }
            HirExprKind::ArrayRepeat { value, count } => {
                self.expr_has_candidate(value) || self.expr_has_candidate(count)
            }
            HirExprKind::Tuple(items)
            | HirExprKind::Array(items)
            | HirExprKind::VecLiteral(items) => items.iter().any(|item| self.expr_has_candidate(item)),
            HirExprKind::StructInit { fields, .. } => {
                fields.iter().any(|field| self.expr_has_candidate(field))
            }
            HirExprKind::Dict(pairs) => pairs
                .iter()
                .any(|(key, value)| self.expr_has_candidate(key) || self.expr_has_candidate(value)),
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr_has_candidate(condition)
                    || self.expr_has_candidate(then_branch)
                    || else_branch
                        .as_ref()
                        .is_some_and(|branch| self.expr_has_candidate(branch))
            }
            HirExprKind::Block(body) | HirExprKind::UnsafeBlock { statements: body, .. } => {
                self.body_has_candidate(body)
            }
            // Deliberately not descended: lambda/generator/future/actor bodies
            // are separate functions whose local 0 is not the receiver.
            _ => false,
        }
    }

    /// Rewrite every candidate in the body in place.
    pub(super) fn rewrite_body(&self, body: &mut [HirStmt]) {
        for stmt in body {
            self.rewrite_stmt(stmt);
        }
    }

    fn rewrite_stmt(&self, stmt: &mut HirStmt) {
        match stmt {
            HirStmt::Let { value: Some(value), .. }
            | HirStmt::Expr(value)
            | HirStmt::Return(Some(value))
            | HirStmt::Assert { condition: value, .. }
            | HirStmt::Assume { condition: value, .. }
            | HirStmt::Admit { condition: value, .. } => self.rewrite_expr(value),
            HirStmt::Assign { target: _, value } => {
                // Assignment targets are deliberately left alone: a bare
                // `field = value` is the sibling defect
                // (implicit_self_field_assignment_still_silent_in_plain_fn_methods_2026-08-31.md),
                // owned by another lane. Only read positions rewrite here.
                self.rewrite_expr(value);
            }
            HirStmt::If {
                condition,
                then_block,
                else_block,
                ..
            } => {
                self.rewrite_expr(condition);
                self.rewrite_body(then_block);
                if let Some(else_block) = else_block {
                    self.rewrite_body(else_block);
                }
            }
            HirStmt::While { condition, body, .. } => {
                self.rewrite_expr(condition);
                self.rewrite_body(body);
            }
            HirStmt::For { iterable, body, .. } => {
                self.rewrite_expr(iterable);
                self.rewrite_body(body);
            }
            HirStmt::Loop { body, .. } | HirStmt::Defer { body } => self.rewrite_body(body),
            _ => {}
        }
    }

    fn rewrite_expr(&self, expr: &mut HirExpr) {
        match &mut expr.kind {
            HirExprKind::Global(name) => {
                if let Some((field_index, field_type)) = self.resolve(name) {
                    expr.kind = HirExprKind::FieldAccess {
                        receiver: Box::new(HirExpr {
                            kind: HirExprKind::Local(0),
                            ty: self.receiver_ty,
                        }),
                        field_index,
                    };
                    expr.ty = field_type;
                }
            }
            HirExprKind::Binary { left, right, .. } => {
                self.rewrite_expr(left);
                self.rewrite_expr(right);
            }
            HirExprKind::Unary { operand, .. }
            | HirExprKind::FieldAccess { receiver: operand, .. }
            | HirExprKind::Ref(operand)
            | HirExprKind::Deref(operand)
            | HirExprKind::Cast { expr: operand, .. }
            | HirExprKind::ContractOld(operand)
            | HirExprKind::NeighborAccess { array: operand, .. } => self.rewrite_expr(operand),
            HirExprKind::Call { func, args } => {
                self.rewrite_expr(func);
                for arg in args {
                    self.rewrite_expr(arg);
                }
            }
            HirExprKind::MethodCall { receiver, args, .. } => {
                self.rewrite_expr(receiver);
                for arg in args {
                    self.rewrite_expr(arg);
                }
            }
            HirExprKind::TypeParamStaticCall { args, .. } | HirExprKind::GpuIntrinsic { args, .. } => {
                for arg in args {
                    self.rewrite_expr(arg);
                }
            }
            HirExprKind::Index { receiver, index } => {
                self.rewrite_expr(receiver);
                self.rewrite_expr(index);
            }
            HirExprKind::ArrayRepeat { value, count } => {
                self.rewrite_expr(value);
                self.rewrite_expr(count);
            }
            HirExprKind::Tuple(items) | HirExprKind::Array(items) | HirExprKind::VecLiteral(items) => {
                for item in items {
                    self.rewrite_expr(item);
                }
            }
            HirExprKind::StructInit { fields, .. } => {
                for field in fields {
                    self.rewrite_expr(field);
                }
            }
            HirExprKind::Dict(pairs) => {
                for (key, value) in pairs {
                    self.rewrite_expr(key);
                    self.rewrite_expr(value);
                }
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.rewrite_expr(condition);
                self.rewrite_expr(then_branch);
                if let Some(else_branch) = else_branch {
                    self.rewrite_expr(else_branch);
                }
            }
            HirExprKind::Block(body) | HirExprKind::UnsafeBlock { statements: body, .. } => {
                self.rewrite_body(body)
            }
            // Deliberately not descended: lambda/generator/future/actor bodies
            // are separate functions whose local 0 is not the receiver.
            _ => {}
        }
    }
}
