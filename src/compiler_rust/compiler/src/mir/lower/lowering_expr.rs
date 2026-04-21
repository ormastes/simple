//! Expression lowering dispatcher for MIR.
//!
//! This module dispatches HIR expression kinds to their dedicated lowering
//! sub-modules. Implementation details live in:
//!
//! - `lowering_expr_literal`   — Integer, Float, Bool, String, Nil, ContractResult
//! - `lowering_expr_ident`     — Local, Global
//! - `lowering_expr_ops`       — Binary, Unary, Cast
//! - `lowering_expr_call`      — Call (direct + indirect)
//! - `lowering_expr_builtin`   — BuiltinCall
//! - `lowering_expr_method`    — MethodCall
//! - `lowering_expr_async`     — Lambda, Yield, GeneratorCreate, FutureCreate, Await, ActorSpawn
//! - `lowering_expr_collection`— Tuple, Array, VecLiteral, Dict, ArrayRepeat
//! - `lowering_expr_struct`    — StructInit, FieldAccess, Index
//! - `lowering_expr_ptr`       — PointerNew, Ref, Deref, ContractOld, NeighborAccess
//! - `lowering_expr_control`   — If, LetIn

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, HirExprKind, HirType, PointerKind, TypeId};
use crate::mir::instructions::VReg;

impl<'a> MirLowerer<'a> {
    /// Recover a named type for a method-call receiver whose own
    /// `receiver.ty` does not resolve to a named class via
    /// `TypeRegistry::get_type_name`.
    ///
    /// Round-16 introduced the Local-idx case (receiver is a bare local
    /// whose MIR local-table entry carries the user's `: T` annotation).
    /// Round-17 widens this to structural receivers whose sub-expression
    /// type is already registered:
    ///
    /// - `HirExprKind::FieldAccess { receiver, field_index }` — look up
    ///   `field_index` on `HirType::Struct { fields }` (also handles the
    ///   tuple-projection case `pair.0`, since tuples lower to
    ///   `FieldAccess` with a numeric index over `HirType::Tuple`).
    /// - `HirExprKind::Index { receiver, .. }` — element type of the
    ///   base's `HirType::Array` / `HirType::Simd` / `HirType::Pointer`.
    ///
    /// Each variant recurses: the base of a field access may itself be a
    /// field access (`self.a.b.init()`) or an array index
    /// (`containers[i].widget.init()`). A `Pointer` layer is transparently
    /// dereferenced because Simple classes are frequently passed by
    /// pointer at the MIR boundary.
    ///
    /// Returns `None` when no structural hop leads to a registered type —
    /// callers fall back to the bare method name, matching pre-Round-17
    /// behaviour.
    pub(super) fn recover_receiver_type(&mut self, expr: &HirExpr) -> Option<TypeId> {
        match &expr.kind {
            HirExprKind::Local(idx) => {
                let lookup_idx = *idx;
                self.with_func(|func, _| {
                    let nparams = func.params.len();
                    // Local indices include params first, then locals.
                    if lookup_idx < nparams {
                        Some(func.params[lookup_idx].ty)
                    } else {
                        let li = lookup_idx - nparams;
                        func.locals.get(li).map(|l| l.ty)
                    }
                })
                .ok()
                .flatten()
            }
            HirExprKind::FieldAccess {
                receiver: base,
                field_index,
            } => {
                // Base's own ty is preferred; if unnamed, walk through
                // another structural hop.
                let base_ty = if self.type_registry.and_then(|r| r.get_type_name(base.ty)).is_some() {
                    Some(base.ty)
                } else {
                    self.recover_receiver_type(base)
                }?;
                let registry = self.type_registry?;
                // Follow a single pointer layer — classes are commonly
                // wrapped in `Pointer { inner, .. }` at the MIR boundary.
                let mut ty = registry.get(base_ty)?;
                if let HirType::Pointer { inner, .. } = ty {
                    ty = registry.get(*inner)?;
                }
                match ty {
                    HirType::Struct { fields, .. } => fields.get(*field_index).map(|(_, fty)| *fty),
                    HirType::Tuple(elems) => elems.get(*field_index).copied(),
                    _ => None,
                }
            }
            HirExprKind::Index { receiver: base, .. } => {
                let base_ty = if self.type_registry.and_then(|r| r.get_type_name(base.ty)).is_some() {
                    Some(base.ty)
                } else {
                    self.recover_receiver_type(base)
                }?;
                let registry = self.type_registry?;
                let mut ty = registry.get(base_ty)?;
                if let HirType::Pointer { inner, .. } = ty {
                    ty = registry.get(*inner)?;
                }
                match ty {
                    HirType::Array { element, .. } => Some(*element),
                    HirType::Simd { element, .. } => Some(*element),
                    HirType::Pointer { inner, .. } => Some(*inner),
                    _ => None,
                }
            }
            // G5: `StructFoo { x: 1 }.method()` — the StructInit payload
            // already carries the target TypeId.
            HirExprKind::StructInit { ty, .. } => Some(*ty),
            // G1: `global_var.method()` — the Global expr's ty was resolved
            // from the globals table during HIR lowering; return it directly.
            HirExprKind::Global(_) => Some(expr.ty),
            // G7: `(&x).method()` — the Ref expr has type Pointer { inner: T };
            // strip one Pointer layer to recover T as the dispatch receiver type.
            HirExprKind::Ref(_inner) => {
                let registry = self.type_registry?;
                match registry.get(expr.ty)? {
                    HirType::Pointer { inner, .. } => Some(*inner),
                    _ => None,
                }
            }
            // G2: `(-x).method()` — unary ops preserve the operand's type;
            // recurse into the operand so the caller can dispatch correctly.
            HirExprKind::Unary { operand, .. } => self.recover_receiver_type(operand),
            // G9: `(x as Foo).method()` — the cast target is the receiver
            // type the dispatcher should qualify against.
            HirExprKind::Cast { target, .. } => Some(*target),
            // G8: `(*ptr).method()` — the inner expression has some
            // `Pointer { inner: T }` type; strip one Pointer layer and
            // return `T`. If the inner's own `ty` is unnamed, recurse so
            // chains like `(*(*pp)).init()` still resolve. Mirrors the
            // pointer-strip pattern used by FieldAccess / Index.
            HirExprKind::Deref(inner) => {
                let inner_ty = if self.type_registry.and_then(|r| r.get_type_name(inner.ty)).is_some() {
                    Some(inner.ty)
                } else {
                    self.recover_receiver_type(inner)
                }
                .unwrap_or(inner.ty);
                let registry = self.type_registry?;
                match registry.get(inner_ty)? {
                    HirType::Pointer { inner, .. } => Some(*inner),
                    _ => None,
                }
            }
            // G6: `(if c then a else b).method()` — both branches share the
            // same type by type-checking; recurse into `then_branch`.
            HirExprKind::If { then_branch, .. } => self.recover_receiver_type(then_branch),
            // G13: `(let x = v in expr).method()` — the expression type comes
            // from the body; recurse into it.
            HirExprKind::LetIn { body, .. } => self.recover_receiver_type(body),
            // G3: `f(x).method()` — the Call expr's `ty` is already set to the
            // function's return type by the HIR lowerer; return it directly.
            // If the return type is unnamed (Any), `get_type_name` will return
            // None at the call site and dispatch falls back gracefully.
            HirExprKind::Call { .. } => Some(expr.ty),
            // G4: `obj.a().b()` — the inner MethodCall expr's `ty` is the
            // return type of `.a()`; return it so `.b()` qualifies correctly.
            HirExprKind::MethodCall { .. } => Some(expr.ty),
            // G11: `future.await.method()` — the HIR lowerer sets expr.ty to
            // the unwrapped T (Future<T> → T); return it directly.
            HirExprKind::Await(_) => Some(expr.ty),
            // G12: `old(x).method()` — contract-spec construct; the inner
            // expression's type is preserved through the old() wrapper.
            HirExprKind::ContractOld(inner) => self.recover_receiver_type(inner),
            _ => None,
        }
    }

    pub(super) fn lower_expr(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
        let expr_ty = expr.ty;

        match &expr.kind {
            HirExprKind::Integer(n) => self.lower_integer_expr(*n),
            HirExprKind::Float(f) => self.lower_float_expr(*f),
            HirExprKind::Bool(b) => self.lower_bool_expr(*b),
            HirExprKind::String(s) => self.lower_string_expr(s.clone()),
            HirExprKind::Nil => self.lower_nil_expr(),
            HirExprKind::ContractResult => self.lower_contract_result_expr(),

            HirExprKind::Local(idx) => self.lower_local_expr(*idx, expr_ty),
            HirExprKind::Global(name) => self.lower_global_expr(name.clone(), expr_ty),

            HirExprKind::Binary { op, left, right } => self.lower_binary_expr(*op, left, right),
            HirExprKind::Unary { op, operand } => self.lower_unary_expr(*op, operand),
            HirExprKind::Cast { expr: inner, target } => self.lower_cast_expr(inner, *target),

            HirExprKind::Call { func: callee, args } => self.lower_call_expr(callee, args),
            HirExprKind::BuiltinCall { name, args } => self.lower_builtin_call_expr(name, args, expr_ty),
            HirExprKind::MethodCall {
                receiver,
                method,
                args,
                dispatch,
            } => self.lower_method_call_expr(receiver, method, args, dispatch),

            HirExprKind::Lambda {
                params: _params,
                body,
                captures,
            } => self.lower_lambda_expr(body, captures),
            HirExprKind::Yield(value) => self.lower_yield_expr(value),
            HirExprKind::GeneratorCreate { body } => self.lower_generator_create_expr(body),
            HirExprKind::FutureCreate { body } => self.lower_future_create_expr(body),
            HirExprKind::Await(future) => self.lower_await_expr(future),
            HirExprKind::ActorSpawn { body } => self.lower_actor_spawn_expr(body),

            HirExprKind::Tuple(elements) => self.lower_tuple_expr(elements),
            HirExprKind::Array(elements) => self.lower_array_expr(elements),
            HirExprKind::VecLiteral(elements) => self.lower_vec_literal_expr(elements),
            HirExprKind::Dict(pairs) => self.lower_dict_expr(pairs),
            HirExprKind::ArrayRepeat { value, count } => self.lower_array_repeat_expr(value, count),

            HirExprKind::StructInit { ty, fields } => self.lower_struct_init_expr(*ty, fields),
            HirExprKind::FieldAccess { receiver, field_index } => {
                self.lower_field_access_expr(receiver, *field_index, expr_ty)
            }
            HirExprKind::Index { receiver, index } => self.lower_index_expr(receiver, index, expr_ty),

            HirExprKind::PointerNew { kind, value } => self.lower_pointer_new_expr(*kind, value),
            HirExprKind::Ref(inner) => self.lower_ref_expr(inner),
            HirExprKind::Deref(inner) => self.lower_deref_expr(inner),
            HirExprKind::ContractOld(inner) => self.lower_contract_old_expr(inner),
            HirExprKind::NeighborAccess { array, direction } => self.lower_neighbor_access_expr(array, direction),
            HirExprKind::GpuIntrinsic { intrinsic, args } => self.lower_gpu_intrinsic(*intrinsic, args),

            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.lower_if_expr(condition, then_branch, else_branch, expr_ty),
            HirExprKind::LetIn { local_idx, value, body } => self.lower_let_in_expr(*local_idx, value, body),
        }
    }
}
