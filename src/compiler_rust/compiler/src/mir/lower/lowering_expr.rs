//! Expression lowering for MIR
//!
//! This module contains methods for lowering HIR expressions to MIR instructions,
//! including literals, variables, operators, function calls, lambdas, async/await,
//! actors, pointers, and collections.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{BinOp, DispatchMode, HirExpr, HirExprKind, HirType, PointerKind, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

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
    fn recover_receiver_type(&mut self, expr: &HirExpr) -> Option<TypeId> {
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
                let base_ty = if self
                    .type_registry
                    .and_then(|r| r.get_type_name(base.ty))
                    .is_some()
                {
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
                    HirType::Struct { fields, .. } => {
                        fields.get(*field_index).map(|(_, fty)| *fty)
                    }
                    HirType::Tuple(elems) => elems.get(*field_index).copied(),
                    _ => None,
                }
            }
            HirExprKind::Index {
                receiver: base,
                ..
            } => {
                let base_ty = if self
                    .type_registry
                    .and_then(|r| r.get_type_name(base.ty))
                    .is_some()
                {
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
                let inner_ty = if self
                    .type_registry
                    .and_then(|r| r.get_type_name(inner.ty))
                    .is_some()
                {
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
            HirExprKind::Integer(n) => {
                let n = *n;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest, value: n });
                    dest
                })
            }

            HirExprKind::Float(f) => {
                let f = *f;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstFloat { dest, value: f });
                    dest
                })
            }

            HirExprKind::Bool(b) => {
                let b = *b;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstBool { dest, value: b });
                    dest
                })
            }

            HirExprKind::String(s) => {
                let s = s.clone();
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstString { dest, value: s });
                    dest
                })
            }

            HirExprKind::Local(idx) => {
                let idx = *idx;
                let is_tagged_local = self.tagged_locals.contains(&idx);
                let result = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let addr_reg = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr_reg,
                        local_index: idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest,
                        addr: addr_reg,
                        ty: expr_ty,
                    });
                    dest
                })?;
                // Propagate tagged status from local to loaded VReg
                if is_tagged_local {
                    self.tagged_vregs.insert(result);
                }
                Ok(result)
            }

            HirExprKind::Binary { op, left, right } => {
                let op = *op;

                // For compound boolean expressions (And, Or), emit condition probes
                // to track each sub-condition for condition/MC-DC coverage (#674)
                if self.coverage_enabled && matches!(op, BinOp::And | BinOp::Or) {
                    // Create a decision ID for this compound expression
                    let decision_id = self.next_decision_id();

                    // Lower left operand and emit condition probe
                    let left_reg = self.lower_expr(left)?;
                    self.emit_condition_probe(decision_id, left_reg, 0, 0)?;

                    // Lower right operand and emit condition probe
                    let right_reg = self.lower_expr(right)?;
                    self.emit_condition_probe(decision_id, right_reg, 0, 0)?;

                    // Compute the final result
                    let dest = self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BinOp {
                            dest,
                            op,
                            left: left_reg,
                            right: right_reg,
                        });
                        dest
                    })?;

                    // Emit decision probe for the overall result
                    self.emit_decision_probe(dest, 0, 0)?;

                    Ok(dest)
                } else {
                    // Non-coverage path or non-boolean operations
                    let left_reg = self.lower_expr(left)?;
                    let right_reg = self.lower_expr(right)?;

                    // String concatenation: if either side is text/string and op is Add,
                    // emit rt_string_concat call instead of iadd
                    let is_string_add = op == BinOp::Add
                        && (left.ty == TypeId::STRING
                            || right.ty == TypeId::STRING
                            || left.ty == TypeId::ANY
                            || right.ty == TypeId::ANY);
                    if is_string_add {
                        // Convert non-string side to string via rt_to_string if needed
                        let left_str = if left.ty != TypeId::STRING && left.ty != TypeId::ANY {
                            self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(dest),
                                    target: crate::mir::CallTarget::from_name("rt_to_string"),
                                    args: vec![left_reg],
                                });
                                dest
                            })?
                        } else {
                            left_reg
                        };
                        let right_str = if right.ty != TypeId::STRING && right.ty != TypeId::ANY {
                            self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(dest),
                                    target: crate::mir::CallTarget::from_name("rt_to_string"),
                                    args: vec![right_reg],
                                });
                                dest
                            })?
                        } else {
                            right_reg
                        };
                        self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: Some(dest),
                                target: crate::mir::CallTarget::from_name("rt_string_concat"),
                                args: vec![left_str, right_str],
                            });
                            dest
                        })
                    } else {
                        self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::BinOp {
                                dest,
                                op,
                                left: left_reg,
                                right: right_reg,
                            });
                            dest
                        })
                    }
                }
            }

            HirExprKind::Unary { op, operand } => {
                let op = *op;
                let operand_reg = self.lower_expr(operand)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::UnaryOp {
                        dest,
                        op,
                        operand: operand_reg,
                    });
                    dest
                })
            }

            HirExprKind::Call { func: callee, args } => {
                let mut arg_regs = Vec::new();
                for arg in args {
                    arg_regs.push(self.lower_expr(arg)?);
                }

                // Direct call or indirect call?
                if let HirExprKind::Global(name) = &callee.kind {
                    // Check if this is an enum variant constructor (e.g., "Color::Blue" or "Color.Blue")
                    if let Some((enum_name, variant_name)) = name.split_once("::").or_else(|| name.split_once('.')) {
                        // Check if this is an enum type via the type registry or callee type
                        let is_enum = if let Some(registry) = self.type_registry {
                            if let Some(type_id) = registry.lookup(enum_name) {
                                matches!(registry.get(type_id), Some(crate::hir::HirType::Enum { .. }))
                            } else {
                                // Also check the callee's type - if it resolves to an enum
                                matches!(registry.get(callee.ty), Some(crate::hir::HirType::Enum { .. }))
                            }
                        } else {
                            false
                        };

                        if is_enum && !arg_regs.is_empty() {
                            // For single-arg variants, use the arg directly as payload
                            // For multi-arg variants, wrap args in an array as the payload
                            let payload_reg = if arg_regs.len() == 1 {
                                arg_regs[0]
                            } else {
                                // Create an array with all args as the payload
                                let array_reg = self.with_func(|func, current_block| {
                                    let dest = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::Call {
                                        dest: Some(dest),
                                        target: CallTarget::from_name("rt_array_new"),
                                        args: vec![],
                                    });
                                    dest
                                })?;
                                // Push each arg into the array
                                for arg in &arg_regs {
                                    self.with_func(|func, current_block| {
                                        let block = func.block_mut(current_block).unwrap();
                                        block.instructions.push(MirInst::Call {
                                            dest: None,
                                            target: CallTarget::from_name("rt_array_push"),
                                            args: vec![array_reg, *arg],
                                        });
                                    })?;
                                }
                                array_reg
                            };
                            return self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::EnumWith {
                                    dest,
                                    enum_name: enum_name.to_string(),
                                    variant_name: variant_name.to_string(),
                                    payload: payload_reg,
                                });
                                dest
                            });
                        }
                    }

                    // Direct call - DI injection is handled at the HIR level
                    // The function signature already includes all parameters (including @inject ones)
                    // So we don't inject at call sites during MIR lowering
                    // NOTE: DI injection at MIR level was causing signature mismatches
                    // because functions were registered with all params but calls tried to inject again

                    let call_target = CallTarget::from_name(name);
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: call_target,
                            args: arg_regs,
                        });
                        dest
                    })
                } else {
                    // Indirect call through closure/function pointer
                    let callee_reg = self.lower_expr(callee)?;
                    let callee_ty = callee.ty;

                    let (param_types, return_type) = if let Some(reg) = self.type_registry {
                        if let Some(HirType::Function { params, ret }) = reg.get(callee_ty) {
                            (params.clone(), *ret)
                        } else {
                            (vec![TypeId::ANY; arg_regs.len()], TypeId::ANY)
                        }
                    } else {
                        (vec![TypeId::ANY; arg_regs.len()], TypeId::ANY)
                    };

                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::IndirectCall {
                            dest: Some(dest),
                            callee: callee_reg,
                            param_types,
                            return_type,
                            args: arg_regs,
                            effect: crate::mir::effects::Effect::Io,
                        });
                        dest
                    })
                }
            }

            HirExprKind::Lambda {
                params: _params,
                body,
                captures,
            } => {
                // Save current block
                let original_block = self.with_func(|_, current_block| current_block)?;

                // Create body block and switch to it (like generators/futures)
                let body_block = self.with_func(|func, _| func.new_block())?;
                self.set_current_block(body_block)?;

                // Lower the lambda body INTO the body block
                let body_reg = self.lower_expr(body)?;

                // Add return terminator to body block
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = crate::mir::Terminator::Return(Some(body_reg));
                })?;

                // Switch back to original block
                self.set_current_block(original_block)?;

                // Each capture is 8 bytes (pointer-sized)
                let closure_size = 8 + (captures.len() as u32 * 8);
                let capture_offsets: Vec<u32> = (0..captures.len()).map(|i| 8 + (i as u32 * 8)).collect();
                let capture_types: Vec<TypeId> = captures.iter().map(|_| TypeId::I64).collect();

                // Load captured variables
                let mut capture_regs = Vec::new();
                for &local_idx in captures.iter() {
                    let reg = self.with_func(|func, current_block| {
                        let addr_reg = func.new_vreg();
                        let val_reg = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest: addr_reg,
                            local_index: local_idx,
                        });
                        block.instructions.push(MirInst::Load {
                            dest: val_reg,
                            addr: addr_reg,
                            ty: TypeId::I64,
                        });
                        val_reg
                    })?;
                    capture_regs.push(reg);
                }

                // Generate function name matching expand_with_outlined convention
                let parent_name = self
                    .try_contract_ctx()
                    .map(|ctx| ctx.func_name.clone())
                    .unwrap_or_else(|_| "anonymous".to_string());
                let func_name = format!("{}_outlined_{}", parent_name, body_block.0);

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ClosureCreate {
                        dest,
                        func_name,
                        closure_size,
                        capture_offsets,
                        capture_types,
                        captures: capture_regs,
                        body_block: Some(body_block),
                    });
                    dest
                })
            }

            HirExprKind::Yield(value) => {
                let value_reg = self.lower_expr(value)?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Yield { value: value_reg });
                    // Yield doesn't have a meaningful result, return the value register
                    value_reg
                })
            }

            HirExprKind::GeneratorCreate { body } => {
                // Save current block
                let original_block = self.with_func(|_, current_block| current_block)?;

                // Create body block and switch to it
                let body_block = self.with_func(|func, _| func.new_block())?;
                self.set_current_block(body_block)?;

                // Lower body expression INTO the body_block
                let body_reg = self.lower_expr(body)?;

                // Add return terminator to body_block
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = crate::mir::Terminator::Return(Some(body_reg));
                })?;

                // Switch back to original block
                self.set_current_block(original_block)?;

                // Emit GeneratorCreate in original block
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GeneratorCreate { dest, body_block });
                    dest
                })
            }

            HirExprKind::FutureCreate { body } => {
                // Save current block
                let original_block = self.with_func(|_, current_block| current_block)?;

                // Create body block and switch to it
                let body_block = self.with_func(|func, _| func.new_block())?;
                self.set_current_block(body_block)?;

                // Lower body expression INTO the body_block
                let body_reg = self.lower_expr(body)?;

                // Add return terminator to body_block
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = crate::mir::Terminator::Return(Some(body_reg));
                })?;

                // Switch back to original block
                self.set_current_block(original_block)?;

                // Emit FutureCreate in original block
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::FutureCreate { dest, body_block });
                    dest
                })
            }

            HirExprKind::Await(future) => {
                let future_reg = self.lower_expr(future)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Await {
                        dest,
                        future: future_reg,
                    });
                    dest
                })
            }

            HirExprKind::ActorSpawn { body } => {
                // Lower the body expression first
                let _body_reg = self.lower_expr(body)?;

                // Create a new block for the actor body
                let body_block = self.with_func(|func, _| func.new_block())?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ActorSpawn { dest, body_block });
                    dest
                })
            }

            HirExprKind::BuiltinCall { name, args } => {
                // Special handling for rt_enum_payload - returns tagged RuntimeValue
                // that needs unboxing when the payload type is a native type
                if name == "rt_enum_payload" && args.len() == 1 {
                    let arg_reg = self.lower_expr(&args[0])?;
                    let raw_result = self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: CallTarget::from_name("rt_enum_payload"),
                            args: vec![arg_reg],
                        });
                        dest
                    })?;

                    // rt_enum_payload returns a tagged RuntimeValue.
                    // Mark it as tagged so downstream Store/Load tracking can
                    // insert UnboxInt when storing to a concrete int-typed local.
                    self.tagged_vregs.insert(raw_result);

                    // If the expected type is known to be a native int/float, unbox now.
                    let needs_int_unbox = matches!(
                        expr.ty,
                        TypeId::I8
                            | TypeId::I16
                            | TypeId::I32
                            | TypeId::I64
                            | TypeId::U8
                            | TypeId::U16
                            | TypeId::U32
                            | TypeId::U64
                            | TypeId::BOOL
                    );
                    let needs_float_unbox = matches!(expr.ty, TypeId::F32 | TypeId::F64);

                    if needs_int_unbox {
                        return self.with_func(|func, current_block| {
                            let unboxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::UnboxInt {
                                dest: unboxed,
                                value: raw_result,
                            });
                            unboxed
                        });
                    } else if needs_float_unbox {
                        return self.with_func(|func, current_block| {
                            let unboxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::UnboxFloat {
                                dest: unboxed,
                                value: raw_result,
                            });
                            unboxed
                        });
                    } else {
                        // Strings, arrays, objects are already valid as RuntimeValue pointers
                        return Ok(raw_result);
                    }
                }

                // Special handling for join
                if name == "join" && args.len() == 1 {
                    let actor_reg = self.lower_expr(&args[0])?;
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ActorJoin { dest, actor: actor_reg });
                        dest
                    });
                }

                // Special handling for reply
                if name == "reply" && args.len() == 1 {
                    let message_reg = self.lower_expr(&args[0])?;
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ActorReply { message: message_reg });
                        // Reply returns nil (represented as 0)
                        block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                        dest
                    });
                }

                // Special handling for rt_value_to_string - box integers/floats
                if name == "rt_value_to_string" && args.len() == 1 {
                    let arg = &args[0];
                    let arg_reg = self.lower_expr(arg)?;

                    // Check if argument is a native integer or float type that needs boxing
                    let needs_boxing = matches!(
                        arg.ty,
                        TypeId::I8
                            | TypeId::I16
                            | TypeId::I32
                            | TypeId::I64
                            | TypeId::U8
                            | TypeId::U16
                            | TypeId::U32
                            | TypeId::U64
                    );
                    let needs_float_boxing = matches!(arg.ty, TypeId::F32 | TypeId::F64);
                    let needs_bool_boxing = arg.ty == TypeId::BOOL;

                    return self.with_func(|func, current_block| {
                        // Box the argument if it's a native type
                        let boxed_arg = if needs_bool_boxing {
                            // Bool needs special boxing via rt_value_bool to preserve true/false
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: Some(boxed),
                                target: CallTarget::from_name("rt_value_bool"),
                                args: vec![arg_reg],
                            });
                            boxed
                        } else if needs_boxing {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::BoxInt {
                                dest: boxed,
                                value: arg_reg,
                            });
                            boxed
                        } else if needs_float_boxing {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::BoxFloat {
                                dest: boxed,
                                value: arg_reg,
                            });
                            boxed
                        } else {
                            // Strings, arrays, etc. are already RuntimeValues
                            arg_reg
                        };

                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: CallTarget::from_name(name),
                            args: vec![boxed_arg],
                        });
                        dest
                    });
                }

                // Special handling for print/println/eprint/eprintln - box numeric args
                if matches!(
                    name.as_str(),
                    "print" | "println" | "eprint" | "eprintln" | "print_raw" | "eprint_raw" | "dprint"
                ) {
                    let mut boxed_arg_regs = Vec::new();
                    for arg in args {
                        let arg_reg = self.lower_expr(arg)?;
                        let needs_int_boxing = matches!(
                            arg.ty,
                            TypeId::I16
                                | TypeId::I32
                                | TypeId::I64
                                | TypeId::U8
                                | TypeId::U16
                                | TypeId::U32
                                | TypeId::U64
                        );
                        let needs_float_boxing = matches!(arg.ty, TypeId::F32 | TypeId::F64);
                        let needs_bool_boxing = arg.ty == TypeId::BOOL || arg.ty == TypeId::I8;
                        if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                            let boxed = if needs_bool_boxing {
                                // Use rt_value_bool for bool → RuntimeValue conversion
                                self.with_func(|func, current_block| {
                                    let boxed = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::Call {
                                        dest: Some(boxed),
                                        target: CallTarget::from_name("rt_value_bool"),
                                        args: vec![arg_reg],
                                    });
                                    boxed
                                })?
                            } else {
                                self.with_func(|func, current_block| {
                                    let boxed = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    if needs_int_boxing {
                                        block.instructions.push(MirInst::BoxInt {
                                            dest: boxed,
                                            value: arg_reg,
                                        });
                                    } else {
                                        block.instructions.push(MirInst::BoxFloat {
                                            dest: boxed,
                                            value: arg_reg,
                                        });
                                    }
                                    boxed
                                })?
                            };
                            boxed_arg_regs.push(boxed);
                        } else {
                            boxed_arg_regs.push(arg_reg);
                        }
                    }
                    let target = CallTarget::from_name(name);
                    return self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target,
                            args: boxed_arg_regs,
                        });
                        dest
                    });
                }

                // Lower all arguments
                let mut arg_regs = Vec::new();
                for arg in args {
                    arg_regs.push(self.lower_expr(arg)?);
                }

                // Create a call to the builtin function
                let target = CallTarget::from_name(name);
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target,
                        args: arg_regs,
                    });
                    dest
                })
            }

            // Contract expressions (Design by Contract)
            HirExprKind::ContractResult => {
                // Return the stored return value from contract context
                let return_value = self.try_contract_ctx()?.return_value;
                if let Some(vreg) = return_value {
                    Ok(vreg)
                } else {
                    // If no return value is set, create a dummy value (shouldn't happen in valid code)
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                        dest
                    })
                }
            }

            HirExprKind::ContractOld(inner) => {
                // Look up the captured VReg for this old() expression
                // During emit_entry_contracts(), we stored: index -> (VReg, HirExpr)
                // Now we need to find which index corresponds to this inner expression

                let ctx = self.try_contract_ctx()?;

                // Search through old_expr_map to find matching expression
                for (idx, captured_expr) in &ctx.old_expr_map {
                    if captured_expr == inner.as_ref() {
                        // Found matching expression, return the captured VReg
                        if let Some(&vreg) = ctx.old_captures.get(idx) {
                            return Ok(vreg);
                        }
                    }
                }

                // If we reach here, the old() expression wasn't found in captures
                // This shouldn't happen with proper HIR lowering
                Err(MirLowerError::Unsupported(format!(
                    "old() expression not found in captures: {:?}",
                    inner
                )))
            }

            // Pointer operations
            HirExprKind::PointerNew { kind, value } => {
                let kind = *kind;
                let value_reg = self.lower_expr(value)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::PointerNew {
                        dest,
                        kind,
                        value: value_reg,
                    });
                    dest
                })
            }

            HirExprKind::Ref(inner) => {
                let source_reg = self.lower_expr(inner)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::PointerRef {
                        dest,
                        kind: PointerKind::Borrow,
                        source: source_reg,
                    });
                    dest
                })
            }

            HirExprKind::Deref(inner) => {
                let pointer_reg = self.lower_expr(inner)?;
                // Determine pointer kind from the inner expression's type
                // For now, default to Borrow
                let kind = PointerKind::Borrow;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::PointerDeref {
                        dest,
                        pointer: pointer_reg,
                        kind,
                    });
                    dest
                })
            }

            HirExprKind::GpuIntrinsic { intrinsic, args } => self.lower_gpu_intrinsic(*intrinsic, args),

            HirExprKind::NeighborAccess { array, direction } => {
                let array_reg = self.lower_expr(array)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::NeighborLoad {
                        dest,
                        array: array_reg,
                        direction: *direction,
                    });
                    dest
                })
            }

            HirExprKind::Tuple(elements) => {
                let mut elem_regs = Vec::new();
                for elem in elements {
                    let reg = self.lower_expr(elem)?;
                    // Box native-typed elements so they become RuntimeValues for the tuple
                    let needs_int_boxing = matches!(
                        elem.ty,
                        TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
                    );
                    let needs_float_boxing = matches!(elem.ty, TypeId::F32 | TypeId::F64);
                    let needs_bool_boxing = elem.ty == TypeId::BOOL || elem.ty == TypeId::I8;
                    if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                        let boxed = if needs_bool_boxing {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(boxed),
                                    target: CallTarget::from_name("rt_value_bool"),
                                    args: vec![reg],
                                });
                                boxed
                            })?
                        } else if needs_float_boxing {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::BoxFloat {
                                    dest: boxed,
                                    value: reg,
                                });
                                boxed
                            })?
                        } else {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::BoxInt {
                                    dest: boxed,
                                    value: reg,
                                });
                                boxed
                            })?
                        };
                        elem_regs.push(boxed);
                    } else {
                        elem_regs.push(reg);
                    }
                }
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::TupleLit {
                        dest,
                        elements: elem_regs,
                    });
                    dest
                })
            }

            HirExprKind::Array(elements) => {
                let mut elem_regs = Vec::new();
                for elem in elements {
                    let reg = self.lower_expr(elem)?;
                    // Box native-typed elements so they become RuntimeValues for the array
                    let needs_int_boxing = matches!(
                        elem.ty,
                        TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
                    );
                    let needs_float_boxing = matches!(elem.ty, TypeId::F32 | TypeId::F64);
                    let needs_bool_boxing = elem.ty == TypeId::BOOL || elem.ty == TypeId::I8;
                    if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                        let boxed = if needs_bool_boxing {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(boxed),
                                    target: CallTarget::from_name("rt_value_bool"),
                                    args: vec![reg],
                                });
                                boxed
                            })?
                        } else if needs_float_boxing {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::BoxFloat {
                                    dest: boxed,
                                    value: reg,
                                });
                                boxed
                            })?
                        } else {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::BoxInt {
                                    dest: boxed,
                                    value: reg,
                                });
                                boxed
                            })?
                        };
                        elem_regs.push(boxed);
                    } else {
                        // Strings, objects, etc. are already RuntimeValues
                        elem_regs.push(reg);
                    }
                }
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ArrayLit {
                        dest,
                        elements: elem_regs,
                    });
                    dest
                })
            }

            HirExprKind::VecLiteral(elements) => {
                let mut elem_regs = Vec::new();
                for elem in elements {
                    elem_regs.push(self.lower_expr(elem)?);
                }
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecLit {
                        dest,
                        elements: elem_regs,
                    });
                    dest
                })
            }

            HirExprKind::StructInit { ty, fields } => {
                // Lower field expressions first
                let mut field_regs = Vec::new();
                for field in fields {
                    field_regs.push(self.lower_expr(field)?);
                }

                // For builtin type "constructors" (str, int), box integer-typed
                // fields as RuntimeValues so the codegen receives tagged values.
                if (*ty == TypeId::STRING || *ty == TypeId::ANY) && field_regs.len() == 1 {
                    let field_ty = fields[0].ty;
                    let needs_boxing = field_ty == TypeId::I64
                        || field_ty == TypeId::I32
                        || field_ty == TypeId::I8
                        || field_ty == TypeId::BOOL;
                    if needs_boxing {
                        let reg = field_regs[0];
                        let boxed = self.with_func(|func, current_block| {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::BoxInt {
                                dest: boxed,
                                value: reg,
                            });
                            boxed
                        })?;
                        field_regs[0] = boxed;
                    }
                }

                // Check if this type has an @inject constructor (ClassName.new)
                // If so, we need to call the constructor with DI injection
                let type_name = self
                    .type_registry
                    .and_then(|registry| registry.get_type_name(*ty))
                    .map(|s| s.to_string());

                if let Some(ref class_name) = type_name {
                    let constructor_name = format!("{}.new", class_name);
                    if let Some(param_info) = self.inject_functions.get(&constructor_name).cloned() {
                        // This type has an @inject constructor
                        // But we should only apply DI injection for EXTERNAL calls, not internal
                        // constructions like `return Self {}` inside the constructor body itself.
                        //
                        // Check if we're inside the constructor for this class. If so, skip DI.
                        let current_func = self
                            .try_contract_ctx()
                            .map(|ctx| ctx.func_name.clone())
                            .unwrap_or_default();
                        let is_inside_constructor = current_func == constructor_name;

                        // Also check if the field count matches the non-injectable param count.
                        // This distinguishes:
                        // - Service(42) in main: 1 field, 1 non-injectable param → apply DI
                        // - Service() in main: 0 fields, 1 non-injectable param → apply DI (will error)
                        // - return Self {} in Service.new: inside constructor → skip DI
                        if !is_inside_constructor {
                            // External constructor call - apply DI injection
                            let mut final_args = Vec::new();
                            let mut provided_idx = 0;

                            for (param_idx, (param_ty, is_injectable)) in param_info.iter().enumerate() {
                                if *is_injectable {
                                    // This parameter should be DI-injected
                                    if self.di_config.is_none() {
                                        return Err(MirLowerError::Unsupported(format!(
                                            "missing DI config for @inject constructor '{}'",
                                            constructor_name
                                        )));
                                    }
                                    let injected = self.resolve_di_arg(*param_ty, &constructor_name, param_idx)?;
                                    final_args.push(injected);
                                } else {
                                    // This parameter should be provided by caller
                                    if provided_idx >= field_regs.len() {
                                        return Err(MirLowerError::Unsupported(format!(
                                            "missing argument at position {} for @inject constructor '{}'",
                                            provided_idx, constructor_name
                                        )));
                                    }
                                    final_args.push(field_regs[provided_idx]);
                                    provided_idx += 1;
                                }
                            }

                            // Generate call to the @inject constructor
                            return self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(dest),
                                    target: CallTarget::from_name(&constructor_name),
                                    args: final_args,
                                });
                                dest
                            });
                        }
                        // else: is_internal_construction - fall through to regular StructInit
                    }
                }

                // No @inject constructor - regular struct initialization
                // Get struct type information from type registry
                let (field_types, field_offsets, struct_size) = if let Some(registry) = self.type_registry {
                    if let Some(HirType::Struct {
                        fields: struct_fields, ..
                    }) = registry.get(*ty)
                    {
                        let field_types: Vec<TypeId> = struct_fields.iter().map(|(_, ty)| *ty).collect();
                        // For now, use simple sequential layout (simplified, may not match actual layout)
                        let mut offsets = Vec::new();
                        let mut offset = 0u32;
                        for (_, field_ty) in struct_fields {
                            offsets.push(offset);
                            // Assume 8-byte fields for simplicity (pointer-sized)
                            offset += 8;
                        }
                        (field_types, offsets, offset)
                    } else {
                        // Fallback: derive layout from field count (8 bytes per field)
                        let n = field_regs.len();
                        let field_types: Vec<TypeId> = (0..n).map(|_| TypeId::ANY).collect();
                        let field_offsets: Vec<u32> = (0..n).map(|i| (i * 8) as u32).collect();
                        (field_types, field_offsets, (n * 8) as u32)
                    }
                } else {
                    // No type registry - derive layout from field count (8 bytes per field)
                    let n = field_regs.len();
                    let field_types: Vec<TypeId> = (0..n).map(|_| TypeId::ANY).collect();
                    let field_offsets: Vec<u32> = (0..n).map(|i| (i * 8) as u32).collect();
                    (field_types, field_offsets, (n * 8) as u32)
                };

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::StructInit {
                        dest,
                        type_id: *ty,
                        struct_size,
                        field_offsets,
                        field_types,
                        field_values: field_regs,
                    });
                    dest
                })
            }

            // Type cast expression
            HirExprKind::Cast { expr, target } => {
                let source_reg = self.lower_expr(expr)?;
                let target_ty = *target;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Cast {
                        dest,
                        source: source_reg,
                        from_ty: expr.ty,
                        to_ty: target_ty,
                    });
                    dest
                })
            }

            // Field access expression: obj.field
            HirExprKind::FieldAccess { receiver, field_index } => {
                let receiver_reg = self.lower_expr(receiver)?;
                let field_index = *field_index;
                let receiver_ty = receiver.ty;

                // Check if the receiver is a tuple type — tuples are opaque runtime
                // objects accessed via rt_tuple_get, not flat structs.
                let is_tuple = self
                    .type_registry
                    .and_then(|tr| tr.get(receiver_ty))
                    .is_some_and(|t| matches!(t, HirType::Tuple(_)));

                if is_tuple {
                    // Emit: index_reg = ConstInt(field_index)
                    //        dest     = Call rt_tuple_get(receiver_reg, index_reg)
                    let index_reg = self.with_func(|func, current_block| {
                        let idx = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ConstInt {
                            dest: idx,
                            value: field_index as i64,
                        });
                        idx
                    })?;

                    let target = CallTarget::from_name("rt_tuple_get");
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target,
                            args: vec![receiver_reg, index_reg],
                        });
                        dest
                    })
                } else {
                    // Struct field access — direct memory load at byte offset
                    let byte_offset = (field_index as u32) * 8;

                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::FieldGet {
                            dest,
                            object: receiver_reg,
                            byte_offset,
                            field_type: expr_ty,
                        });
                        dest
                    })
                }
            }

            // Index expression: array[index] or string[index]
            HirExprKind::Index { receiver, index } => {
                let receiver_reg = self.lower_expr(receiver)?;
                let index_reg = self.lower_expr(index)?;
                let receiver_ty = receiver.ty;

                // Check if the receiver is a tuple type
                let is_tuple = self
                    .type_registry
                    .and_then(|tr| tr.get(receiver_ty))
                    .is_some_and(|t| matches!(t, crate::hir::HirType::Tuple(_)));

                let raw_result = if is_tuple {
                    // Use rt_tuple_get(tuple_rv, index_u64) for tuples
                    let target = CallTarget::from_name("rt_tuple_get");
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target,
                            args: vec![receiver_reg, index_reg],
                        });
                        dest
                    })?
                } else {
                    // Box the index as RuntimeValue if it's a native type
                    let boxed_index = {
                        let needs_int_boxing = matches!(
                            index.ty,
                            TypeId::I16
                                | TypeId::I32
                                | TypeId::I64
                                | TypeId::U8
                                | TypeId::U16
                                | TypeId::U32
                                | TypeId::U64
                        );
                        let needs_bool_boxing = index.ty == TypeId::BOOL || index.ty == TypeId::I8;
                        if needs_int_boxing {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::BoxInt {
                                    dest: boxed,
                                    value: index_reg,
                                });
                                boxed
                            })?
                        } else if needs_bool_boxing {
                            self.with_func(|func, current_block| {
                                let boxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(boxed),
                                    target: CallTarget::from_name("rt_value_bool"),
                                    args: vec![index_reg],
                                });
                                boxed
                            })?
                        } else {
                            // String keys etc. are already RuntimeValues
                            index_reg
                        }
                    };
                    // Use rt_index_get(collection_rv, index_rv) for arrays/strings/dicts
                    let target = CallTarget::from_name("rt_index_get");
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target,
                            args: vec![receiver_reg, boxed_index],
                        });
                        dest
                    })?
                };

                // rt_array_get returns RuntimeValue; unbox if the expected type is a native type
                let needs_int_unbox = matches!(
                    expr.ty,
                    TypeId::I8
                        | TypeId::I16
                        | TypeId::I32
                        | TypeId::I64
                        | TypeId::U8
                        | TypeId::U16
                        | TypeId::U32
                        | TypeId::U64
                        | TypeId::BOOL
                );
                let needs_float_unbox = matches!(expr.ty, TypeId::F32 | TypeId::F64);

                if needs_int_unbox {
                    self.with_func(|func, current_block| {
                        let unboxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::UnboxInt {
                            dest: unboxed,
                            value: raw_result,
                        });
                        unboxed
                    })
                } else if needs_float_unbox {
                    self.with_func(|func, current_block| {
                        let unboxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::UnboxFloat {
                            dest: unboxed,
                            value: raw_result,
                        });
                        unboxed
                    })
                } else {
                    // Strings, arrays, objects are already usable as pointers
                    Ok(raw_result)
                }
            }

            // Method call with dispatch mode (static vs dynamic)
            HirExprKind::MethodCall {
                receiver,
                method,
                args,
                dispatch,
            } => {
                // rt_array_push returns bool, not a new pointer — no store-back needed.
                let _receiver_local_index: Option<usize> = None;

                let receiver_reg = self.lower_expr(receiver)?;
                let mut arg_regs = Vec::new();
                for arg in args {
                    arg_regs.push(self.lower_expr(arg)?);
                }

                // Box integer arguments for array .push() — matches IndexGet unbox at line 1236.
                // Without this, wrap_value (no-op) passes raw integers to rt_array_push,
                // but IndexGet + MIR UnboxInt expects tagged (val << 3) values.
                if method == "push" && !args.is_empty() {
                    let push_arg_ty = args[0].ty;
                    let needs_push_boxing = matches!(
                        push_arg_ty,
                        TypeId::I8
                            | TypeId::I16
                            | TypeId::I32
                            | TypeId::I64
                            | TypeId::U8
                            | TypeId::U16
                            | TypeId::U32
                            | TypeId::U64
                            | TypeId::BOOL
                    );
                    if needs_push_boxing {
                        let raw_arg = arg_regs[0];
                        let boxed_arg = self.with_func(|func, current_block| {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::BoxInt {
                                dest: boxed,
                                value: raw_arg,
                            });
                            boxed
                        })?;
                        arg_regs[0] = boxed_arg;
                    }
                }

                // Try to qualify method name with receiver type (e.g., "TreeSitter.expect")
                // When `receiver.ty` is `Any` (which happens for cross-module
                // `var x = Imported.new()` where type inference cannot reach
                // into the imported constructor), `get_type_name` returns
                // None and the func_name falls through to the bare method
                // name. The native-build codegen then picks the shortest
                // `.<method>` symbol in the whole module — a silent miscall
                // that caused `shell.init()` to dispatch to `Ps2Keyboard.init`
                // on the x86_64 baremetal desktop lane (see Agent V's
                // 2026-04-13 workaround). Set SIMPLE_DEBUG_METHOD_DISPATCH=1
                // to dump these bare-name dispatches at compile time.
                //
                // Round-16 fix (sys-gui-006 Blocker 2): when the expression's
                // own `receiver.ty` cannot be named, fall back to the type
                // recorded on the corresponding `MirFunction.locals[idx]`
                // when the receiver is `HirExprKind::Local(idx)`. This is
                // exactly the user-supplied `var shell: DesktopShell = ...`
                // annotation — copied into the MIR local table by the
                // statement lowerer — and survives even when constructor
                // return-type inference falls through to `Any`. Without
                // this fallback the typed-receiver workaround at
                // `desktop_e2e_entry.spl:97` was being silently undone for
                // the very call site (`shell.init()`) it was meant to fix.
                //
                // Round-17 widening (T58 follow-up): non-Local receivers —
                // `self.widget.init()`, `container.pair.0.init()`,
                // `arr[i].init()` — would still mis-dispatch because their
                // `receiver.ty` is likewise Unknown/Any in the same
                // cross-module constructor scenarios. Recover the type by
                // walking one structural hop into the sub-expression: look
                // up the field's type on the struct type of the base, the
                // tuple element type at the given index, or the array/vec
                // element type. Each hop uses only registered type info
                // from `TypeRegistry` — no synthesis — and the recursion
                // terminates at a Local (or an expression whose own `ty`
                // is already named).
                let receiver_local_ty: Option<TypeId> =
                    self.recover_receiver_type(receiver);

                let func_name = if let Some(registry) = self.type_registry {
                    if let Some(type_name) = registry.get_type_name(receiver.ty) {
                        format!("{}.{}", type_name, method)
                    } else if let Some(local_ty) = receiver_local_ty {
                        if let Some(type_name) = registry.get_type_name(local_ty) {
                            if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                                eprintln!(
                                    "[MIR-METHOD-DISPATCH] '{}' qualified via local-table type '{}' (receiver.ty was unnamed)",
                                    method, type_name
                                );
                            }
                            format!("{}.{}", type_name, method)
                        } else {
                            if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                                let ty_desc = registry
                                    .get(receiver.ty)
                                    .map(|t| format!("{:?}", t))
                                    .unwrap_or_else(|| format!("<missing tid={:?}>", receiver.ty));
                                eprintln!(
                                    "[MIR-METHOD-DISPATCH] bare '{}' call: receiver ty = {} (local-table fallback also unnamed)",
                                    method, ty_desc
                                );
                            }
                            method.clone()
                        }
                    } else {
                        if std::env::var("SIMPLE_DEBUG_METHOD_DISPATCH").is_ok() {
                            let ty_desc = registry
                                .get(receiver.ty)
                                .map(|t| format!("{:?}", t))
                                .unwrap_or_else(|| format!("<missing tid={:?}>", receiver.ty));
                            eprintln!(
                                "[MIR-METHOD-DISPATCH] bare '{}' call: receiver ty = {}",
                                method, ty_desc
                            );
                        }
                        method.clone()
                    }
                } else {
                    method.clone()
                };

                let _receiver_ty = receiver.ty;
                match dispatch {
                    DispatchMode::Dynamic => {
                        // Try to find the method in a registered trait (vtable dispatch)
                        if let Some((vtable_slot, param_types, return_type)) =
                            self.find_trait_for_method(&method)
                        {
                            let dest = self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::MethodCallVirtual {
                                    dest: Some(dest),
                                    receiver: receiver_reg,
                                    vtable_slot,
                                    param_types,
                                    return_type,
                                    args: arg_regs,
                                });
                                dest
                            })?;
                            Ok(dest)
                        } else {
                            // Fallback: not a registered trait method — use static dispatch
                            let dest = self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::MethodCallStatic {
                                    dest: Some(dest),
                                    receiver: receiver_reg,
                                    func_name,
                                    args: arg_regs,
                                });
                                dest
                            })?;

                            // NOTE: Do NOT store the push result back to the receiver
                            // variable. rt_array_push returns bool (success/failure),
                            // NOT a new array pointer. Storing the bool back would
                            // overwrite the array pointer with 1 (true), causing
                            // crashes on subsequent array access.
                            // The array is mutated in-place; the pointer stays valid.

                            Ok(dest)
                        }
                    }
                    DispatchMode::Static => {
                        let dest = self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::MethodCallStatic {
                                dest: Some(dest),
                                receiver: receiver_reg,
                                func_name,
                                args: arg_regs,
                            });
                            dest
                        })?;

                        // NOTE: Do NOT store the push result back to the receiver
                        // variable. rt_array_push returns bool (success/failure),
                        // NOT a new array pointer. Storing the bool back would
                        // overwrite the array pointer with 1 (true), causing
                        // crashes on subsequent array access.
                        // The array is mutated in-place; the pointer stays valid.

                        Ok(dest)
                    }
                }
            }

            // Global enum variant or global variable
            HirExprKind::Global(name) => {
                // Check if this is an enum variant (contains :: or .)
                if let Some((enum_name, variant)) = name.split_once("::").or_else(|| name.split_once('.')) {
                    // Look up the enum type to verify the variant exists
                    let variant_exists = if let Some(registry) = self.type_registry {
                        // Try looking up by enum_name first
                        let by_name = if let Some(enum_type_id) = registry.lookup(enum_name) {
                            matches!(registry.get(enum_type_id), Some(HirType::Enum { .. }))
                        } else {
                            false
                        };
                        // Also check the expression's type
                        let by_expr_ty = matches!(registry.get(expr_ty), Some(HirType::Enum { .. }));
                        by_name || by_expr_ty
                    } else {
                        false
                    };

                    if variant_exists {
                        // Emit EnumUnit instruction for proper RuntimeEnum creation
                        return self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::EnumUnit {
                                dest,
                                enum_name: enum_name.to_string(),
                                variant_name: variant.to_string(),
                            });
                            dest
                        });
                    }

                    if name.contains("::") {
                        // Enum variant with :: separator not found — genuine error
                        return Err(MirLowerError::Unsupported(format!("unknown enum variant: {}", name)));
                    }
                    // Dot-separated name that's not an enum — static method reference
                    // (e.g. Point.origin). Fall through to GlobalLoad below.
                }

                // Regular global variable - load via GlobalLoad instruction
                let name = name.clone();
                let ty = expr_ty; // Use the expression's type
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GlobalLoad {
                        dest,
                        global_name: name,
                        ty,
                    });
                    dest
                })
            }

            // Dictionary literal
            HirExprKind::Dict(pairs) => {
                // Create an empty dict and insert pairs
                // Dict is represented as a runtime value (i64 pointer)
                let pairs_count = pairs.len();

                // Emit call to create empty dict with capacity
                let capacity = std::cmp::max(8, pairs_count * 2) as i64;
                let capacity_reg = self.with_func(|func, current_block| {
                    let reg = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt {
                        dest: reg,
                        value: capacity,
                    });
                    reg
                })?;

                let dict_target = CallTarget::from_name("rt_dict_new");
                let dict_reg = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: dict_target,
                        args: vec![capacity_reg],
                    });
                    dest
                })?;

                // Insert each pair
                for (key_expr, value_expr) in pairs {
                    let key_reg = self.lower_expr(key_expr)?;
                    let value_reg = self.lower_expr(value_expr)?;
                    let insert_target = CallTarget::from_name("rt_dict_insert");
                    self.with_func(|func, current_block| {
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: None,
                            target: insert_target,
                            args: vec![dict_reg, key_reg, value_reg],
                        });
                    })?;
                }

                Ok(dict_reg)
            }

            HirExprKind::Nil => {
                // Nil is tagged value 3 in the runtime (TAG_SPECIAL=0b011 | SPECIAL_NIL=0).
                // Must match the runtime's RuntimeValue::NIL representation.
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest, value: 3 });
                    dest
                })
            }

            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                use crate::hir::TypeId;
                use crate::mir::effects::LocalKind;
                use crate::mir::function::MirLocal;

                // Lower condition
                let cond_reg = self.lower_expr(condition)?;

                // Create temporary local for result BEFORE branching
                let temp_local_index = self.with_func(|func, _| {
                    let index = func.params.len() + func.locals.len();
                    func.locals.push(MirLocal {
                        name: format!("$if_merge_{}", index),
                        ty: expr_ty,
                        kind: LocalKind::Local,
                        is_ghost: false,
                    });
                    index
                })?;

                // Get address of temp local
                let temp_addr = self.with_func(|func, current_block| {
                    let addr = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: temp_local_index,
                    });
                    addr
                })?;

                // Create basic blocks
                let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
                    let then_id = func.new_block();
                    let else_id = func.new_block();
                    let merge_id = func.new_block();

                    // Set branch terminator
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = crate::mir::Terminator::Branch {
                        cond: cond_reg,
                        then_block: then_id,
                        else_block: else_id,
                    };
                    (then_id, else_id, merge_id)
                })?;

                // Lower then branch
                self.set_current_block(then_id)?;
                let then_value = self.lower_expr(then_branch)?;
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Store {
                        addr: temp_addr,
                        value: then_value,
                        ty: expr_ty,
                    });
                })?;
                self.finalize_block_jump(merge_id)?;

                // Lower else branch
                self.set_current_block(else_id)?;
                let else_value = if let Some(else_expr) = else_branch {
                    self.lower_expr(else_expr)?
                } else {
                    // No else branch - use nil (0)
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                        dest
                    })?
                };
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Store {
                        addr: temp_addr,
                        value: else_value,
                        ty: expr_ty,
                    });
                })?;
                self.finalize_block_jump(merge_id)?;

                // Load merged value in merge block
                self.set_current_block(merge_id)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Load {
                        dest,
                        addr: temp_addr,
                        ty: expr_ty,
                    });
                    dest
                })
            }

            HirExprKind::LetIn { local_idx, value, body } => {
                // Store the value into the local variable, then evaluate body
                let val_reg = self.lower_expr(value)?;
                let value_ty = value.ty;
                self.with_func(|func, current_block| {
                    let addr = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: *local_idx,
                    });
                    block.instructions.push(MirInst::Store {
                        addr,
                        value: val_reg,
                        ty: value_ty,
                    });
                })?;
                self.lower_expr(body)
            }

            HirExprKind::ArrayRepeat { value, count } => {
                // Array repeat: [value; count] - creates array with count copies of value
                // Lower to runtime call: rt_array_repeat(value, count)
                let value_reg = self.lower_expr(value)?;
                let count_reg = self.lower_expr(count)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_array_repeat"),
                        args: vec![value_reg, count_reg],
                    });
                    dest
                })
            }
        }
    }
}
