//! Expression lowering for MIR
//!
//! This module contains methods for lowering HIR expressions to MIR instructions,
//! including literals, variables, operators, function calls, lambdas, async/await,
//! actors, pointers, and collections.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{DispatchMode, HirExpr, HirExprKind, HirType, PointerKind, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_expr(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
        let expr_ty = expr.ty;
        let expr_kind = expr.kind.clone();

        match &expr_kind {
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
                self.with_func(|func, current_block| {
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
                })
            }

            HirExprKind::Binary { op, left, right } => {
                let op = *op;
                let left_reg = self.lower_expr(left)?;
                let right_reg = self.lower_expr(right)?;

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

                // Get function name and create CallTarget with effect information
                let call_target = if let HirExprKind::Global(name) = &callee.kind {
                    if let Some(param_info) = self.inject_functions.get(name).cloned() {
                        // Per-parameter injection (#1013)
                        // Build final arg list by injecting params marked as injectable
                        let mut final_args = Vec::new();
                        let mut provided_idx = 0;

                        for (param_idx, (param_ty, is_injectable)) in param_info.iter().enumerate() {
                            if *is_injectable {
                                // This parameter should be DI-injected
                                if self.di_config.is_none() {
                                    return Err(MirLowerError::Unsupported(format!(
                                        "missing di config for injected call to '{}'",
                                        name
                                    )));
                                }
                                let injected = self.resolve_di_arg(*param_ty, name, param_idx)?;
                                final_args.push(injected);
                            } else {
                                // This parameter should be provided by caller
                                if provided_idx >= arg_regs.len() {
                                    return Err(MirLowerError::Unsupported(format!(
                                        "missing argument at position {} for call to '{}'",
                                        provided_idx, name
                                    )));
                                }
                                final_args.push(arg_regs[provided_idx]);
                                provided_idx += 1;
                            }
                        }

                        // Replace arg_regs with final_args
                        arg_regs = final_args;
                    }
                    CallTarget::from_name(name)
                } else {
                    return Err(MirLowerError::Unsupported("indirect call".to_string()));
                };

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
            }

            HirExprKind::Lambda {
                params: _params,
                body,
                captures,
            } => {
                // Lower the lambda body to get the result vreg
                let body_reg = self.lower_expr(body)?;

                // For now, create a simple closure with captures
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

                // Generate a unique function name for the lambda body
                let func_name = format!("__lambda_{}", body_reg.0);

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
                // Lower the body expression first to get any setup
                let _body_reg = self.lower_expr(body)?;

                // Create a new block for the generator body
                let body_block = self.with_func(|func, _| func.new_block())?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GeneratorCreate { dest, body_block });
                    dest
                })
            }

            HirExprKind::FutureCreate { body } => {
                // Lower the body expression first
                let _body_reg = self.lower_expr(body)?;

                // Create a new block for the future body
                let body_block = self.with_func(|func, _| func.new_block())?;

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
                    elem_regs.push(self.lower_expr(elem)?);
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
                    elem_regs.push(self.lower_expr(elem)?);
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
                // Lower field expressions
                let mut field_regs = Vec::new();
                for field in fields {
                    field_regs.push(self.lower_expr(field)?);
                }

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
                        // Fallback: use empty struct
                        (Vec::new(), Vec::new(), 0u32)
                    }
                } else {
                    // No type registry, use empty struct
                    (Vec::new(), Vec::new(), 0u32)
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

            // Method call with dispatch mode (static vs dynamic)
            HirExprKind::MethodCall {
                receiver,
                method,
                args,
                dispatch,
            } => {
                let receiver_reg = self.lower_expr(receiver)?;
                let mut arg_regs = Vec::new();
                for arg in args {
                    arg_regs.push(self.lower_expr(arg)?);
                }

                match dispatch {
                    DispatchMode::Static => {
                        // Static dispatch: direct function call (monomorphized)
                        // The method name should be fully qualified as Type::method
                        let func_name = method.clone();
                        self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::MethodCallStatic {
                                dest: Some(dest),
                                receiver: receiver_reg,
                                func_name,
                                args: arg_regs,
                            });
                            dest
                        })
                    }
                    DispatchMode::Dynamic => {
                        // Dynamic dispatch: vtable lookup at runtime
                        // Try to resolve vtable slot from trait info
                        let receiver_type = receiver.ty;

                        // Try to get trait name from receiver type
                        let trait_name = self
                            .type_registry
                            .and_then(|reg| reg.get_type_name(receiver_type))
                            .map(|s| s.to_string());

                        // Resolve vtable slot and param types from trait info
                        let (vtable_slot, param_types) = if let Some(ref tname) = trait_name {
                            let slot = self.get_vtable_slot(tname, method).unwrap_or(0);
                            let params = self
                                .get_trait_method_signature(tname, method)
                                .map(|(p, _)| p)
                                .unwrap_or_default();
                            (slot, params)
                        } else {
                            // Fallback: slot 0, no param types
                            (0, vec![])
                        };

                        let return_type = expr_ty;
                        self.with_func(|func, current_block| {
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
                        })
                    }
                }
            }

            _ => Err(MirLowerError::Unsupported(format!("{:?}", expr_kind))),
        }
    }
}
