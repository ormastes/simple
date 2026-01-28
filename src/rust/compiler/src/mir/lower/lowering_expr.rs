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

                // Special handling for rt_value_to_string - box integers/floats
                if name == "rt_value_to_string" && args.len() == 1 {
                    let arg = &args[0];
                    let arg_reg = self.lower_expr(arg)?;

                    // Check if argument is a native integer or float type that needs boxing
                    let needs_boxing = matches!(
                        arg.ty,
                        TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 |
                        TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
                    );
                    let needs_float_boxing = matches!(arg.ty, TypeId::F32 | TypeId::F64);

                    return self.with_func(|func, current_block| {
                        // Box the argument if it's a native numeric type
                        let boxed_arg = if needs_boxing {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::BoxInt { dest: boxed, value: arg_reg });
                            boxed
                        } else if needs_float_boxing {
                            let boxed = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::BoxFloat { dest: boxed, value: arg_reg });
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
                // Lower field expressions first
                let mut field_regs = Vec::new();
                for field in fields {
                    field_regs.push(self.lower_expr(field)?);
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

            // Field access expression: obj.field
            HirExprKind::FieldAccess { receiver, field_index } => {
                let receiver_reg = self.lower_expr(receiver)?;
                let field_index = *field_index;

                // Compute byte offset - assume 8 bytes per field for now
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

            // Index expression: array[index] or string[index]
            HirExprKind::Index { receiver, index } => {
                let receiver_reg = self.lower_expr(receiver)?;
                let index_reg = self.lower_expr(index)?;

                // Use rt_array_get which works for both arrays and strings
                let target = CallTarget::from_name("rt_array_get");
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
                        // Dynamic dispatch: currently Simple doesn't use vtable-based dispatch
                        // for user types. Use static dispatch with method name matching instead.
                        // This works because user classes don't have vtables - only trait objects would.
                        //
                        // TODO: Add proper vtable dispatch when trait objects are implemented.
                        //
                        // For now, use MethodCallStatic which will search for Type.method pattern.
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
                }
            }

            // Global enum variant or global variable
            HirExprKind::Global(name) => {
                // Check if this is an enum variant (contains ::)
                if let Some((enum_name, variant)) = name.split_once("::") {
                    // Look up the enum type to find the variant index
                    if let Some(registry) = self.type_registry {
                        if let Some(enum_type_id) = registry.lookup(enum_name) {
                            if let Some(HirType::Enum { variants, .. }) = registry.get(enum_type_id) {
                                for (idx, (variant_name, _fields)) in variants.iter().enumerate() {
                                    if variant_name == variant {
                                        // Emit the discriminant value as an integer
                                        return self.with_func(|func, current_block| {
                                            let dest = func.new_vreg();
                                            let block = func.block_mut(current_block).unwrap();
                                            block.instructions.push(MirInst::ConstInt {
                                                dest,
                                                value: idx as i64,
                                            });
                                            dest
                                        });
                                    }
                                }
                            }
                        }
                    }
                    // Enum or variant not found - fall through to error
                    return Err(MirLowerError::Unsupported(format!("unknown enum variant: {}", name)));
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
                        ()
                    })?;
                }

                Ok(dict_reg)
            }

            HirExprKind::Nil => {
                // Nil is represented as integer 0 (null pointer)
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                    dest
                })
            }

            HirExprKind::If { condition, then_branch, else_branch } => {
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

            _ => Err(MirLowerError::Unsupported(format!("{:?}", expr_kind))),
        }
    }
}
