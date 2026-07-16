//! Struct/field/index expression lowering: StructInit, FieldAccess, Index.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, HirType, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, UnitOverflowBehavior, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_struct_init_expr(&mut self, ty: TypeId, fields: &[HirExpr]) -> MirLowerResult<VReg> {
        // Lower field expressions first
        let mut field_regs = Vec::new();
        for field in fields {
            field_regs.push(self.lower_expr(field)?);
        }

        // For builtin type "constructors" (str, int), box integer-typed
        // fields as RuntimeValues so the codegen receives tagged values.
        if (ty == TypeId::STRING || ty == TypeId::ANY) && field_regs.len() == 1 {
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
            .and_then(|registry| registry.get_type_name(ty))
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

                    for (param_idx, (param_ty, type_name_hint, is_injectable)) in param_info.iter().enumerate() {
                        if *is_injectable {
                            let injected = self.resolve_di_arg_with_hint(
                                *param_ty,
                                type_name_hint.as_deref(),
                                &constructor_name,
                                param_idx,
                            )?;
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
            }) = registry.get(ty)
            {
                let field_types: Vec<TypeId> = struct_fields.iter().map(|(_, ty)| *ty).collect();
                // For now, use simple sequential layout (simplified, may not match actual layout)
                let mut offsets = Vec::new();
                let mut offset = 0u32;
                for (_, _field_ty) in struct_fields {
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
                type_id: ty,
                struct_name: type_name.clone(),
                struct_size,
                field_offsets,
                field_types,
                field_values: field_regs,
            });
            dest
        })
    }

    pub(super) fn lower_field_access_expr(
        &mut self,
        receiver: &HirExpr,
        field_index: usize,
        expr_ty: TypeId,
    ) -> MirLowerResult<VReg> {
        let receiver_reg = self.lower_expr(receiver)?;
        let receiver_ty = receiver.ty;

        // Check if the receiver is a tuple type — tuples are opaque runtime
        // objects accessed via rt_tuple_get, not flat structs. Labeled tuples
        // use the same positional runtime representation; labels are type
        // metadata used before MIR lowering.
        let is_tuple = self
            .type_registry
            .and_then(|tr| tr.get(receiver_ty))
            .is_some_and(|t| matches!(t, HirType::Tuple(_) | HirType::LabeledTuple(_)));

        if let Some(HirType::Bitfield { fields, .. }) = self.type_registry.and_then(|tr| tr.get(receiver_ty)) {
            if let Some(field) = fields.get(field_index) {
                let mask = if field.bit_width >= 64 {
                    -1i64
                } else {
                    ((1u64 << field.bit_width) - 1) as i64
                };
                let shifted = if field.bit_offset == 0 {
                    receiver_reg
                } else {
                    let shift_reg = self.with_func(|func, current_block| {
                        let r = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ConstInt {
                            dest: r,
                            value: field.bit_offset as i64,
                        });
                        r
                    })?;
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BinOp {
                            dest,
                            op: crate::hir::BinOp::ShiftRight,
                            left: receiver_reg,
                            right: shift_reg,
                        });
                        dest
                    })?
                };
                let mask_reg = self.with_func(|func, current_block| {
                    let r = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest: r, value: mask });
                    r
                })?;
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BinOp {
                        dest,
                        op: crate::hir::BinOp::BitAnd,
                        left: shifted,
                        right: mask_reg,
                    });
                    dest
                });
            }
        }

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

    pub(super) fn lower_index_expr(
        &mut self,
        receiver: &HirExpr,
        index: &HirExpr,
        expr_ty: TypeId,
    ) -> MirLowerResult<VReg> {
        let has_loop_len_bound = self.index_has_active_len_bound(receiver, index);
        let hoisted_data_ptr = self.active_array_data_ptr(receiver, index);
        let receiver_reg = if hoisted_data_ptr.is_some() {
            hoisted_data_ptr.unwrap()
        } else {
            self.lower_expr(receiver)?
        };
        let index_reg = self.lower_expr(index)?;
        let index_ty = if index.ty == TypeId::ANY || index.ty.0 == u32::MAX {
            self.recover_receiver_type(index).unwrap_or(index.ty)
        } else {
            index.ty
        };
        let receiver_ty = receiver.ty;
        let recovered_receiver_ty = if receiver_ty == TypeId::ANY || receiver_ty.0 == u32::MAX {
            self.recover_receiver_type(receiver)
        } else {
            Some(receiver_ty)
        };
        let receiver_is_array = self
            .type_registry
            .and_then(|tr| recovered_receiver_ty.and_then(|ty| tr.get(ty)))
            .is_some_and(|ty| matches!(ty, HirType::Array { .. }));
        // Mirror `receiver_is_array` (and Dict #117): test the ANY-recovered
        // type, not the raw `receiver_ty`. When `[u8]`/`[u32]`/`[u64]` erases
        // to ANY across extern facades, the raw ty is ANY and these typed
        // fast-path flags would be false, dropping to generic `rt_index_get`
        // with no narrow — mistagging the handle for strict C byte consumers
        // (sshd banner garbage). `recovered_receiver_ty` degenerates to
        // `Some(receiver_ty)` when the raw ty is not ANY, so this only widens
        // the erased case.
        let receiver_is_u8_array = self
            .type_registry
            .and_then(|tr| recovered_receiver_ty.and_then(|ty| tr.get(ty)))
            .is_some_and(|ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U8));
        let receiver_is_u32_array = self
            .type_registry
            .and_then(|tr| recovered_receiver_ty.and_then(|ty| tr.get(ty)))
            .is_some_and(|ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U32));
        let receiver_is_u64_array = self
            .type_registry
            .and_then(|tr| recovered_receiver_ty.and_then(|ty| tr.get(ty)))
            .is_some_and(|ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U64));
        let element_expr_ty = if expr_ty == TypeId::ANY {
            self.type_registry
                .and_then(|tr| tr.get(receiver_ty))
                .and_then(|ty| match ty {
                    HirType::Array { element, .. } => Some(*element),
                    // Dict<K, V>: `d[k]` yields the value type V so a scalar
                    // value gets unboxed symmetrically with the store side, and
                    // a heap value type (struct/enum) is passed through verbatim
                    // (no spurious unbox). Task #117.
                    HirType::Dict { value, .. } => Some(*value),
                    _ => None,
                })
                .unwrap_or(expr_ty)
        } else {
            expr_ty
        };

        // Check if the receiver is a tuple type. Labeled tuple indexing also
        // lowers through rt_tuple_get because MIR stores fields positionally.
        let is_tuple = self
            .type_registry
            .and_then(|tr| tr.get(receiver_ty))
            .is_some_and(|t| matches!(t, crate::hir::HirType::Tuple(_) | crate::hir::HirType::LabeledTuple(_)));

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
        } else if receiver_is_u8_array
            && matches!(
                index_ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            )
        {
            return self.with_func(|func, current_block| {
                let raw_byte = func.new_vreg();
                let narrowed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(raw_byte),
                    target: CallTarget::from_name(if hoisted_data_ptr.is_some() {
                        "rt_typed_bytes_u8_data_at"
                    } else if has_loop_len_bound {
                        "rt_typed_bytes_u8_unchecked"
                    } else {
                        "rt_typed_bytes_u8_at"
                    }),
                    args: vec![receiver_reg, index_reg],
                });
                block.instructions.push(MirInst::UnitNarrow {
                    dest: narrowed,
                    value: raw_byte,
                    from_bits: 64,
                    to_bits: 8,
                    signed: false,
                    overflow: UnitOverflowBehavior::Wrap,
                });
                narrowed
            });
        } else if receiver_is_u32_array
            && matches!(
                index_ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            )
        {
            return self.with_func(|func, current_block| {
                let raw_word = func.new_vreg();
                let narrowed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(raw_word),
                    target: CallTarget::from_name(if hoisted_data_ptr.is_some() {
                        "rt_typed_words_u32_data_at"
                    } else if has_loop_len_bound {
                        "rt_typed_words_u32_unchecked"
                    } else {
                        "rt_typed_words_u32_at"
                    }),
                    args: vec![hoisted_data_ptr.unwrap_or(receiver_reg), index_reg],
                });
                block.instructions.push(MirInst::UnitNarrow {
                    dest: narrowed,
                    value: raw_word,
                    from_bits: 64,
                    to_bits: 32,
                    signed: false,
                    overflow: UnitOverflowBehavior::Wrap,
                });
                narrowed
            });
        } else if receiver_is_u64_array
            && matches!(
                index_ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            )
        {
            return self.with_func(|func, current_block| {
                let raw_word = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                if let Some(data_ptr) = hoisted_data_ptr {
                    block.instructions.push(MirInst::Call {
                        dest: Some(raw_word),
                        target: CallTarget::from_name("rt_typed_words_u64_raw_data_at"),
                        args: vec![data_ptr, index_reg],
                    });
                } else {
                    block.instructions.push(MirInst::Call {
                        dest: Some(raw_word),
                        target: CallTarget::from_name(if has_loop_len_bound {
                            "rt_typed_words_u64_unchecked"
                        } else {
                            "rt_typed_words_u64_at"
                        }),
                        args: vec![receiver_reg, index_reg],
                    });
                }
                raw_word
            });
        } else if receiver_is_array
            && matches!(
                index_ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            )
        {
            // HIR already proved this receiver is an array, so avoid the
            // generic collection dispatcher and boxed-index path.
            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target: CallTarget::from_name(if element_expr_ty == TypeId::STRING {
                        "rt_array_get_text"
                    } else {
                        "rt_array_get"
                    }),
                    args: vec![receiver_reg, index_reg],
                });
                dest
            })?
        } else {
            // Box the index as RuntimeValue if it's a native type
            let boxed_index = {
                let needs_int_boxing = receiver_is_array
                    || matches!(
                        index_ty,
                        TypeId::I8
                            | TypeId::I16
                            | TypeId::I32
                            | TypeId::I64
                            | TypeId::U8
                            | TypeId::U16
                            | TypeId::U32
                            | TypeId::U64
                    );
                let needs_bool_boxing = index_ty == TypeId::BOOL;
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
            element_expr_ty,
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
        let needs_float_unbox = matches!(element_expr_ty, TypeId::F32 | TypeId::F64);

        if needs_int_unbox {
            if std::env::var("FR_DRIVER_0002B_TRACE").is_ok() {
                eprintln!("[narrow-hit-1] expr_ty={:?}", element_expr_ty);
            }
            // FR-DRIVER-0002b array variant (A2): after UnboxInt produces an
            // i64-typed payload, narrow it to the actual element width so
            // `body::build_vreg_types` stamps the correct narrow TypeId on the
            // dest, letting `compile_binop` dispatch unsigned `>>` to `ushr`
            // for U8/U16/U32 (and signed `>>` to `sshr` for I8/I16/I32).
            let (to_bits, signed_opt): (u8, Option<bool>) = match element_expr_ty {
                TypeId::U8 => (8, Some(false)),
                TypeId::U16 => (16, Some(false)),
                TypeId::U32 => (32, Some(false)),
                TypeId::I8 => (8, Some(true)),
                TypeId::I16 => (16, Some(true)),
                TypeId::I32 => (32, Some(true)),
                // U64/I64/BOOL: keep i64-typed unboxed VReg unchanged.
                _ => (0, None),
            };
            self.with_func(|func, current_block| {
                let unboxed = func.new_vreg();
                let narrowed_opt = signed_opt.map(|_| func.new_vreg());
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::UnboxInt {
                    dest: unboxed,
                    value: raw_result,
                });
                if let (Some(narrowed), Some(signed)) = (narrowed_opt, signed_opt) {
                    block.instructions.push(MirInst::UnitNarrow {
                        dest: narrowed,
                        value: unboxed,
                        from_bits: 64,
                        to_bits,
                        signed,
                        overflow: UnitOverflowBehavior::Wrap,
                    });
                    narrowed
                } else {
                    unboxed
                }
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
        } else if element_expr_ty == TypeId::STRING {
            self.with_func(|func, current_block| {
                let typed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Cast {
                    dest: typed,
                    source: raw_result,
                    from_ty: TypeId::STRING,
                    to_ty: TypeId::STRING,
                });
                typed
            })
        } else {
            // Strings, arrays, objects are already usable as pointers
            Ok(raw_result)
        }
    }
}
