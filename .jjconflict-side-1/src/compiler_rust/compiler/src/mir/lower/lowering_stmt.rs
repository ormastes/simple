//! Statement lowering for MIR
//!
//! This module contains methods for lowering HIR statements to MIR instructions,
//! including control flow (if, while, loop, break, continue) and assignments.

use super::lowering_core::{ArrayAppendPtrs, LoopContext, MirLowerResult, MirLowerer};
use crate::hir::{BinOp, HirContract, HirExpr, HirExprKind, HirStmt, HirType, TypeId};
use crate::mir::blocks::Terminator;
use crate::mir::effects::CallTarget;
use crate::mir::effects::LocalKind;
use crate::mir::function::MirLocal;
use crate::mir::instructions::{MirInst, UnitOverflowBehavior};

impl<'a> MirLowerer<'a> {
    fn emit_runtime_pool_safepoint(&mut self) -> MirLowerResult<()> {
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Call {
                dest: None,
                target: CallTarget::from_name("rt_pool_safepoint"),
                args: vec![],
            });
        })
    }

    pub(super) fn lower_stmt(&mut self, stmt: &HirStmt, contract: Option<&HirContract>) -> MirLowerResult<()> {
        match stmt {
            HirStmt::Let {
                local_index,
                ty: declared_ty,
                value,
            } => {
                let mut effective_declared_ty = *declared_ty;
                self.with_func(|func, _| {
                    let param_count = func.params.len();
                    if *local_index >= param_count {
                        let local_slot = *local_index - param_count;
                        while func.locals.len() <= local_slot {
                            let index = param_count + func.locals.len();
                            let ty = if index == *local_index {
                                *declared_ty
                            } else {
                                TypeId::ANY
                            };
                            func.locals.push(MirLocal {
                                name: format!("$block_local_{}", index),
                                ty,
                                kind: LocalKind::Local,
                                is_ghost: false,
                            });
                        }
                        if let Some(local) = func.locals.get_mut(local_slot) {
                            effective_declared_ty = local.ty;
                        }
                    }
                })?;
                if self.dead_append_array_locals.contains(local_index) {
                    self.record_len_local_source(*local_index, None);
                    self.record_array_capacity_local_source(*local_index, None);
                    return Ok(());
                }
                if let Some(val) = value {
                    let is_u8_array_declared = self
                        .type_registry
                        .and_then(|tr| tr.get(effective_declared_ty))
                        .is_some_and(|ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U8));

                    if is_u8_array_declared {
                        if let HirExprKind::Array(elements) = &val.kind {
                            if elements.is_empty() {
                                // Empty [u8] literal: allocate a byte-packed buffer with default capacity.
                                let local_idx = *local_index;
                                self.with_func(|func, current_block| {
                                    let capacity = func.new_vreg();
                                    let array = func.new_vreg();
                                    let addr = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::ConstInt {
                                        dest: capacity,
                                        value: 1024,
                                    });
                                    block.instructions.push(MirInst::Call {
                                        dest: Some(array),
                                        target: CallTarget::from_name("rt_byte_array_new"),
                                        args: vec![capacity],
                                    });
                                    block.instructions.push(MirInst::LocalAddr {
                                        dest: addr,
                                        local_index: local_idx,
                                    });
                                    block.instructions.push(MirInst::Store {
                                        addr,
                                        value: array,
                                        ty: effective_declared_ty,
                                    });
                                })?;
                                return Ok(());
                            } else {
                                // Non-empty [u8] literal: bare integer literals default to I64 in HIR,
                                // so the element type check in lower_array_expr misses this case.
                                // Use declared_ty here to emit packed byte storage.
                                let capacity = elements.len() as i64;
                                // Clone elements to avoid borrowing `self` while calling methods.
                                let elements: Vec<_> = elements.to_vec();
                                let local_idx = *local_index;
                                let capacity_reg = self.with_func(|func, current_block| {
                                    let reg = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::ConstInt {
                                        dest: reg,
                                        value: capacity,
                                    });
                                    reg
                                })?;
                                let array_reg = self.with_func(|func, current_block| {
                                    let dest = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::Call {
                                        dest: Some(dest),
                                        target: CallTarget::from_name("rt_byte_array_new"),
                                        args: vec![capacity_reg],
                                    });
                                    dest
                                })?;
                                for elem in &elements {
                                    let value_reg = self.lower_expr(elem)?;
                                    self.with_func(|func, current_block| {
                                        let dest = func.new_vreg();
                                        let block = func.block_mut(current_block).unwrap();
                                        block.instructions.push(MirInst::Call {
                                            dest: Some(dest),
                                            target: CallTarget::from_name("rt_typed_bytes_u8_push"),
                                            args: vec![array_reg, value_reg],
                                        });
                                        dest
                                    })?;
                                }
                                self.with_func(|func, current_block| {
                                    let addr = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::LocalAddr {
                                        dest: addr,
                                        local_index: local_idx,
                                    });
                                    block.instructions.push(MirInst::Store {
                                        addr,
                                        value: array_reg,
                                        ty: effective_declared_ty,
                                    });
                                })?;
                                self.record_len_local_source(*local_index, Some(val));
                                self.record_array_capacity_local_source(*local_index, Some(val));
                                return Ok(());
                            }
                        }
                    }

                    let vreg = self.lower_expr(val)?;
                    let local_idx = *local_index;
                    let value_ty = val.ty;

                    // Wrap value in union if assigning to a union type
                    let vreg = self.emit_union_wrap_if_needed(effective_declared_ty, value_ty, vreg)?;

                    // Emit unit bound check if assigning to a unit type with constraints
                    self.emit_unit_bound_check(effective_declared_ty, vreg)?;

                    // Track tagged status: if storing a tagged VReg, mark the local as tagged
                    if self.tagged_vregs.contains(&vreg) {
                        self.tagged_locals.insert(local_idx);
                    } else {
                        self.tagged_locals.remove(&local_idx);
                    }

                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest,
                            local_index: local_idx,
                        });
                        block.instructions.push(MirInst::Store {
                            addr: dest,
                            value: vreg,
                            ty: effective_declared_ty,
                        });
                    })?;
                    self.record_len_local_source(*local_index, Some(val));
                    self.record_array_capacity_local_source(*local_index, Some(val));
                } else {
                    self.record_len_local_source(*local_index, None);
                    self.record_array_capacity_local_source(*local_index, None);
                }
                Ok(())
            }

            HirStmt::Assign { target, value } => {
                if let HirExprKind::Local(local_index) = &target.kind {
                    self.record_len_local_source(*local_index, None);
                    self.record_array_capacity_local_source(*local_index, None);
                }
                let val_reg = self.lower_expr(value)?;
                let ty = value.ty;

                // Emit unit bound check if assigning to a unit type with constraints
                self.emit_unit_bound_check(ty, val_reg)?;

                // Handle different assignment targets
                match &target.kind {
                    // Field assignment: obj.field = value -> FieldSet (or rt_tuple_set for tuples)
                    HirExprKind::FieldAccess { receiver, field_index } => {
                        let receiver_reg = self.lower_expr(receiver)?;
                        let field_index = *field_index;
                        let receiver_ty = receiver.ty;

                        if let Some(HirType::Bitfield { fields, .. }) =
                            self.type_registry.and_then(|tr| tr.get(receiver_ty))
                        {
                            if let (Some(field), HirExprKind::Local(local_idx)) =
                                (fields.get(field_index), &receiver.kind)
                            {
                                let field_mask = if field.bit_width >= 64 {
                                    u64::MAX
                                } else {
                                    (1u64 << field.bit_width) - 1
                                };
                                let shifted_mask = field_mask << field.bit_offset;
                                let keep_mask = !(shifted_mask as i64);

                                let updated = self.with_func(|func, current_block| {
                                    let keep_mask_reg = func.new_vreg();
                                    let value_mask_reg = func.new_vreg();
                                    let shift_reg = func.new_vreg();
                                    let kept = func.new_vreg();
                                    let masked_value = func.new_vreg();
                                    let shifted_value = func.new_vreg();
                                    let combined = func.new_vreg();
                                    let addr = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::ConstInt {
                                        dest: keep_mask_reg,
                                        value: keep_mask,
                                    });
                                    block.instructions.push(MirInst::BinOp {
                                        dest: kept,
                                        op: BinOp::BitAnd,
                                        left: receiver_reg,
                                        right: keep_mask_reg,
                                    });
                                    block.instructions.push(MirInst::ConstInt {
                                        dest: value_mask_reg,
                                        value: field_mask as i64,
                                    });
                                    block.instructions.push(MirInst::BinOp {
                                        dest: masked_value,
                                        op: BinOp::BitAnd,
                                        left: val_reg,
                                        right: value_mask_reg,
                                    });
                                    block.instructions.push(MirInst::ConstInt {
                                        dest: shift_reg,
                                        value: field.bit_offset as i64,
                                    });
                                    block.instructions.push(MirInst::BinOp {
                                        dest: shifted_value,
                                        op: BinOp::ShiftLeft,
                                        left: masked_value,
                                        right: shift_reg,
                                    });
                                    block.instructions.push(MirInst::BinOp {
                                        dest: combined,
                                        op: BinOp::BitOr,
                                        left: kept,
                                        right: shifted_value,
                                    });
                                    block.instructions.push(MirInst::LocalAddr {
                                        dest: addr,
                                        local_index: *local_idx,
                                    });
                                    block.instructions.push(MirInst::Store {
                                        addr,
                                        value: combined,
                                        ty: receiver_ty,
                                    });
                                    combined
                                })?;
                                if self.tagged_vregs.contains(&updated) {
                                    self.tagged_locals.insert(*local_idx);
                                } else {
                                    self.tagged_locals.remove(local_idx);
                                }
                                return Ok(());
                            }
                        }

                        // Check if the receiver is a tuple type — tuples use
                        // rt_tuple_set, not raw memory stores.
                        let is_tuple = self
                            .type_registry
                            .and_then(|tr| tr.get(receiver_ty))
                            .is_some_and(|t| matches!(t, HirType::Tuple(_)));

                        if is_tuple {
                            // Emit: index_reg = ConstInt(field_index)
                            //        Call rt_tuple_set(receiver_reg, index_reg, val_reg)
                            let index_reg = self.with_func(|func, current_block| {
                                let idx = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::ConstInt {
                                    dest: idx,
                                    value: field_index as i64,
                                });
                                idx
                            })?;

                            let target = CallTarget::from_name("rt_tuple_set");
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target,
                                    args: vec![receiver_reg, index_reg, val_reg],
                                });
                            })?;
                        } else {
                            let byte_offset = (field_index as u32) * 8;

                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::FieldSet {
                                    object: receiver_reg,
                                    byte_offset,
                                    field_type: ty,
                                    value: val_reg,
                                });
                            })?;
                        }
                    }

                    // Index assignment: arr[i] = value -> rt_index_set call
                    HirExprKind::Index { receiver, index } => {
                        let receiver_reg = self.lower_expr(receiver)?;
                        let index_reg = self.lower_expr(index)?;

                        let is_u8_array_set = matches!(
                            index.ty,
                            TypeId::I16
                                | TypeId::I32
                                | TypeId::I64
                                | TypeId::U8
                                | TypeId::U16
                                | TypeId::U32
                                | TypeId::U64
                        ) && self
                            .type_registry
                            .and_then(|tr| tr.get(receiver.ty))
                            .is_some_and(|ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U8));
                        let is_u32_array_set = value.ty == TypeId::U32
                            && matches!(
                                index.ty,
                                TypeId::I16
                                    | TypeId::I32
                                    | TypeId::I64
                                    | TypeId::U8
                                    | TypeId::U16
                                    | TypeId::U32
                                    | TypeId::U64
                            )
                            && self.type_registry.and_then(|tr| tr.get(receiver.ty)).is_some_and(
                                |ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U32),
                            );
                        let is_u64_array_set = value.ty == TypeId::U64
                            && matches!(
                                index.ty,
                                TypeId::I16
                                    | TypeId::I32
                                    | TypeId::I64
                                    | TypeId::U8
                                    | TypeId::U16
                                    | TypeId::U32
                                    | TypeId::U64
                            )
                            && self.type_registry.and_then(|tr| tr.get(receiver.ty)).is_some_and(
                                |ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U64),
                            );
                        let is_text_array_set = value.ty == TypeId::STRING
                            && matches!(
                                index.ty,
                                TypeId::I16
                                    | TypeId::I32
                                    | TypeId::I64
                                    | TypeId::U8
                                    | TypeId::U16
                                    | TypeId::U32
                                    | TypeId::U64
                            )
                            && self.type_registry.and_then(|tr| tr.get(receiver.ty)).is_some_and(
                                |ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::STRING),
                            );
                        if is_u8_array_set {
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target: crate::mir::CallTarget::from_name("rt_typed_bytes_u8_set"),
                                    args: vec![receiver_reg, index_reg, val_reg],
                                });
                            })?;
                        } else if is_u32_array_set {
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target: crate::mir::CallTarget::from_name("rt_typed_words_u32_set"),
                                    args: vec![receiver_reg, index_reg, val_reg],
                                });
                            })?;
                        } else if is_u64_array_set {
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target: crate::mir::CallTarget::from_name("rt_typed_words_u64_set"),
                                    args: vec![receiver_reg, index_reg, val_reg],
                                });
                            })?;
                        } else if is_text_array_set {
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target: crate::mir::CallTarget::from_name("rt_array_set_text"),
                                    args: vec![receiver_reg, index_reg, val_reg],
                                });
                            })?;
                        } else {
                            // Box index if it's a native type (int index for arrays)
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
                                            target: crate::mir::CallTarget::from_name("rt_value_bool"),
                                            args: vec![index_reg],
                                        });
                                        boxed
                                    })?
                                } else {
                                    index_reg
                                }
                            };

                            // Derive the receiver's element/value type. For a
                            // Dict<K, V> whose value type V is a heap type
                            // (struct/enum/string/array), the value operand is
                            // ALREADY a heap RuntimeValue; boxing it with BoxInt
                            // would wrap the heap pointer as a boxed-int and
                            // destroy its tag (task #117 / #107: env
                            // `Dict<text, Value>` round-trip → disc -1). Only box
                            // when the destination slot expects a raw scalar.
                            let recv_elem_ty: Option<TypeId> = self
                                .type_registry
                                .and_then(|tr| tr.get(receiver.ty))
                                .and_then(|ty| match ty {
                                    HirType::Array { element, .. } => Some(*element),
                                    HirType::Dict { value, .. } => Some(*value),
                                    _ => None,
                                });
                            let elem_is_heap = matches!(
                                recv_elem_ty,
                                Some(t)
                                    if t != TypeId::ANY
                                        && !matches!(
                                            t,
                                            TypeId::I8
                                                | TypeId::I16
                                                | TypeId::I32
                                                | TypeId::I64
                                                | TypeId::U8
                                                | TypeId::U16
                                                | TypeId::U32
                                                | TypeId::U64
                                                | TypeId::F32
                                                | TypeId::F64
                                                | TypeId::BOOL
                                        )
                            );

                            // Box value if it's a native type
                            let boxed_val = {
                                let needs_int_boxing = !elem_is_heap
                                    && matches!(
                                        value.ty,
                                        TypeId::I16
                                            | TypeId::I32
                                            | TypeId::I64
                                            | TypeId::U8
                                            | TypeId::U16
                                            | TypeId::U32
                                            | TypeId::U64
                                    );
                                let needs_float_boxing = !elem_is_heap && matches!(value.ty, TypeId::F32 | TypeId::F64);
                                let needs_bool_boxing =
                                    !elem_is_heap && (value.ty == TypeId::BOOL || value.ty == TypeId::I8);
                                if needs_int_boxing {
                                    self.with_func(|func, current_block| {
                                        let boxed = func.new_vreg();
                                        let block = func.block_mut(current_block).unwrap();
                                        block.instructions.push(MirInst::BoxInt {
                                            dest: boxed,
                                            value: val_reg,
                                        });
                                        boxed
                                    })?
                                } else if needs_float_boxing {
                                    self.with_func(|func, current_block| {
                                        let boxed = func.new_vreg();
                                        let block = func.block_mut(current_block).unwrap();
                                        block.instructions.push(MirInst::BoxFloat {
                                            dest: boxed,
                                            value: val_reg,
                                        });
                                        boxed
                                    })?
                                } else if needs_bool_boxing {
                                    self.with_func(|func, current_block| {
                                        let boxed = func.new_vreg();
                                        let block = func.block_mut(current_block).unwrap();
                                        block.instructions.push(MirInst::Call {
                                            dest: Some(boxed),
                                            target: crate::mir::CallTarget::from_name("rt_value_bool"),
                                            args: vec![val_reg],
                                        });
                                        boxed
                                    })?
                                } else {
                                    val_reg
                                }
                            };

                            // Use rt_index_set for array/dict index assignment (handles both types)
                            let target = crate::mir::CallTarget::from_name("rt_index_set");
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target,
                                    args: vec![receiver_reg, boxed_index, boxed_val],
                                });
                            })?;
                        }
                    }

                    // Property setter: obj.field = value (when field access became MethodCall)
                    // This happens when type information is lost or for dynamic property access
                    HirExprKind::MethodCall {
                        receiver, method, args, ..
                    } if args.is_empty() => {
                        let receiver_reg = self.lower_expr(receiver)?;

                        // Create a string constant for the field name
                        let field_name_reg = self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ConstString {
                                dest,
                                value: method.clone(),
                            });
                            dest
                        })?;

                        // Use rt_field_set for dynamic field assignment
                        let target = crate::mir::CallTarget::from_name("rt_field_set");
                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: None,
                                target,
                                args: vec![receiver_reg, field_name_reg, val_reg],
                            });
                        })?;
                    }

                    // Tuple destructuring: (a, b, c) = expr
                    HirExprKind::Tuple(elements) => {
                        // val_reg holds the tuple value; extract each element and assign
                        for (i, elem) in elements.iter().enumerate() {
                            // Create index constant
                            let index_reg = self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::ConstInt { dest, value: i as i64 });
                                dest
                            })?;
                            // Extract tuple element via rt_tuple_get
                            let elem_reg = self.with_func(|func, current_block| {
                                let dest = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(dest),
                                    target: crate::mir::CallTarget::from_name("rt_tuple_get"),
                                    args: vec![val_reg, index_reg],
                                });
                                dest
                            })?;
                            // Store to the lvalue element
                            let addr_reg = self.lower_lvalue(elem)?;
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Store {
                                    addr: addr_reg,
                                    value: elem_reg,
                                    ty: elem.ty,
                                });
                            })?;
                        }
                    }

                    // Global variable assignment: use GlobalStore directly
                    HirExprKind::Global(name) => {
                        let global_name = name.clone();
                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::GlobalStore {
                                global_name,
                                value: val_reg,
                                ty,
                            });
                        })?;
                    }

                    // Local variable assignment: use address + store pattern
                    _ => {
                        // Tagged value tracking: if storing a tagged RuntimeValue
                        // (e.g., from rt_enum_payload) to a concrete int-typed local,
                        // insert UnboxInt to convert tagged→raw before storing.
                        // This prevents double-tagging when the local is later BoxInt'd.
                        let is_tagged_val = self.tagged_vregs.contains(&val_reg);
                        let target_is_int = matches!(
                            target.ty,
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
                        let target_is_float = matches!(target.ty, TypeId::F32 | TypeId::F64);

                        let store_val = if is_tagged_val && target_is_int {
                            // Unbox tagged RuntimeValue to raw integer before storing
                            self.with_func(|func, current_block| {
                                let unboxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::UnboxInt {
                                    dest: unboxed,
                                    value: val_reg,
                                });
                                unboxed
                            })?
                        } else if is_tagged_val && target_is_float {
                            self.with_func(|func, current_block| {
                                let unboxed = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::UnboxFloat {
                                    dest: unboxed,
                                    value: val_reg,
                                });
                                unboxed
                            })?
                        } else {
                            val_reg
                        };

                        let addr_reg = self.lower_lvalue(target)?;
                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Store {
                                addr: addr_reg,
                                value: store_val,
                                ty,
                            });
                        })?;
                    }
                }

                Ok(())
            }

            HirStmt::Return(value) => {
                let ret_reg = if let Some(v) = value {
                    let reg = self.lower_expr(v)?;
                    Some(reg)
                } else {
                    None
                };

                // Emit contract checks before the actual return based on contract mode
                if let Some(contract) = contract {
                    if self.should_emit_contracts() {
                        // Detect if this is a Result::Err return to call the appropriate contract handler
                        let is_error_return = value
                            .as_ref()
                            .map(|v| self.is_result_err_construction(v))
                            .unwrap_or(false);

                        if is_error_return && !contract.error_postconditions.is_empty() {
                            // This is an error return - emit error postconditions
                            if let Some(ret) = ret_reg {
                                self.emit_error_contracts(contract, ret)?;
                            }
                        } else {
                            // This is a success return - emit normal postconditions
                            self.emit_exit_contracts(contract, ret_reg)?;
                        }
                    }
                }

                // Emit deferred blocks in LIFO order before returning
                self.emit_deferred_blocks(contract)?;

                // Emit drop instructions for all locals before returning
                // This ensures proper cleanup in LIFO order (Rust-level memory safety)
                self.emit_function_drops()?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Return(ret_reg);
                })?;
                Ok(())
            }

            HirStmt::Expr(expr) => {
                if let HirExprKind::MethodCall {
                    receiver, method, args, ..
                } = &expr.kind
                {
                    if (method == "push" || method == "append") && args.len() == 1 {
                        if self.is_dead_append_array_local(receiver) {
                            let _ = self.lower_expr(&args[0])?;
                            self.last_expr_value = None;
                            return Ok(());
                        }

                        let typed_push_target =
                            if self.type_registry.and_then(|tr| tr.get(receiver.ty)).is_some_and(
                                |ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U8),
                            ) {
                                Some("rt_typed_bytes_u8_push")
                            } else if args[0].ty == TypeId::U32
                                && self.type_registry.and_then(|tr| tr.get(receiver.ty)).is_some_and(
                                    |ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U32),
                                )
                            {
                                Some("rt_typed_words_u32_push")
                            } else if args[0].ty == TypeId::U64
                                && self.type_registry.and_then(|tr| tr.get(receiver.ty)).is_some_and(
                                    |ty| matches!(ty, HirType::Array { element, .. } if *element == TypeId::U64),
                                )
                            {
                                Some("rt_typed_words_u64_push")
                            } else {
                                None
                            };

                        if let Some(target) = typed_push_target {
                            let receiver_reg = self.lower_expr(receiver)?;
                            let value_reg = self.lower_expr(&args[0])?;
                            let append_ptrs = self.active_array_append_ptrs(receiver);
                            let append_index = append_ptrs
                                .map(|ptrs| ptrs.index_local_index)
                                .or_else(|| self.active_array_append_index(receiver));
                            let index_reg = if let Some(index_local_index) = append_index {
                                Some(self.with_func(|func, current_block| {
                                    let addr = func.new_vreg();
                                    let index = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::LocalAddr {
                                        dest: addr,
                                        local_index: index_local_index,
                                    });
                                    block.instructions.push(MirInst::Load {
                                        dest: index,
                                        addr,
                                        ty: TypeId::U64,
                                    });
                                    index
                                })?)
                            } else {
                                None
                            };
                            let target = match (target, append_index) {
                                ("rt_typed_words_u32_push", Some(_)) if append_ptrs.is_some() => {
                                    "rt_typed_words_u32_store_known_data_at"
                                }
                                ("rt_typed_words_u64_push", Some(_)) if append_ptrs.is_some() => {
                                    "rt_typed_words_u64_store_known_data_at"
                                }
                                ("rt_typed_words_u32_push", Some(_)) => "rt_typed_words_u32_push_known_at",
                                ("rt_typed_words_u64_push", Some(_)) => "rt_typed_words_u64_push_known_at",
                                _ => target,
                            };
                            self.with_func(|func, current_block| {
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: None,
                                    target: CallTarget::from_name(target),
                                    args: if let (Some(ptrs), Some(index_reg)) = (append_ptrs, index_reg) {
                                        vec![ptrs.header_ptr, ptrs.data_ptr, index_reg, value_reg]
                                    } else if let Some(index_reg) = index_reg {
                                        vec![receiver_reg, index_reg, value_reg]
                                    } else {
                                        vec![receiver_reg, value_reg]
                                    },
                                });
                            })?;
                            self.last_expr_value = None;
                            return Ok(());
                        }
                    }
                }

                let vreg = self.lower_expr(expr)?;
                // Track the last expression value for implicit returns
                self.last_expr_value = Some(vreg);
                Ok(())
            }

            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                let cond_reg = self.lower_expr(condition)?;

                // Emit decision probe for coverage (before branch)
                self.emit_decision_probe(cond_reg, 0, 0)?;

                // Save last_expr_value before branches (for proper value merging)
                let saved_last_expr = self.last_expr_value;

                // Pre-allocate a temporary local for value merging BEFORE branching.
                // This is critical: when branches contain nested if/else, the current
                // block after lowering is an inner merge block, not then_id/else_id.
                // We must store values in the current block before finalize_block_jump,
                // not go back to then_id/else_id after the fact.
                use crate::hir::TypeId;
                use crate::mir::effects::LocalKind;
                use crate::mir::function::MirLocal;

                let temp_local_index = self.with_func(|func, _| {
                    let index = func.params.len() + func.locals.len();
                    func.locals.push(MirLocal {
                        name: format!("__if_merge_{}", index),
                        ty: TypeId::I64,
                        kind: LocalKind::Local,
                        is_ghost: false,
                    });
                    index
                })?;

                // Create blocks
                let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
                    let then_id = func.new_block();
                    let else_id = func.new_block();
                    let merge_id = func.new_block();

                    // Set branch terminator
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Branch {
                        cond: cond_reg,
                        then_block: then_id,
                        else_block: else_id,
                    };
                    (then_id, else_id, merge_id)
                })?;

                // Lower then block
                self.set_current_block(then_id)?;
                self.last_expr_value = saved_last_expr;
                for stmt in then_block {
                    self.lower_stmt(stmt, contract)?;
                }
                let then_value = self.last_expr_value;
                // Store then value in temp local BEFORE finalize (current block may be inner merge)
                if let Some(tv) = then_value {
                    self.with_func(|func, current_block| {
                        let addr = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest: addr,
                            local_index: temp_local_index,
                        });
                        block.instructions.push(MirInst::Store {
                            addr,
                            value: tv,
                            ty: TypeId::I64,
                        });
                    })?;
                }
                self.finalize_block_jump(merge_id)?;

                // Lower else block
                self.set_current_block(else_id)?;
                self.last_expr_value = saved_last_expr;
                if let Some(else_stmts) = else_block {
                    for stmt in else_stmts {
                        self.lower_stmt(stmt, contract)?;
                    }
                }
                let else_value = self.last_expr_value;
                // Store else value in temp local BEFORE finalize
                if let Some(ev) = else_value {
                    self.with_func(|func, current_block| {
                        let addr = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest: addr,
                            local_index: temp_local_index,
                        });
                        block.instructions.push(MirInst::Store {
                            addr,
                            value: ev,
                            ty: TypeId::I64,
                        });
                    })?;
                }
                self.finalize_block_jump(merge_id)?;

                // Load merged value in merge block
                self.set_current_block(merge_id)?;

                match (then_value, else_value) {
                    (Some(_), _) | (_, Some(_)) => {
                        // At least one branch produced a value - load from temp local
                        let merged_value = self.with_func(|func, current_block| {
                            let addr = func.new_vreg();
                            let value = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::LocalAddr {
                                dest: addr,
                                local_index: temp_local_index,
                            });
                            block.instructions.push(MirInst::Load {
                                dest: value,
                                addr,
                                ty: TypeId::I64,
                            });
                            value
                        })?;
                        self.last_expr_value = Some(merged_value);
                    }
                    (None, None) => {
                        // Neither branch produced a value - restore saved
                        self.last_expr_value = saved_last_expr;
                    }
                }

                Ok(())
            }

            HirStmt::While { condition, body, .. } => {
                let bound_proof = self
                    .loop_len_bound_proof(condition)
                    .filter(|proof| !Self::body_may_mutate_or_escape_array(body, proof.array_local_index));
                let append_bound_proof = self.loop_append_bound_proof(condition, body);
                // Create blocks and set initial jump
                let (cond_id, body_id, exit_id) = self.with_func(|func, current_block| {
                    let cond_id = func.new_block();
                    let body_id = func.new_block();
                    let exit_id = func.new_block();
                    (cond_id, body_id, exit_id)
                })?;

                let hoisted_data_ptr = if let Some(proof) = bound_proof {
                    Some(self.with_func(|func, current_block| {
                        let addr = func.new_vreg();
                        let array = func.new_vreg();
                        let data_ptr = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest: addr,
                            local_index: proof.array_local_index,
                        });
                        block.instructions.push(MirInst::Load {
                            dest: array,
                            addr,
                            ty: TypeId::ANY,
                        });
                        block.instructions.push(MirInst::Call {
                            dest: Some(data_ptr),
                            target: CallTarget::from_name("rt_array_data_ptr"),
                            args: vec![array],
                        });
                        data_ptr
                    })?)
                } else {
                    None
                };
                let hoisted_append_ptrs = if let Some(proof) = append_bound_proof {
                    Some(self.with_func(|func, current_block| {
                        let addr = func.new_vreg();
                        let array = func.new_vreg();
                        let header_ptr = func.new_vreg();
                        let data_ptr = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest: addr,
                            local_index: proof.array_local_index,
                        });
                        block.instructions.push(MirInst::Load {
                            dest: array,
                            addr,
                            ty: TypeId::ANY,
                        });
                        block.instructions.push(MirInst::Call {
                            dest: Some(header_ptr),
                            target: CallTarget::from_name("rt_array_header_ptr"),
                            args: vec![array],
                        });
                        block.instructions.push(MirInst::Call {
                            dest: Some(data_ptr),
                            target: CallTarget::from_name("rt_array_data_ptr"),
                            args: vec![array],
                        });
                        ArrayAppendPtrs {
                            array_local_index: proof.array_local_index,
                            index_local_index: proof.index_local_index,
                            capacity_local_index: proof.capacity_local_index,
                            header_ptr,
                            data_ptr,
                        }
                    })?)
                } else {
                    None
                };

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(cond_id);
                })?;

                // Push loop context for break/continue
                self.push_loop(LoopContext {
                    continue_target: cond_id,
                    break_target: exit_id,
                })?;

                // Check condition
                self.set_current_block(cond_id)?;
                let cond_reg = self.lower_expr(condition)?;

                // Emit decision probe for while condition coverage
                // Line/column require span tracking in HIR expressions
                self.emit_decision_probe(cond_reg, 0, 0)?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Branch {
                        cond: cond_reg,
                        then_block: body_id,
                        else_block: exit_id,
                    };
                })?;

                // Lower body
                self.set_current_block(body_id)?;
                self.emit_runtime_pool_safepoint()?;
                if let Some(proof) = bound_proof {
                    self.active_array_len_bounds.push(proof);
                    if let Some(data_ptr) = hoisted_data_ptr {
                        self.active_array_data_ptrs.push((proof.array_local_index, data_ptr));
                    }
                }
                if let Some(proof) = append_bound_proof {
                    self.active_array_append_bounds.push(proof);
                }
                if let Some(ptrs) = hoisted_append_ptrs {
                    self.active_array_append_ptrs.push(ptrs);
                }
                for stmt in body {
                    self.lower_stmt(stmt, contract)?;
                }
                if hoisted_append_ptrs.is_some() {
                    self.active_array_append_ptrs.pop();
                }
                if append_bound_proof.is_some() {
                    self.active_array_append_bounds.pop();
                }
                if bound_proof.is_some() {
                    self.active_array_len_bounds.pop();
                    if hoisted_data_ptr.is_some() {
                        self.active_array_data_ptrs.pop();
                    }
                }
                self.finalize_block_jump(cond_id)?;

                // Pop loop context
                self.pop_loop()?;

                self.set_current_block(exit_id)?;
                if let Some(ptrs) = hoisted_append_ptrs {
                    let capacity_reg = self.with_func(|func, current_block| {
                        let addr = func.new_vreg();
                        let capacity = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest: addr,
                            local_index: ptrs.capacity_local_index,
                        });
                        block.instructions.push(MirInst::Load {
                            dest: capacity,
                            addr,
                            ty: TypeId::U64,
                        });
                        capacity
                    })?;
                    self.with_func(|func, current_block| {
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: None,
                            target: CallTarget::from_name("rt_array_set_len_known"),
                            args: vec![ptrs.header_ptr, capacity_reg],
                        });
                    })?;
                }
                Ok(())
            }

            HirStmt::Loop { body, .. } => {
                // Create blocks
                let (body_id, exit_id) = self.with_func(|func, current_block| {
                    let body_id = func.new_block();
                    let exit_id = func.new_block();

                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(body_id);
                    (body_id, exit_id)
                })?;

                // Push loop context
                self.push_loop(LoopContext {
                    continue_target: body_id,
                    break_target: exit_id,
                })?;

                self.set_current_block(body_id)?;
                self.emit_runtime_pool_safepoint()?;
                for stmt in body {
                    self.lower_stmt(stmt, contract)?;
                }
                self.finalize_block_jump(body_id)?;

                // Pop loop context
                self.pop_loop()?;

                self.set_current_block(exit_id)?;
                Ok(())
            }

            HirStmt::Break => {
                // Use loop context for proper jump target
                let loop_ctx = self
                    .current_loop()
                    .ok_or(super::lowering_core::MirLowerError::BreakOutsideLoop)?
                    .clone();

                // Emit deferred blocks before breaking out of loop
                self.emit_deferred_blocks(contract)?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(loop_ctx.break_target);
                })?;
                Ok(())
            }

            HirStmt::Continue => {
                // Use loop context for proper jump target
                let loop_ctx = self
                    .current_loop()
                    .ok_or(super::lowering_core::MirLowerError::ContinueOutsideLoop)?
                    .clone();

                // Emit deferred blocks before continuing loop
                self.emit_deferred_blocks(contract)?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(loop_ctx.continue_target);
                })?;
                Ok(())
            }

            HirStmt::Assert { condition, message } => {
                // Lower the assertion condition
                let cond_reg = self.lower_expr(condition)?;

                // Emit decision probe for assert condition coverage (#674)
                self.emit_decision_probe(cond_reg, 0, 0)?;

                // Get function name for error message (best effort)
                let func_name = self
                    .try_contract_ctx()
                    .map(|ctx| ctx.func_name.clone())
                    .unwrap_or_else(|_| "<unknown>".to_string());

                // Emit contract check instruction with Assertion kind
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ContractCheck {
                        condition: cond_reg,
                        kind: crate::mir::instructions::ContractKind::Assertion,
                        func_name,
                        message: message.clone(),
                    });
                })?;
                Ok(())
            }

            HirStmt::For {
                pattern,
                pattern_local,
                iterable,
                body,
                simd_requested: _simd_requested,
                ..
            } => {
                // Check if this is a range-based for loop (0..n or 0..=n)
                // Range iterables are represented as BuiltinCall("rt_range"/"rt_range_inclusive")
                if let HirExprKind::BuiltinCall { name, args: range_args } = &iterable.kind {
                    if (name == "rt_range" || name == "rt_range_inclusive") && range_args.len() == 2 {
                        let is_inclusive = name == "rt_range_inclusive";
                        return self.lower_for_range(
                            pattern,
                            *pattern_local,
                            &range_args[0],
                            &range_args[1],
                            is_inclusive,
                            body,
                            contract,
                        );
                    }
                }

                // For loops use index-based iteration over collections
                // 1. Evaluate iterable once
                // 2. Get length
                // 3. Loop: check index < len, get element, execute body, increment index

                // Lower the iterable expression
                let collection_reg = self.lower_expr(iterable)?;

                // Normalize the iterable for index-based iteration. Dicts are
                // converted to an array of (key, value) tuples at runtime
                // (rt_for_iterable is a pass-through for everything else).
                // Without this, `rt_array_len(dict)` / `IndexGet(dict, i)`
                // below silently treat the dict handle as an array: the loop
                // body sees nil/garbage items (stage4 SIGSEGV in
                // `desugar_module` iterating `module.functions`).
                let collection_reg = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name("rt_for_iterable"),
                        args: vec![collection_reg],
                    });
                    dest
                })?;

                // Bind the loop variable. Prefer the exact local index that
                // HIR lowering allocated for it (`pattern_local`): the body's
                // `Local(idx)` references that slot, and resolving by NAME is
                // ambiguous — `add_local` appends a fresh slot for every
                // same-named `val`/`var`/loop variable, so both an earlier
                // shadowed binding and a later same-named loop produce
                // duplicate names. First-name-match stored elements into a
                // stale slot while the body read nil from the real one
                // (stage4 10th-site (b): check.spl `for arg in file_args`
                // after `val arg` in the arg-parse loop → "1 of 0 file(s)").
                let pattern_local_index = if let Some(idx) = pattern_local {
                    *idx
                } else {
                    // Fallback for HIR producers that don't track the index
                    // (HIR-level transforms, tests): legacy name search.
                    self.with_func(|func, _| {
                        let num_params = func.params.len();
                        // First check params
                        for (i, param) in func.params.iter().enumerate() {
                            if param.name == *pattern {
                                return i;
                            }
                        }
                        // Then check locals
                        for (i, local) in func.locals.iter().enumerate() {
                            if local.name == *pattern {
                                return num_params + i;
                            }
                        }
                        // Not found - create a new local for the loop variable
                        let index = num_params + func.locals.len();
                        func.locals.push(crate::mir::function::MirLocal {
                            name: pattern.clone(),
                            ty: crate::hir::TypeId::ANY, // Type will be inferred from collection element type
                            kind: crate::mir::effects::LocalKind::Local,
                            is_ghost: false,
                        });
                        index
                    })?
                };

                // Get collection length via rt_array_len call
                let len_reg = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name("rt_array_len"),
                        args: vec![collection_reg],
                    });
                    dest
                })?;

                // Create index register, initialize to 0
                let index_reg = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                    dest
                })?;

                // We need a mutable index, so use a local slot for it
                // Allocate a stack slot for the index
                let index_addr_reg = self.with_func(|func, current_block| {
                    // Add a synthetic local for the index counter
                    let index_local_idx = func.params.len() + func.locals.len();
                    func.locals.push(crate::mir::function::MirLocal {
                        name: format!("__for_index_{}", pattern),
                        ty: crate::hir::TypeId::I64,
                        kind: crate::mir::effects::LocalKind::Local,
                        is_ghost: false,
                    });

                    let addr = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Store {
                        addr,
                        value: index_reg,
                        ty: crate::hir::TypeId::I64,
                    });
                    (addr, index_local_idx)
                })?;
                let (index_addr, index_local_idx) = index_addr_reg;

                // Create blocks (including separate increment block for correct continue behavior)
                let (header_id, body_id, increment_id, exit_id) = self.with_func(|func, current_block| {
                    let header_id = func.new_block();
                    let body_id = func.new_block();
                    let increment_id = func.new_block();
                    let exit_id = func.new_block();

                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(header_id);
                    (header_id, body_id, increment_id, exit_id)
                })?;

                // continue must jump to increment (not header) so the index advances
                self.push_loop(LoopContext {
                    continue_target: increment_id,
                    break_target: exit_id,
                })?;

                // Header: load index, compare with len, branch
                self.set_current_block(header_id)?;
                let cond_reg = self.with_func(|func, current_block| {
                    // Allocate all vregs first
                    let addr = func.new_vreg();
                    let current_idx = func.new_vreg();
                    let cond = func.new_vreg();

                    // Now get the block and emit instructions
                    let block = func.block_mut(current_block).unwrap();

                    // Load current index
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest: current_idx,
                        addr,
                        ty: crate::hir::TypeId::I64,
                    });

                    // Compare index < len
                    block.instructions.push(MirInst::BinOp {
                        dest: cond,
                        op: crate::hir::BinOp::Lt,
                        left: current_idx,
                        right: len_reg,
                    });
                    cond
                })?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Branch {
                        cond: cond_reg,
                        then_block: body_id,
                        else_block: exit_id,
                    };
                })?;

                // Body: get element, store to loop var, execute body, increment index
                self.set_current_block(body_id)?;

                // Determine element type for unboxing after IndexGet
                let element_ty = if let Some(registry) = self.type_registry {
                    if let Some(crate::hir::HirType::Array { element, .. }) = registry.get(iterable.ty) {
                        *element
                    } else {
                        crate::hir::TypeId::ANY
                    }
                } else {
                    crate::hir::TypeId::ANY
                };
                let needs_int_unbox = matches!(
                    element_ty,
                    crate::hir::TypeId::I8
                        | crate::hir::TypeId::I16
                        | crate::hir::TypeId::I32
                        | crate::hir::TypeId::I64
                        | crate::hir::TypeId::U8
                        | crate::hir::TypeId::U16
                        | crate::hir::TypeId::U32
                        | crate::hir::TypeId::U64
                        | crate::hir::TypeId::BOOL
                );
                let needs_float_unbox = matches!(element_ty, crate::hir::TypeId::F32 | crate::hir::TypeId::F64);
                // FR-DRIVER-0002b: narrow after UnboxInt for [u8]/[u16]/[u32]/[i8]/[i16]/[i32]
                // element types so the loop variable's value gets the correct narrow TypeId.
                let narrow_to_signed: Option<(u8, bool)> = match element_ty {
                    crate::hir::TypeId::U8 => Some((8, false)),
                    crate::hir::TypeId::U16 => Some((16, false)),
                    crate::hir::TypeId::U32 => Some((32, false)),
                    crate::hir::TypeId::I8 => Some((8, true)),
                    crate::hir::TypeId::I16 => Some((16, true)),
                    crate::hir::TypeId::I32 => Some((32, true)),
                    _ => None,
                };

                // Load current index and get element
                self.with_func(|func, current_block| {
                    // Allocate all vregs first
                    let addr = func.new_vreg();
                    let current_idx = func.new_vreg();
                    let boxed_idx = func.new_vreg();
                    let raw_element = func.new_vreg();
                    let element = if needs_int_unbox || needs_float_unbox {
                        func.new_vreg()
                    } else {
                        raw_element
                    };
                    // For narrow int element types, UnboxInt -> intermediate i64,
                    // then UnitNarrow -> element so element gets the narrow TypeId.
                    let unboxed_intermediate = if narrow_to_signed.is_some() {
                        func.new_vreg()
                    } else {
                        element
                    };
                    let var_addr = func.new_vreg();

                    // Now get the block and emit instructions
                    let block = func.block_mut(current_block).unwrap();

                    // Load current index
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest: current_idx,
                        addr,
                        ty: crate::hir::TypeId::I64,
                    });

                    // Box the raw i64 index for rt_index_get (expects RuntimeValue)
                    block.instructions.push(MirInst::BoxInt {
                        dest: boxed_idx,
                        value: current_idx,
                    });

                    // Get element via IndexGet (which calls rt_index_get internally)
                    block.instructions.push(MirInst::IndexGet {
                        dest: raw_element,
                        collection: collection_reg,
                        index: boxed_idx,
                    });

                    // Unbox element if it's a native type (rt_index_get returns RuntimeValue)
                    if needs_int_unbox {
                        block.instructions.push(MirInst::UnboxInt {
                            dest: unboxed_intermediate,
                            value: raw_element,
                        });
                        // FR-DRIVER-0002b: narrow to actual element width when needed.
                        if let Some((to_bits, signed)) = narrow_to_signed {
                            block.instructions.push(MirInst::UnitNarrow {
                                dest: element,
                                value: unboxed_intermediate,
                                from_bits: 64,
                                to_bits,
                                signed,
                                overflow: UnitOverflowBehavior::Wrap,
                            });
                        }
                    } else if needs_float_unbox {
                        block.instructions.push(MirInst::UnboxFloat {
                            dest: element,
                            value: raw_element,
                        });
                    }

                    // Store element to loop variable's local
                    block.instructions.push(MirInst::LocalAddr {
                        dest: var_addr,
                        local_index: pattern_local_index,
                    });
                    block.instructions.push(MirInst::Store {
                        addr: var_addr,
                        value: element,
                        ty: element_ty,
                    });
                })?;

                // Execute body statements
                self.emit_runtime_pool_safepoint()?;
                for stmt in body {
                    self.lower_stmt(stmt, contract)?;
                }

                // Body falls through to increment block
                self.finalize_block_jump(increment_id)?;

                // Increment block: increment index, then jump back to header
                self.set_current_block(increment_id)?;
                self.with_func(|func, current_block| {
                    // Allocate all vregs first
                    let addr = func.new_vreg();
                    let current_idx = func.new_vreg();
                    let one = func.new_vreg();
                    let new_idx = func.new_vreg();

                    // Now get the block and emit instructions
                    let block = func.block_mut(current_block).unwrap();

                    // Load current index
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest: current_idx,
                        addr,
                        ty: crate::hir::TypeId::I64,
                    });

                    // Increment
                    block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
                    block.instructions.push(MirInst::BinOp {
                        dest: new_idx,
                        op: crate::hir::BinOp::Add,
                        left: current_idx,
                        right: one,
                    });

                    // Store back
                    block.instructions.push(MirInst::Store {
                        addr,
                        value: new_idx,
                        ty: crate::hir::TypeId::I64,
                    });
                })?;

                self.finalize_block_jump(header_id)?;

                self.pop_loop()?;
                self.set_current_block(exit_id)?;
                Ok(())
            }

            HirStmt::Assume { condition, message } => {
                // Assume is a verification statement similar to assert
                // At runtime, we treat it as an assertion
                let cond_reg = self.lower_expr(condition)?;

                // Emit decision probe for assume condition coverage (#674)
                self.emit_decision_probe(cond_reg, 0, 0)?;

                let func_name = self
                    .try_contract_ctx()
                    .map(|ctx| ctx.func_name.clone())
                    .unwrap_or_else(|_| "<unknown>".to_string());

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ContractCheck {
                        condition: cond_reg,
                        kind: crate::mir::instructions::ContractKind::Assertion,
                        func_name,
                        message: message.clone(),
                    });
                })?;
                Ok(())
            }

            HirStmt::Admit { condition, message } => {
                // Admit is a verification-only statement that admits a fact without proof
                // At runtime, this is a no-op (we trust the admitted fact)
                let _ = condition;
                let _ = message;
                Ok(())
            }

            HirStmt::ProofHint { hint: _ } => {
                // Proof hints are verification-only statements that provide tactic hints to Lean
                // At runtime, this is a no-op
                Ok(())
            }

            HirStmt::Calc { steps: _ } => {
                // Calculational proofs are verification-only statements for Lean calc blocks
                // At runtime, this is a no-op
                Ok(())
            }

            HirStmt::InlineAsm { instructions, volatile } => {
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::InlineAsm {
                        instructions: instructions.clone(),
                        volatile: *volatile,
                    });
                })?;
                Ok(())
            }

            HirStmt::Defer { body } => {
                // Defer statement for RAII/cleanup patterns
                // Push the body onto the defer stack; it will be emitted in LIFO order
                // at scope exit points (return, break, continue, end of function)
                self.push_defer(body.clone())?;
                Ok(())
            }
        }
    }

    /// Check if an expression constructs a Result::Err variant
    ///
    /// This is used to determine whether to emit error postconditions or
    /// normal postconditions when processing a return statement.
    ///
    /// Detection strategies:
    /// 1. Check if it's a Call to a Global("Err") function
    /// 2. Check if the type is a Result enum and look at the construction pattern
    fn is_result_err_construction(&self, expr: &HirExpr) -> bool {
        // Strategy 1: Check if it's a direct call to Err()
        if let HirExprKind::Call { func, args: _ } = &expr.kind {
            if let HirExprKind::Global(name) = &func.kind {
                if name == "Err" {
                    return true;
                }
            }
        }

        // Strategy 2: Check if the type is Result and look up variant info
        if let Some(registry) = self.type_registry {
            if let Some(HirType::Enum { name, variants: _, .. }) = registry.get(expr.ty) {
                // If the type is named "Result", check the expression pattern
                if name == "Result" {
                    // For StructInit, check if the type name contains "Err"
                    if let HirExprKind::StructInit { ty, fields: _ } = &expr.kind {
                        if let Some(HirType::Struct { name: struct_name, .. }) = registry.get(*ty) {
                            return struct_name.contains("Err");
                        }
                    }
                }
            }
        }

        false
    }

    /// Emit drop instructions for all locals in the current function.
    /// Drops are emitted in LIFO order (last declared first) to ensure proper
    /// cleanup ordering, matching Rust's drop semantics.
    ///
    /// This is called before return statements to ensure all locals are properly
    /// cleaned up. For scope-level drops (e.g., block exit), use emit_scope_drops.
    pub(super) fn emit_function_drops(&mut self) -> MirLowerResult<()> {
        // First, collect information about which locals need dropping
        let locals_to_drop: Vec<(usize, crate::hir::TypeId)> = self.with_func(|func, _| {
            let local_base = func.params.len();
            func.locals
                .iter()
                .enumerate()
                .rev() // LIFO order
                .filter_map(|(idx, local)| {
                    // Skip ghost variables (verification-only)
                    if local.is_ghost {
                        return None;
                    }
                    // Skip parameters (not owned by this function)
                    if local.kind.is_parameter() {
                        return None;
                    }
                    Some((local_base + idx, local.ty))
                })
                .collect()
        })?;

        // Now emit drop instructions for each local
        for (local_index, ty) in locals_to_drop {
            self.with_func(|func, current_block| {
                let addr_vreg = func.new_vreg();
                let value_vreg = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();

                // Get address of local
                block.instructions.push(MirInst::LocalAddr {
                    dest: addr_vreg,
                    local_index,
                });

                // Load the value to drop
                block.instructions.push(MirInst::Load {
                    dest: value_vreg,
                    addr: addr_vreg,
                    ty,
                });

                // Emit the drop instruction
                block.instructions.push(MirInst::Drop { value: value_vreg, ty });
            })?;
        }

        Ok(())
    }

    /// Emit EndScope marker for a local going out of scope.
    /// This provides lifetime information for static analysis but is a no-op at runtime.
    pub(super) fn emit_end_scope(&mut self, local_index: usize) -> MirLowerResult<()> {
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::EndScope { local_index });
        })
    }

    /// Lower a for-range loop (e.g., `for i in 0..n`) as a counter-based loop.
    /// This avoids creating a range collection object and uses direct integer comparison.
    #[allow(clippy::too_many_arguments)] // reason: mirrors HirStmt::For fields; loop-var index must travel with the pattern name
    fn lower_for_range(
        &mut self,
        pattern: &str,
        pattern_local: Option<usize>,
        start_expr: &crate::hir::HirExpr,
        end_expr: &crate::hir::HirExpr,
        inclusive: bool,
        body: &[crate::hir::HirStmt],
        contract: Option<&HirContract>,
    ) -> MirLowerResult<()> {
        use crate::hir::BinOp;
        use crate::mir::MirInst;

        let loop_ty = range_counter_type(start_expr.ty, end_expr.ty);

        // Lower start and end expressions
        let start_reg = self.lower_expr(start_expr)?;
        let end_reg = self.lower_expr(end_expr)?;

        // Bind the loop variable: prefer the exact HIR-allocated local index
        // (see HirStmt::For binder above — name search is ambiguous with
        // shadowed or sequential same-named loop variables).
        let pattern_local_index = if let Some(idx) = pattern_local {
            self.with_func(|func, _| {
                let num_params = func.params.len();
                if idx >= num_params {
                    if let Some(local) = func.locals.get_mut(idx - num_params) {
                        local.ty = loop_ty;
                    }
                }
                idx
            })?
        } else {
            self.with_func(|func, _| {
                let num_params = func.params.len();
                for (i, param) in func.params.iter().enumerate() {
                    if param.name == pattern {
                        return i;
                    }
                }
                for (i, local) in func.locals.iter().enumerate() {
                    if local.name == pattern {
                        if let Some(local) = func.locals.get_mut(i) {
                            local.ty = loop_ty;
                        }
                        return num_params + i;
                    }
                }
                let index = num_params + func.locals.len();
                func.locals.push(crate::mir::function::MirLocal {
                    name: pattern.to_string(),
                    ty: loop_ty,
                    kind: crate::mir::effects::LocalKind::Local,
                    is_ghost: false,
                });
                index
            })?
        };

        // Store start value to the loop variable
        self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: pattern_local_index,
            });
            block.instructions.push(MirInst::Store {
                addr,
                value: start_reg,
                ty: loop_ty,
            });
        })?;

        // Create blocks
        let (header_id, body_id, exit_id) = self.with_func(|func, current_block| {
            let header_id = func.new_block();
            let body_id = func.new_block();
            let exit_id = func.new_block();
            let block = func.block_mut(current_block).unwrap();
            block.terminator = Terminator::Jump(header_id);
            (header_id, body_id, exit_id)
        })?;

        self.push_loop(LoopContext {
            continue_target: header_id,
            break_target: exit_id,
        })?;

        // Header: load loop var, compare with end, branch
        self.set_current_block(header_id)?;
        let cond_reg = self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let current_val = func.new_vreg();
            let cond = func.new_vreg();

            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: pattern_local_index,
            });
            block.instructions.push(MirInst::Load {
                dest: current_val,
                addr,
                ty: loop_ty,
            });

            // For exclusive range: i < end; for inclusive: i <= end
            let op = if inclusive { BinOp::LtEq } else { BinOp::Lt };
            block.instructions.push(MirInst::BinOp {
                dest: cond,
                op,
                left: current_val,
                right: end_reg,
            });
            cond
        })?;

        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.terminator = Terminator::Branch {
                cond: cond_reg,
                then_block: body_id,
                else_block: exit_id,
            };
        })?;

        // Body: execute body, then increment
        self.set_current_block(body_id)?;

        // Execute body statements
        self.emit_runtime_pool_safepoint()?;
        for stmt in body {
            self.lower_stmt(stmt, contract)?;
        }

        // Increment loop variable
        self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let current_val = func.new_vreg();
            let one = func.new_vreg();
            let new_val = func.new_vreg();

            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: pattern_local_index,
            });
            block.instructions.push(MirInst::Load {
                dest: current_val,
                addr,
                ty: loop_ty,
            });
            block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
            block.instructions.push(MirInst::BinOp {
                dest: new_val,
                op: BinOp::Add,
                left: current_val,
                right: one,
            });
            block.instructions.push(MirInst::Store {
                addr,
                value: new_val,
                ty: loop_ty,
            });
        })?;

        self.finalize_block_jump(header_id)?;

        self.pop_loop()?;
        self.set_current_block(exit_id)?;
        Ok(())
    }
}

fn range_counter_type(start_ty: TypeId, end_ty: TypeId) -> TypeId {
    match end_ty {
        TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64 => end_ty,
        TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 => end_ty,
        _ => match start_ty {
            TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64 => start_ty,
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 => start_ty,
            _ => TypeId::I64,
        },
    }
}
