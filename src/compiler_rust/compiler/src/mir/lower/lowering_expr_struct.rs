//! Struct/field/index expression lowering: StructInit, FieldAccess, Index.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, HirType, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

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

    pub(super) fn lower_index_expr(
        &mut self,
        receiver: &HirExpr,
        index: &HirExpr,
        expr_ty: TypeId,
    ) -> MirLowerResult<VReg> {
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
                    TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
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
            expr_ty,
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
        let needs_float_unbox = matches!(expr_ty, TypeId::F32 | TypeId::F64);

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
}
