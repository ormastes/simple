//! Collection expression lowering: Tuple, Array, VecLiteral, Dict, ArrayRepeat.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, HirExprKind, HirType, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_tuple_expr(&mut self, elements: &[HirExpr]) -> MirLowerResult<VReg> {
        let mut elem_regs = Vec::new();
        for elem in elements {
            let reg = self.lower_expr(elem)?;
            // Box native-typed elements so they become RuntimeValues for the tuple
            let needs_int_boxing = matches!(
                elem.ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            );
            let needs_float_boxing = matches!(elem.ty, TypeId::F32 | TypeId::F64);
            let needs_bool_boxing = elem.ty == TypeId::BOOL;
            if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                let boxed = if elem.ty == TypeId::U64 {
                    self.box_u64_runtime_value(reg)?
                } else if needs_bool_boxing {
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

    pub(super) fn lower_array_expr(&mut self, elements: &[HirExpr], outer_ty: TypeId) -> MirLowerResult<VReg> {
        // Detect u8 byte-array: elements typed U8, OR outer declared type is [u8] (elements may
        // be untyped I64 integer literals even when the declaration says [u8]).
        let outer_is_u8_array = self
            .type_registry
            .and_then(|tr| tr.get(outer_ty))
            .is_some_and(|t| matches!(t, HirType::Array { element, .. } if *element == TypeId::U8));
        let outer_is_u64_array = self
            .type_registry
            .and_then(|tr| tr.get(outer_ty))
            .is_some_and(|t| matches!(t, HirType::Array { element, .. } if *element == TypeId::U64));
        if elements.is_empty() && (outer_is_u8_array || outer_is_u64_array) {
            let capacity_reg = self.with_func(|func, current_block| {
                let reg = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ConstInt { dest: reg, value: 16 });
                reg
            })?;
            let target = if outer_is_u8_array {
                CallTarget::from_name("rt_byte_array_new")
            } else {
                CallTarget::from_name("rt_array_new_with_cap_u64")
            };
            return self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    target,
                    args: vec![capacity_reg],
                });
                dest
            });
        }
        if !elements.is_empty() && (elements.iter().all(|elem| elem.ty == TypeId::U8) || outer_is_u8_array) {
            let capacity = elements.len() as i64;
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
            for elem in elements {
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
            return Ok(array_reg);
        }

        if !elements.is_empty() && (elements.iter().all(|elem| elem.ty == TypeId::U64) || outer_is_u64_array) {
            let capacity = elements.len() as i64;
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
                    target: CallTarget::from_name("rt_array_new_with_cap_u64"),
                    args: vec![capacity_reg],
                });
                dest
            })?;
            for elem in elements {
                let value_reg = self.lower_expr(elem)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_typed_words_u64_push"),
                        args: vec![array_reg, value_reg],
                    });
                    dest
                })?;
            }
            return Ok(array_reg);
        }

        let has_function_elements = elements.iter().any(|elem| {
            matches!(elem.kind, HirExprKind::Lambda { .. })
                || self
                    .type_registry
                    .and_then(|tr| tr.get(elem.ty))
                    .is_some_and(|ty| matches!(ty, HirType::Function { .. }))
        }) || self.type_registry.and_then(|tr| tr.get(outer_ty)).is_some_and(|ty| {
            matches!(
                ty,
                HirType::Array { element, .. }
                    if self
                        .type_registry
                        .and_then(|tr| tr.get(*element))
                        .is_some_and(|element_ty| matches!(element_ty, HirType::Function { .. }))
            )
        });

        if has_function_elements {
            let outer_function_element = self
                .type_registry
                .and_then(|tr| tr.get(outer_ty))
                .and_then(|ty| match ty {
                    HirType::Array { element, .. } => Some(*element),
                    _ => None,
                })
                .and_then(|element| self.type_registry.and_then(|tr| tr.get(element)))
                .is_some_and(|element_ty| matches!(element_ty, HirType::Function { .. }));
            let capacity = elements.len() as i64;
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
                    target: CallTarget::from_name("rt_array_new"),
                    args: vec![capacity_reg],
                });
                dest
            })?;
            for elem in elements {
                let reg = self.lower_expr(elem)?;
                let elem_is_function = outer_function_element
                    || matches!(elem.kind, HirExprKind::Lambda { .. })
                    || self
                        .type_registry
                        .and_then(|tr| tr.get(elem.ty))
                        .is_some_and(|ty| matches!(ty, HirType::Function { .. }));
                let needs_int_boxing = matches!(
                    elem.ty,
                    TypeId::I8
                        | TypeId::I16
                        | TypeId::I32
                        | TypeId::I64
                        | TypeId::U8
                        | TypeId::U16
                        | TypeId::U32
                        | TypeId::U64
                );
                let needs_float_boxing = matches!(elem.ty, TypeId::F32 | TypeId::F64);
                let needs_bool_boxing = elem.ty == TypeId::BOOL;
                let pushed = if elem_is_function {
                    reg
                } else if needs_bool_boxing {
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
                } else if elem.ty == TypeId::U64 {
                    self.box_u64_runtime_value(reg)?
                } else if needs_int_boxing {
                    self.with_func(|func, current_block| {
                        let boxed = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BoxInt {
                            dest: boxed,
                            value: reg,
                        });
                        boxed
                    })?
                } else {
                    reg
                };
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_array_push"),
                        args: vec![array_reg, pushed],
                    });
                    dest
                })?;
            }
            return Ok(array_reg);
        }

        let mut elem_regs = Vec::new();
        for elem in elements {
            let reg = self.lower_expr(elem)?;
            // Box native-typed elements so they become RuntimeValues for the array
            let needs_int_boxing = matches!(
                elem.ty,
                TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
            );
            let needs_float_boxing = matches!(elem.ty, TypeId::F32 | TypeId::F64);
            let needs_bool_boxing = elem.ty == TypeId::BOOL;
            if needs_int_boxing || needs_float_boxing || needs_bool_boxing {
                let boxed = if elem.ty == TypeId::U64 {
                    self.box_u64_runtime_value(reg)?
                } else if needs_bool_boxing {
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

    pub(super) fn lower_vec_literal_expr(&mut self, elements: &[HirExpr]) -> MirLowerResult<VReg> {
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

    /// Tag a native integer VReg into a RuntimeValue when `ty` is an integer
    /// type, mirroring the array-literal element boxing above. Non-integer
    /// operands (strings, heap handles, floats, bools) pass through unchanged.
    fn box_int_operand(&mut self, reg: VReg, ty: TypeId) -> MirLowerResult<VReg> {
        if ty == TypeId::U64 {
            return self.box_u64_runtime_value(reg);
        }
        let needs_int_boxing = matches!(
            ty,
            TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
        );
        if !needs_int_boxing {
            return Ok(reg);
        }
        self.with_func(|func, current_block| {
            let boxed = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::BoxInt {
                dest: boxed,
                value: reg,
            });
            boxed
        })
    }

    pub(super) fn lower_dict_expr(&mut self, pairs: &[(HirExpr, HirExpr)]) -> MirLowerResult<VReg> {
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

        // Insert each pair.
        //
        // `rt_dict_set(dict, key, value)` takes TAGGED RuntimeValues: it hashes
        // the key with `value_hash` and compares with `rt_value_eq`. Every dict
        // READ path already tags an integer key (`d[k]` lowers to BoxInt +
        // rt_index_get; `d.contains_key(k)` / `d.get(k)` wrap_value the key into
        // rt_box_int), so a dict LITERAL that stored the RAW native integer
        // hashed into a different bucket and every later read missed:
        // `{1: 10, 2: 20}` gave `d[2] == nil` and `d.contains_key(1) == false`
        // under the Cranelift JIT, while the interpreter — which boxes on both
        // sides — was correct. Only key 0 survived, because `0 << 3 == 0`.
        // Box on the WRITE side to match the reads and the runtime contract.
        //
        // VALUES, mirroring keys (task: dict_value_read_returns_tag_boxed_word).
        // The stored VALUE had an analogous but NOT identical asymmetry: a raw
        // (unboxed) integer value whose low 3 bits are 0 reads back as `v >> 3`
        // on the Cranelift JIT, so `{"a": 8}` yielded `d["a"] == 1` while
        // `{"a": 1}.get("a")` was "accidentally correct" (`1` has non-zero low
        // bits, so `UnboxInt`'s tag check — see `MirInst::UnboxInt` codegen,
        // Task #123 — left it passed through raw instead of shifting). Boxing
        // the value here is NOT a self-contained fix on its own: `d[k]`
        // unboxes its result (see `lower_index_expr`), but until now the
        // `Dict.get` lowering emitted NO UnboxInt at all, so boxing the value
        // without also unboxing `.get()` would turn `{"a": 1}.get("a")` from
        // accidentally-correct `1` into wrongly-boxed `8`. Both sides now land
        // together: this box here, plus the `.get()` route through
        // `lower_index_expr` in `lowering_expr_method.rs` (search
        // `receiver_is_dict`). Floats/bools/strings remain untouched (follow-up).
        for (key_expr, value_expr) in pairs {
            let key_reg = self.lower_expr(key_expr)?;
            let key_reg = self.box_int_operand(key_reg, key_expr.ty)?;
            let value_reg = self.lower_expr(value_expr)?;
            let value_reg = self.box_int_operand(value_reg, value_expr.ty)?;
            let insert_target = CallTarget::from_name("rt_dict_set");
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

    pub(super) fn lower_array_repeat_expr(&mut self, value: &HirExpr, count: &HirExpr) -> MirLowerResult<VReg> {
        // Array repeat: [value; count] - creates array with count copies of value
        let raw_value_reg = self.lower_expr(value)?;
        let count_reg = self.lower_expr(count)?;
        let value_reg = if value.ty == TypeId::U64 {
            self.box_u64_runtime_value(raw_value_reg)?
        } else if value.ty == TypeId::U32 {
            self.with_func(|func, current_block| {
                let boxed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::BoxInt {
                    dest: boxed,
                    value: raw_value_reg,
                });
                boxed
            })?
        } else {
            raw_value_reg
        };

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
