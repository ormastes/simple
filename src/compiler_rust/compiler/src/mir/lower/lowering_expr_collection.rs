//! Collection expression lowering: Tuple, Array, VecLiteral, Dict, ArrayRepeat.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{BinOp, HirExpr, HirExprKind, HirType, TypeId, UnaryOp};
use crate::mir::blocks::Terminator;
use crate::mir::effects::{CallTarget, LocalKind};
use crate::mir::function::MirLocal;
use crate::mir::instructions::{MirInst, VReg};

/// Above this many identical scalar elements an array literal is built by one
/// repeat call instead of one operand per element.
pub(super) const ARRAY_LITERAL_REPEAT_MIN: usize = 256;

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
            if !self.array_push_returns_header && elements.len() > ARRAY_LITERAL_REPEAT_MIN {
                let first = &elements[0];
                if Self::repeat_scalar_element(first) && elements.iter().all(|elem| elem == first) {
                    let count_expr = HirExpr {
                        kind: HirExprKind::Integer(elements.len() as i64),
                        ty: TypeId::I64,
                    };
                    return self.lower_u8_array_repeat_expr(first, &count_expr);
                }
            }
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
            let mut array_reg = self.with_func(|func, current_block| {
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
                let pushed = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_typed_bytes_u8_push"),
                        args: vec![array_reg, value_reg],
                    });
                    dest
                })?;
                if self.array_push_returns_header {
                    array_reg = pushed;
                }
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
            let mut array_reg = self.with_func(|func, current_block| {
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
                let pushed = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_typed_words_u64_push"),
                        args: vec![array_reg, value_reg],
                    });
                    dest
                })?;
                if self.array_push_returns_header {
                    array_reg = pushed;
                }
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
            let mut array_reg = self.with_func(|func, current_block| {
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
                let pushed_dest = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_array_push"),
                        args: vec![array_reg, pushed],
                    });
                    dest
                })?;
                if self.array_push_returns_header {
                    array_reg = pushed_dest;
                }
            }
            return Ok(array_reg);
        }

        // A large literal of one repeated side-effect-free scalar -- what HIR
        // produces for `[NAME; 72200]` -- becomes a single rt_array_repeat.
        // Lowering it element by element put ~144K instructions into one
        // function (font_renderer.spl `_kern_ascii_vals`), and Cranelift
        // regalloc spent ~344 s on that one `__module_init_dynamic` per run.
        // The array is identical: every slot holds the same boxed scalar the
        // per-element path would have produced, and loading a literal, local
        // or global once instead of N times is unobservable. Only this
        // generic branch is affected; byte, u64-word and function arrays
        // returned above.
        if elements.len() > ARRAY_LITERAL_REPEAT_MIN {
            let first = &elements[0];
            if Self::repeat_scalar_element(first) && elements.iter().all(|elem| elem == first) {
                // Same boxing per type as the per-element loop below.
                let reg = self.lower_expr(first)?;
                let boxed = if matches!(first.ty, TypeId::F32 | TypeId::F64) {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BoxFloat { dest, value: reg });
                        dest
                    })?
                } else if first.ty == TypeId::BOOL {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: CallTarget::from_name("rt_value_bool"),
                            args: vec![reg],
                        });
                        dest
                    })?
                } else {
                    self.box_int_operand(reg, first.ty)?
                };
                let count = elements.len() as i64;
                return self.with_func(|func, current_block| {
                    let count_reg = func.new_vreg();
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt {
                        dest: count_reg,
                        value: count,
                    });
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_array_repeat"),
                        args: vec![boxed, count_reg],
                    });
                    dest
                });
            }
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

    /// Scalar element whose single evaluation is indistinguishable from N
    /// evaluations: a numeric/bool literal, a negated numeric literal, or a
    /// plain local/global read of a numeric/bool type.
    pub(super) fn repeat_scalar_element(elem: &HirExpr) -> bool {
        let scalar_ty = matches!(
            elem.ty,
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
        );
        if !scalar_ty {
            return false;
        }
        match &elem.kind {
            HirExprKind::Integer(_)
            | HirExprKind::Float(_)
            | HirExprKind::Bool(_)
            | HirExprKind::Local(_)
            | HirExprKind::Global(_) => true,
            HirExprKind::Unary {
                op: UnaryOp::Neg,
                operand,
            } => matches!(operand.kind, HirExprKind::Integer(_) | HirExprKind::Float(_)),
            _ => false,
        }
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
        // `receiver_is_dict`).
        //
        // FLOAT values take the same lossless box as array/tuple elements.
        // A raw f64 bit-pattern whose low 3 bits alias TAG_FLOAT (0b010) was
        // read back by `UnboxFloat` -> `rt_value_as_float` as a legacy inline
        // float, shifting the payload and zeroing the low 3 mantissa bits
        // (`{"k": 0.1}` read as 0.09999999999999998,
        // seed_jit_dict_f64_literal_value_read_loses_low_mantissa_bits_2026-11-27).
        // Bool VALUE tagging remains a follow-up (the raw 0/1 word currently
        // round-trips through the integer readers).
        for (key_expr, value_expr) in pairs {
            let key_reg = self.lower_expr(key_expr)?;
            // Boolean keys must match tagged membership/index reads. Preserve
            // the existing write ABI for every other key type, including floats.
            let key_reg = if key_expr.ty == TypeId::BOOL {
                self.box_arg_for_any_param(key_reg, key_expr)?
            } else {
                self.box_int_operand(key_reg, key_expr.ty)?
            };
            let value_reg = self.lower_expr(value_expr)?;
            let value_reg = if matches!(value_expr.ty, TypeId::F32 | TypeId::F64) {
                self.with_func(|func, current_block| {
                    let boxed = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BoxFloat {
                        dest: boxed,
                        value: value_reg,
                    });
                    boxed
                })?
            } else {
                self.box_int_operand(value_reg, value_expr.ty)?
            };
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

    fn is_zero_byte_hir_expr(expr: &HirExpr) -> bool {
        match &expr.kind {
            HirExprKind::Integer(n) => (*n & 0xFF) == 0,
            HirExprKind::Cast { expr, .. } => Self::is_zero_byte_hir_expr(expr),
            _ => false,
        }
    }

    fn clamp_non_negative_repeat_count(&mut self, count: &HirExpr, count_reg: VReg) -> MirLowerResult<VReg> {
        if let HirExprKind::Integer(n) = &count.kind {
            if *n <= 0 {
                return self.with_func(|func, current_block| {
                    let zero = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest: zero, value: 0 });
                    zero
                });
            }
            return Ok(count_reg);
        }
        if Self::is_unsigned_int_type(count.ty) {
            return Ok(count_reg);
        }

        // Normalize narrow signed widths (i8/i16/i32) to i64 before storing
        // into the signed i64 clamp slot.
        let count_i64 = if matches!(count.ty, TypeId::I8 | TypeId::I16 | TypeId::I32) {
            self.with_func(|func, current_block| {
                let cast = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Cast {
                    dest: cast,
                    source: count_reg,
                    from_ty: count.ty,
                    to_ty: TypeId::I64,
                });
                cast
            })?
        } else {
            self.unbox_scalar_for_raw_slot(TypeId::I64, count.ty, count_reg)?
        };

        let temp_local_index = self.with_func(|func, _| {
            let index = func.params.len() + func.locals.len();
            func.locals.push(MirLocal {
                name: format!("$u8_repeat_count_{}", index),
                ty: TypeId::I64,
                kind: LocalKind::Local,
                is_ghost: false,
            });
            index
        })?;
        let (temp_addr, cond_reg, signed_count_reg) = self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let signed_count = func.new_vreg();
            let zero = func.new_vreg();
            let cond = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: temp_local_index,
            });
            block.instructions.push(MirInst::Store {
                addr,
                value: count_i64,
                ty: TypeId::I64,
            });
            // Load from a TypeId::I64 slot so BinOp::Gt uses signed comparison.
            block.instructions.push(MirInst::Load {
                dest: signed_count,
                addr,
                ty: TypeId::I64,
            });
            block.instructions.push(MirInst::ConstInt { dest: zero, value: 0 });
            block.instructions.push(MirInst::BinOp {
                dest: cond,
                op: BinOp::Gt,
                left: signed_count,
                right: zero,
            });
            (addr, cond, signed_count)
        })?;
        let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
            let then_id = func.new_block();
            let else_id = func.new_block();
            let merge_id = func.new_block();
            let block = func.block_mut(current_block).unwrap();
            block.terminator = Terminator::Branch {
                cond: cond_reg,
                then_block: then_id,
                else_block: else_id,
            };
            (then_id, else_id, merge_id)
        })?;

        self.set_current_block(then_id)?;
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Store {
                addr: temp_addr,
                value: signed_count_reg,
                ty: TypeId::I64,
            });
        })?;
        self.finalize_block_jump(merge_id)?;

        self.set_current_block(else_id)?;
        self.with_func(|func, current_block| {
            let zero = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConstInt { dest: zero, value: 0 });
            block.instructions.push(MirInst::Store {
                addr: temp_addr,
                value: zero,
                ty: TypeId::I64,
            });
        })?;
        self.finalize_block_jump(merge_id)?;

        self.set_current_block(merge_id)?;
        self.with_func(|func, current_block| {
            let clamped = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Load {
                dest: clamped,
                addr: temp_addr,
                ty: TypeId::I64,
            });
            clamped
        })
    }

    /// Lower a `[u8]` repeat `[value; count]` into a `BYTE_PACKED` runtime
    /// array so copies (`rt_array_copy`) and appends (`rt_typed_bytes_u8_push`)
    /// keep 1-byte backing storage instead of 8-byte tagged slots.
    pub(super) fn lower_u8_array_repeat_expr(&mut self, value: &HirExpr, count: &HirExpr) -> MirLowerResult<VReg> {
        let raw_value_reg = self.lower_expr(value)?;
        let raw_value_reg = self.unbox_scalar_for_raw_slot(TypeId::U8, value.ty, raw_value_reg)?;
        let count_reg = self.lower_expr(count)?;
        let clamped_count = self.clamp_non_negative_repeat_count(count, count_reg)?;
        let arr_reg = self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Call {
                dest: Some(dest),
                target: CallTarget::from_name("rt_byte_array_new_len"),
                args: vec![clamped_count],
            });
            dest
        })?;
        if !Self::is_zero_byte_hir_expr(value) {
            self.with_func(|func, current_block| {
                let zero = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ConstInt { dest: zero, value: 0 });
                block.instructions.push(MirInst::Call {
                    dest: None,
                    target: CallTarget::from_name("rt_array_fill_span"),
                    args: vec![arr_reg, zero, clamped_count, raw_value_reg],
                });
            })?;
        }
        Ok(arr_reg)
    }

    pub(super) fn lower_array_repeat_expr(
        &mut self,
        value: &HirExpr,
        count: &HirExpr,
        outer_ty: TypeId,
    ) -> MirLowerResult<VReg> {
        let outer_is_u8_array = self
            .type_registry
            .and_then(|tr| tr.get(outer_ty))
            .is_some_and(|t| matches!(t, HirType::Array { element, .. } if *element == TypeId::U8));
        if !self.array_push_returns_header && (value.ty == TypeId::U8 || outer_is_u8_array) {
            return self.lower_u8_array_repeat_expr(value, count);
        }
        // Array repeat: [value; count] - creates array with count copies of value
        let raw_value_reg = self.lower_expr(value)?;
        let count_reg = self.lower_expr(count)?;
        let value_reg = self.box_value_as_runtime(raw_value_reg, value.ty)?;

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
