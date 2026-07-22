//! Built-in call expression lowering (rt_* and print/println family).

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, HirType, TypeId};
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, UnitOverflowBehavior, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_builtin_call_expr(
        &mut self,
        name: &str,
        args: &[HirExpr],
        expr_ty: TypeId,
    ) -> MirLowerResult<VReg> {
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

            // If the expected type is known to be a native int/float, unbox now.
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
                // FR-DRIVER-0002b: narrow after UnboxInt so the dest VReg gets
                // stamped with the correct narrow TypeId (U8/U16/U32/I8/I16/I32).
                let (to_bits, signed_opt): (u8, Option<bool>) = match expr_ty {
                    TypeId::U8 => (8, Some(false)),
                    TypeId::U16 => (16, Some(false)),
                    TypeId::U32 => (32, Some(false)),
                    TypeId::I8 => (8, Some(true)),
                    TypeId::I16 => (16, Some(true)),
                    TypeId::I32 => (32, Some(true)),
                    // U64/I64/BOOL: keep i64-typed unboxed VReg unchanged.
                    _ => (0, None),
                };
                return self.with_func(|func, current_block| {
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
                });
            } else if expr_ty == TypeId::F64 {
                // Enum f64 payloads are stored RAW in the enum's 64-bit payload
                // slot: every construct site (Some/Ok/Err and user-enum
                // single-field, `box_enum_payload_if_needed` / the EnumWith
                // path) excludes floats from BoxInt/BoxFloat, so the slot holds
                // the verbatim IEEE-754 bit pattern and `rt_enum_payload`
                // returns that raw i64. Emitting `UnboxFloat` here would apply
                // the tagged-float mask `(bits >> 3) << 3`, zeroing the low 3
                // mantissa bits and corrupting any f64 with nonzero low bits
                // (e.g. 0.1) — the enum_payload f64 precision leak. `UnboxFloat`
                // must stay masked for genuinely BoxFloat'd values (array/dict
                // f64 in `lowering_expr_collection`), so it cannot be de-masked
                // globally.
                //
                // Instead reinterpret the raw bits with an F64->F64 self-cast:
                //   - cranelift: the float->float cast bitcasts an i64-typed
                //     source to f64 (see codegen `compile_cast`), the lossless
                //     reinterpret with no mask;
                //   - LLVM: `Cast` stamps the dest F64 in the type map while the
                //     tagged-i64 ABI coerces i64->f64 via `bitcast` at each typed
                //     use (`coerce_value_to_type`); without this stamp the value
                //     stays i64 and the `==` compare / return mis-handles it;
                //   - MIR interpreter: identity.
                return self.with_func(|func, current_block| {
                    let casted = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Cast {
                        dest: casted,
                        source: raw_result,
                        from_ty: TypeId::F64,
                        to_ty: TypeId::F64,
                    });
                    casted
                });
            } else if needs_float_unbox {
                // F32 enum payloads keep the existing tagged path. Their
                // construct-side representation (f32 stored via a separate
                // coercion) is a distinct concern from the f64 precision leak
                // and is out of scope here.
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

            if arg.ty == TypeId::U64 {
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: CallTarget::from_name("rt_raw_u64_to_string"),
                        args: vec![arg_reg],
                    });
                    dest
                });
            }

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

        // Runtime numeric kernels that return a scalar pack the result as RuntimeValue.
        // Unbox them when the HIR expects a native float.
        if matches!(
            name,
            "rt_numeric_dot_f32"
                | "rt_numeric_sum_f32"
                | "rt_numeric_min_f32"
                | "rt_numeric_max_f32"
                | "rt_numeric_sum_f64"
                | "rt_numeric_dot_f64"
                | "rt_numeric_xor_sum_u64"
        ) && matches!(expr_ty, TypeId::F32 | TypeId::F64)
        {
            let mut arg_regs = Vec::new();
            for arg in args {
                arg_regs.push(self.lower_expr(arg)?);
            }

            return self.with_func(|func, current_block| {
                let raw_result = func.new_vreg();
                let unboxed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(raw_result),
                    target: CallTarget::from_name(name),
                    args: arg_regs,
                });
                block.instructions.push(MirInst::UnboxFloat {
                    dest: unboxed,
                    value: raw_result,
                });
                unboxed
            });
        }

        if name == "rt_numeric_xor_sum_u64" && matches!(expr_ty, TypeId::U64) {
            let mut arg_regs = Vec::new();
            for arg in args {
                arg_regs.push(self.lower_expr(arg)?);
            }

            return self.with_func(|func, current_block| {
                let raw_result = func.new_vreg();
                let unboxed = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(raw_result),
                    target: CallTarget::from_name(name),
                    args: arg_regs,
                });
                block.instructions.push(MirInst::UnboxInt {
                    dest: unboxed,
                    value: raw_result,
                });
                unboxed
            });
        }

        // Special handling for print/println/eprint/eprintln - box numeric args
        if matches!(
            name,
            "print" | "println" | "eprint" | "eprintln" | "print_raw" | "eprint_raw" | "dprint"
        ) {
            let mut boxed_arg_regs = Vec::new();
            for arg in args {
                let arg_reg = self.lower_expr(arg)?;
                // BoxInt/BoxFloat pack a value into the 61-bit tagged-int
                // RuntimeValue payload (`(value << 3) | TAG_INT`); any i64/u64
                // magnitude outside that range silently loses its top bits
                // (e.g. i64::MAX boxes to -1, 2^62 boxes to 0 -- see
                // doc/08_tracking/bug/stress_f02_i64_boxing_truncation_2026-07-17.md).
                // u64 already routes around this via rt_raw_u64_to_string;
                // I64 needs the signed counterpart for the same reason.
                if arg.ty == TypeId::U64 || arg.ty == TypeId::I64 {
                    let raw_to_string_fn = if arg.ty == TypeId::U64 {
                        "rt_raw_u64_to_string"
                    } else {
                        "rt_raw_i64_to_string"
                    };
                    let stringified = self.with_func(|func, current_block| {
                        let stringified = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(stringified),
                            target: CallTarget::from_name(raw_to_string_fn),
                            args: vec![arg_reg],
                        });
                        stringified
                    })?;
                    boxed_arg_regs.push(stringified);
                    continue;
                }
                // P1 fix (2026-07-22): flat-optional (i64?/bool?/f64?/...) print
                // args. `T?` lowers to `HirType::Pointer { inner: T }` and is
                // represented at runtime as a RAW payload -- the bare inner
                // value, or the nil sentinel (rt_core_nil() == 3) -- never a
                // tagged RuntimeValue (no BoxInt/BoxFloat/(v<<3)|TAG_INT
                // wrapping is ever applied to it; see the obstacle report for
                // the full site-enumeration this was scoped down from). Generic
                // print (rt_println_value) assumes every argument is already a
                // validly-tagged RuntimeValue and misreads these raw low bits
                // as tag bits (payload 1 -> "nil", 2 -> "0.0", 4 ->
                // "<value:0x4>", ...). Route through a raw-to-string bypass the
                // same way the I64/U64 case above does. NOTE: a genuine payload
                // equal to the nil sentinel (3) is indistinguishable from real
                // nil at this representation -- documented limitation, not
                // fixed here (full tagging was scoped out as a 7-site,
                // hot-path, bootstrap-only-engine change). See
                // doc/08_tracking/bug/interp_index_of_digit_leading_literal_2026-07-22.md.
                if let Some(registry) = self.type_registry {
                    if let Some(HirType::Pointer { inner, .. }) = registry.get(arg.ty) {
                        let inner = *inner;
                        let opt_to_string_fn = if inner == TypeId::BOOL {
                            Some("rt_opt_bool_to_string")
                        } else if matches!(
                            inner,
                            TypeId::I64
                                | TypeId::U64
                                | TypeId::I32
                                | TypeId::U32
                                | TypeId::I16
                                | TypeId::U16
                                | TypeId::U8
                        ) {
                            Some("rt_opt_i64_to_string")
                        } else if matches!(inner, TypeId::F32 | TypeId::F64) {
                            Some("rt_opt_f64_to_string")
                        } else {
                            None
                        };
                        if let Some(fn_name) = opt_to_string_fn {
                            let stringified = self.with_func(|func, current_block| {
                                let stringified = func.new_vreg();
                                let block = func.block_mut(current_block).unwrap();
                                block.instructions.push(MirInst::Call {
                                    dest: Some(stringified),
                                    target: CallTarget::from_name(fn_name),
                                    args: vec![arg_reg],
                                });
                                stringified
                            })?;
                            boxed_arg_regs.push(stringified);
                            continue;
                        }
                        // Other inner types (heap types: text?, struct?, ...)
                        // fall through unchanged -- those already carry a real
                        // heap-boxed RuntimeEnum, not a raw payload, and
                        // rt_println_value already handles them correctly
                        // (confirmed: text? print was clean in every probe).
                    }
                }
                // I64/U64 are handled above via the raw-to-string bypass (both can
                // exceed the 61-bit boxed-int range); this list only covers widths
                // that always fit.
                let needs_int_boxing =
                    matches!(arg.ty, TypeId::I16 | TypeId::I32 | TypeId::U8 | TypeId::U16 | TypeId::U32);
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
}
