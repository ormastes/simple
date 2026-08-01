//! Basic operation instruction compilation.
//!
//! Handles simple operations: copy, cast, unary operations, and spread.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::{TypeId, UnaryOp};
use crate::mir::VReg;

use super::helpers::adapted_call;
use super::{InstrContext, InstrResult};

/// Compile Copy instruction: copies a value from one register to another
pub fn compile_copy<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    dest: VReg,
    src: VReg,
) -> InstrResult<()> {
    let val = match ctx.vreg_values.get(&src) {
        Some(&v) => v,
        None => return Err(format!("Copy: source vreg {:?} not found", src)),
    };
    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile Cast instruction: type conversion between numeric types
pub fn compile_cast<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
    from_ty: TypeId,
    to_ty: TypeId,
) -> InstrResult<()> {
    let src_val = match ctx.vreg_values.get(&source) {
        Some(&v) => v,
        None => return Err(format!("Cast: source vreg {:?} not found", source)),
    };

    if from_ty == TypeId::ANY {
        match to_ty {
            TypeId::I8
            | TypeId::I16
            | TypeId::I32
            | TypeId::I64
            | TypeId::U8
            | TypeId::U16
            | TypeId::U32
            | TypeId::U64 => {
                let unwrap_id = ctx
                    .runtime_funcs
                    .get("rt_value_as_int")
                    .copied()
                    .ok_or_else(|| "Cast: runtime function rt_value_as_int not declared".to_string())?;
                let unwrap_ref = ctx.module.declare_func_in_func(unwrap_id, builder.func);
                let unwrapped = adapted_call(builder, unwrap_ref, &[src_val]);
                let raw_i64 = builder.inst_results(unwrapped)[0];
                let target_ty = match to_ty {
                    TypeId::I8 | TypeId::U8 => types::I8,
                    TypeId::I16 | TypeId::U16 => types::I16,
                    TypeId::I32 | TypeId::U32 => types::I32,
                    _ => types::I64,
                };
                let narrowed = if target_ty == types::I64 {
                    raw_i64
                } else {
                    builder.ins().ireduce(target_ty, raw_i64)
                };
                ctx.vreg_values.insert(dest, narrowed);
                return Ok(());
            }
            _ => {}
        }
    }

    // Determine source and target types.
    //
    // Defensive: MIR lowering occasionally annotates a float-producing
    // expression with an integer source type (e.g. `(a.to_f32() * opacity).to_u32()`
    // in browser_engine `_apply_opacity`, where the multiplication's result vreg
    // is left typed as i32/u32 even though codegen emitted `fmul` and the runtime
    // value is f32). Honor the actual cranelift value type so we don't dispatch a
    // bare `ireduce` on a float — the verifier rejects that with
    // "ireduce.i32 vN: arg type f32 failed to satisfy type set".
    let actual_src_ty = builder.func.dfg.value_type(src_val);
    let actual_is_float = actual_src_ty == types::F32 || actual_src_ty == types::F64;
    let is_from_float = from_ty == TypeId::F64 || from_ty == TypeId::F32 || actual_is_float;
    let is_to_float = to_ty == TypeId::F64 || to_ty == TypeId::F32;
    let to_int_width = match to_ty {
        TypeId::I8 | TypeId::U8 => Some(types::I8),
        TypeId::I16 | TypeId::U16 => Some(types::I16),
        TypeId::I32 | TypeId::U32 => Some(types::I32),
        TypeId::I64 | TypeId::U64 => Some(types::I64),
        _ => None,
    };
    let to_signed = matches!(to_ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);
    let from_signed = matches!(from_ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);

    let val = if from_ty == TypeId::STRING && to_int_width.is_some() {
        // `int(text_expr)` (and any other integer-cast of a `text` value) used
        // to load the first byte of the string data and use its char code as
        // the result (e.g. int("42") == 52, the ASCII code of '4') instead of
        // parsing the decimal digits. Task #100 — Rust-side sibling of task
        // #94's `cranelift_codegen_adapter.spl` fix (`cl_translate_cast`):
        // route through a runtime parser instead.
        //
        // Task #118 correction: this used to call `rt_string_to_int`, which
        // was believed (per stale comments here and in
        // `cranelift_codegen_adapter.spl`) to be strtoll-based/leading-prefix
        // lenient like its C (`runtime_native.c`) and self-hosted
        // (`simple_core/core_string.spl`) namesakes. It is NOT: the Rust-native
        // `simple-runtime` crate's `rt_string_to_int` (runtime/src/value/collections.rs)
        // does a *strict whole-string* `str::parse::<i64>()` and returns 0 on
        // any partial match, so `int("4.2")` silently produced 0 instead of 4.
        // `rt_string_to_int` is left strict on purpose — it also backs
        // `.to_int()`/`.parse_int()`/`to_i64()` method calls (see
        // closures_structs.rs / calls.rs), which reject partial matches.
        // `int(text_expr)` now routes through the sibling
        // `rt_string_to_int_lenient` (added for task #118), which does the
        // canonical leading-digit-run parse ("4.2" -> 4, "abc"/"" -> 0),
        // matching eval_builtins.spl's `eval_int_parse_lenient` (flat-AST
        // interpreter) and interpreter_call/builtins.rs's `parse_int_lenient`
        // (seed tree-walk interpreter). `src_val` here is already the boxed
        // string RuntimeValue, so no rt_string_new re-boxing is needed.
        // Not every JIT compilation pre-populates `rt_string_to_int_lenient` in
        // `ctx.runtime_funcs` (unlike `rt_string_len`/`rt_string_data` used
        // below) — fall back to declaring it fresh, mirroring the existing
        // `.to_int()` method-call lowering in closures_structs.rs.
        let string_to_int_id = if let Some(&fid) = ctx.runtime_funcs.get("rt_string_to_int_lenient") {
            fid
        } else if let Some(&fid) = ctx.func_ids.get("rt_string_to_int_lenient") {
            fid
        } else {
            let mut sig = cranelift_codegen::ir::Signature::new(crate::codegen::shared::platform_call_conv());
            sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
            sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
            let fid = ctx
                .module
                .declare_function("rt_string_to_int_lenient", cranelift_module::Linkage::Import, &sig)
                .map_err(|e| e.to_string())?;
            ctx.func_ids.insert("rt_string_to_int_lenient".to_string(), fid);
            fid
        };
        let string_to_int_ref = ctx.module.declare_func_in_func(string_to_int_id, builder.func);
        let parse_call = adapted_call(builder, string_to_int_ref, &[src_val]);
        let parsed_i64 = builder.inst_results(parse_call)[0];

        match to_int_width {
            Some(types::I8) => builder.ins().ireduce(types::I8, parsed_i64),
            Some(types::I16) => builder.ins().ireduce(types::I16, parsed_i64),
            Some(types::I32) => builder.ins().ireduce(types::I32, parsed_i64),
            _ => parsed_i64,
        }
    } else if from_ty == TypeId::STRING && is_to_float {
        let string_len_id = ctx.runtime_funcs["rt_string_len"];
        let string_len_ref = ctx.module.declare_func_in_func(string_len_id, builder.func);
        let len_call = adapted_call(builder, string_len_ref, &[src_val]);
        let len_val = builder.inst_results(len_call)[0];

        let string_data_id = ctx.runtime_funcs["rt_string_data"];
        let string_data_ref = ctx.module.declare_func_in_func(string_data_id, builder.func);
        let data_call = adapted_call(builder, string_data_ref, &[src_val]);
        let data_ptr = builder.inst_results(data_call)[0];

        let zero = builder.ins().iconst(types::I64, 0);
        let has_data = builder.ins().icmp(
            cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan,
            len_val,
            zero,
        );
        let first_byte = builder.ins().load(types::I8, MemFlags::new(), data_ptr, 0);
        let widened_first_byte = builder.ins().uextend(types::I64, first_byte);
        let code_i64 = builder.ins().select(has_data, widened_first_byte, zero);

        if to_ty == TypeId::F32 {
            builder.ins().fcvt_from_uint(types::F32, code_i64)
        } else {
            builder.ins().fcvt_from_uint(types::F64, code_i64)
        }
    } else if is_from_float && !is_to_float {
        // Float to int conversion. The HIR `from` type can disagree with the
        // actual cranelift value: call results arrive as plain ints in the
        // tagged i64 ABI even when HIR typed the expression as float (e.g.
        // `floor(x + 0.5)` mis-typed f32 — verifier rejected fcvt_to_sint on
        // an i64 arg, 2026-06-12). Dispatch on the actual value type.
        let src_ty = builder.func.dfg.value_type(src_val);
        let widened = if src_ty.is_int() {
            if src_ty.bits() < 64 {
                if to_signed {
                    builder.ins().sextend(types::I64, src_val)
                } else {
                    builder.ins().uextend(types::I64, src_val)
                }
            } else {
                src_val
            }
        } else if to_signed {
            builder.ins().fcvt_to_sint(types::I64, src_val)
        } else {
            builder.ins().fcvt_to_uint(types::I64, src_val)
        };
        match to_int_width {
            Some(types::I8) => builder.ins().ireduce(types::I8, widened),
            Some(types::I16) => builder.ins().ireduce(types::I16, widened),
            Some(types::I32) => builder.ins().ireduce(types::I32, widened),
            _ => widened,
        }
    } else if !is_from_float && is_to_float {
        // Int to float conversion
        if from_signed {
            builder.ins().fcvt_from_sint(types::F64, src_val)
        } else {
            builder.ins().fcvt_from_uint(types::F64, src_val)
        }
    } else if is_from_float && is_to_float {
        // Float to float (F32 <-> F64). Dispatch on the ACTUAL cranelift value
        // type, not the MIR annotation: values that crossed a block boundary or
        // arrived through the tagged-i64 ABI are i64 bit patterns of the
        // promoted f64 (see ensure_i64), so a bare fpromote/fdemote on them
        // fails the verifier (engine3d mat4_* after the _sin/_cos wrappers
        // became inlinable, 2026-07-03).
        let target = if to_ty == TypeId::F32 { types::F32 } else { types::F64 };
        let as_float = if builder.func.dfg.value_type(src_val) == types::I64 {
            builder.ins().bitcast(types::F64, MemFlags::new(), src_val)
        } else {
            src_val
        };
        let src_float_ty = builder.func.dfg.value_type(as_float);
        if src_float_ty == target {
            as_float
        } else if target == types::F64 {
            builder.ins().fpromote(types::F64, as_float)
        } else {
            builder.ins().fdemote(types::F32, as_float)
        }
    } else if let Some(target_ty) = to_int_width {
        let src_ty = builder.func.dfg.value_type(src_val);
        if src_ty == target_ty {
            src_val
        } else {
            match target_ty {
                types::I8 | types::I16 | types::I32 => builder.ins().ireduce(target_ty, src_val),
                types::I64 => match src_ty {
                    types::I8 | types::I16 | types::I32 => {
                        if from_signed {
                            builder.ins().sextend(types::I64, src_val)
                        } else {
                            builder.ins().uextend(types::I64, src_val)
                        }
                    }
                    _ => src_val,
                },
                _ => src_val,
            }
        }
    } else {
        // Default: just copy the value
        src_val
    };

    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile UnaryOp instruction: negation, logical not, bitwise not
pub fn compile_unary_op<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    op: UnaryOp,
    operand: VReg,
) -> InstrResult<()> {
    let mut val = match ctx.vreg_values.get(&operand) {
        Some(&v) => v,
        None => return Err(format!("UnaryOp: operand vreg {:?} not found", operand)),
    };
    // Cross-block float operands arrive as i64 bit patterns of the promoted
    // f64 (see ensure_i64); reinterpret before classifying, mirroring
    // compile_binop's reinterpret_f64.
    if matches!(
        ctx.vreg_types.get(&operand).copied(),
        Some(TypeId::F64) | Some(TypeId::F32)
    ) && builder.func.dfg.value_type(val) == types::I64
    {
        val = builder.ins().bitcast(types::F64, MemFlags::new(), val);
    }
    let val_type = builder.func.dfg.value_type(val);
    let val_is_float = val_type == types::F32 || val_type == types::F64;
    let result = match op {
        UnaryOp::Neg => {
            if val_is_float {
                builder.ins().fneg(val)
            } else {
                builder.ins().ineg(val)
            }
        }
        UnaryOp::Not => {
            if val_is_float {
                let zero_f = if val_type == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().f64const(0.0)
                };
                builder
                    .ins()
                    .fcmp(cranelift_codegen::ir::condcodes::FloatCC::Equal, val, zero_f)
            } else {
                builder
                    .ins()
                    .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::Equal, val, 0)
            }
        }
        UnaryOp::BitNot => builder.ins().bnot(val),
    };
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile Spread instruction: spreads a collection (currently just copies the value)
pub fn compile_spread<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
) -> InstrResult<()> {
    let source_val = match ctx.vreg_values.get(&source) {
        Some(&v) => v,
        None => return Err(format!("Spread: source vreg {:?} not found", source)),
    };
    ctx.vreg_values.insert(dest, source_val);
    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use crate::codegen::Codegen;
    use crate::hir::TypeId;
    use crate::mir::{BlockId, MirFunction, MirInst, MirModule, Terminator};
    use simple_parser::ast::Visibility;

    /// Helper: build a single-function MIR module and AOT-compile it.
    /// The `build` closure pushes instructions into block 0 and returns the
    /// VReg to use as the return value.  Compilation exercises the Cranelift
    /// verifier — if any instruction emits invalid IR (e.g. `ireduce` on an
    /// f32 operand) `aot_ok` returns false.
    fn aot_ok(name: &str, build: impl FnOnce(&mut MirFunction) -> crate::mir::VReg) -> bool {
        let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
        let ret = build(&mut func);
        func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));
        let mut module = MirModule::new();
        module.functions.push(func);
        Codegen::new()
            .expect("Codegen::new failed")
            .compile_module(&module)
            .is_ok()
    }

    /// Regression test for the ireduce-on-f32 verifier failure.
    ///
    /// Pattern:  `ConstFloat` produces an f64 Cranelift value; a `Cast F64→F32`
    /// narrows it to f32.  Then a second `Cast` whose *HIR annotation* says
    /// `U32 → U32` (as MIR lowering incorrectly stamps when a float-producing
    /// expression chain is annotated with the surrounding integer type) arrives
    /// with an f32 operand.
    ///
    /// Bug (HEAD): `is_from_float` is false (annotation says U32), so the code
    /// falls into the int→int branch and emits `ireduce.i32 <f32-value>` —
    /// the Cranelift verifier rejects this.
    ///
    /// Fix (working tree): the `actual_src_ty` check detects the real f32 and
    /// routes through `fcvt_to_uint.i64` + `ireduce.i32`, which is valid IR.
    #[test]
    fn cast_f32_value_annotated_as_u32_compiles() {
        assert!(
            aot_ok("cast_f32_as_u32", |f| {
                let vreg_f64 = f.new_vreg();
                let vreg_f32 = f.new_vreg();
                // This vreg holds an f32 Cranelift value, but the subsequent
                // Cast annotation will claim it is U32 (the MIR bug scenario).
                let vreg_u32_wrong_ann = f.new_vreg();
                // Coerce to i64 for the function return (which is I64)
                let vreg_ret = f.new_vreg();

                let block = f.block_mut(BlockId(0)).unwrap();
                // Step 1: produce an f64 constant
                block.instructions.push(MirInst::ConstFloat {
                    dest: vreg_f64,
                    value: 0.7,
                });
                // Step 2: demote to f32  (annotation correct: F64→F32)
                block.instructions.push(MirInst::Cast {
                    dest: vreg_f32,
                    source: vreg_f64,
                    from_ty: TypeId::F64,
                    to_ty: TypeId::F32,
                });
                // Step 3: Cast annotated as U32→U32 but ACTUAL VALUE is f32.
                // This is the exact MIR lowering mistake that triggered the
                // ireduce-on-f32 verifier failure in _apply_opacity.
                block.instructions.push(MirInst::Cast {
                    dest: vreg_u32_wrong_ann,
                    source: vreg_f32,
                    from_ty: TypeId::U32, // wrong annotation — real value is f32
                    to_ty: TypeId::U32,
                });
                // Step 4: Cast the result to I64 for the I64 return slot.
                block.instructions.push(MirInst::Cast {
                    dest: vreg_ret,
                    source: vreg_u32_wrong_ann,
                    from_ty: TypeId::U32,
                    to_ty: TypeId::I64,
                });
                vreg_ret
            }),
            "ireduce on f32 operand must not reach the verifier"
        );
    }

    /// Complementary: Cast annotated as I32→I32 but actual value is f32
    /// (signed variant of the same bug — `fcvt_to_sint` path).
    #[test]
    fn cast_f32_value_annotated_as_i32_compiles() {
        assert!(
            aot_ok("cast_f32_as_i32", |f| {
                let vreg_f64 = f.new_vreg();
                let vreg_f32 = f.new_vreg();
                let vreg_i32_wrong_ann = f.new_vreg();
                let vreg_ret = f.new_vreg();

                let block = f.block_mut(BlockId(0)).unwrap();
                block.instructions.push(MirInst::ConstFloat {
                    dest: vreg_f64,
                    value: 1.5,
                });
                block.instructions.push(MirInst::Cast {
                    dest: vreg_f32,
                    source: vreg_f64,
                    from_ty: TypeId::F64,
                    to_ty: TypeId::F32,
                });
                // Bug scenario: annotated I32→I32 but holds f32
                block.instructions.push(MirInst::Cast {
                    dest: vreg_i32_wrong_ann,
                    source: vreg_f32,
                    from_ty: TypeId::I32, // wrong annotation
                    to_ty: TypeId::I32,
                });
                block.instructions.push(MirInst::Cast {
                    dest: vreg_ret,
                    source: vreg_i32_wrong_ann,
                    from_ty: TypeId::I32,
                    to_ty: TypeId::I64,
                });
                vreg_ret
            }),
            "ireduce on f32 operand (signed path) must not reach the verifier"
        );
    }

    /// Sanity: correct Cast F32→U32 (annotation matches actual type) also compiles.
    #[test]
    fn cast_f32_to_u32_correct_annotation_compiles() {
        assert!(aot_ok("cast_f32_u32_correct", |f| {
            let vreg_f64 = f.new_vreg();
            let vreg_f32 = f.new_vreg();
            let vreg_u32 = f.new_vreg();
            let vreg_ret = f.new_vreg();

            let block = f.block_mut(BlockId(0)).unwrap();
            block.instructions.push(MirInst::ConstFloat {
                dest: vreg_f64,
                value: 255.9,
            });
            block.instructions.push(MirInst::Cast {
                dest: vreg_f32,
                source: vreg_f64,
                from_ty: TypeId::F64,
                to_ty: TypeId::F32,
            });
            block.instructions.push(MirInst::Cast {
                dest: vreg_u32,
                source: vreg_f32,
                from_ty: TypeId::F32, // correct annotation
                to_ty: TypeId::U32,
            });
            block.instructions.push(MirInst::Cast {
                dest: vreg_ret,
                source: vreg_u32,
                from_ty: TypeId::U32,
                to_ty: TypeId::I64,
            });
            vreg_ret
        }));
    }

    /// Sanity: correct Cast F32→I32 (annotation matches actual type) also compiles.
    #[test]
    fn cast_f32_to_i32_correct_annotation_compiles() {
        assert!(aot_ok("cast_f32_i32_correct", |f| {
            let vreg_f64 = f.new_vreg();
            let vreg_f32 = f.new_vreg();
            let vreg_i32 = f.new_vreg();
            let vreg_ret = f.new_vreg();

            let block = f.block_mut(BlockId(0)).unwrap();
            block.instructions.push(MirInst::ConstFloat {
                dest: vreg_f64,
                value: -3.7,
            });
            block.instructions.push(MirInst::Cast {
                dest: vreg_f32,
                source: vreg_f64,
                from_ty: TypeId::F64,
                to_ty: TypeId::F32,
            });
            block.instructions.push(MirInst::Cast {
                dest: vreg_i32,
                source: vreg_f32,
                from_ty: TypeId::F32, // correct annotation
                to_ty: TypeId::I32,
            });
            block.instructions.push(MirInst::Cast {
                dest: vreg_ret,
                source: vreg_i32,
                from_ty: TypeId::I32,
                to_ty: TypeId::I64,
            });
            vreg_ret
        }));
    }
}
