// Core instruction compilation helpers: binary operations, builtin I/O, and interpreter calls.

use cranelift_codegen::ir::{
    condcodes::{FloatCC, IntCC},
    types, InstBuilder, MemFlags,
};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::{BinOp, TypeId};
use crate::mir::VReg;

use super::helpers::{
    adapted_call, call_runtime_1, call_runtime_1_void, call_runtime_2, call_runtime_2_void, call_runtime_3,
    call_runtime_4, create_string_constant, declare_named_bytes,
};
use super::{InstrContext, InstrResult};

/// Look up whether a VReg holds a signed integer.
///
/// Returns:
/// - `Some(true)` for signed integer types (`i8`, `i16`, `i32`, `i64`).
/// - `Some(false)` for unsigned integer types (`u8`, `u16`, `u32`, `u64`).
/// - `None` if the VReg has no entry in `vreg_types` (unknown), or the
///   stored type is not an integer (bool, floats, structs, strings, etc.).
///
/// Used by integer widening, shifts, division, comparisons, and mixed
/// integer/float coercion to preserve source signedness.
pub fn vreg_is_signed<M: Module>(ctx: &InstrContext<'_, M>, v: VReg) -> Option<bool> {
    let ty = ctx.vreg_types.get(&v).copied()?;
    match ty {
        TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 => Some(true),
        TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64 => Some(false),
        _ => None,
    }
}

fn vreg_is_native_equality_scalar<M: Module>(ctx: &InstrContext<'_, M>, v: VReg) -> bool {
    matches!(
        ctx.vreg_types.get(&v).copied(),
        Some(
            TypeId::I8
                | TypeId::I16
                | TypeId::I32
                | TypeId::I64
                | TypeId::U8
                | TypeId::U16
                | TypeId::U32
                | TypeId::U64
                | TypeId::BOOL
        )
    )
}

fn interp_call_returns_f64(func_name: &str) -> bool {
    matches!(
        func_name,
        "rt_torch_torchtensor_sum"
            | "rt_torch_torchtensor_norm"
            | "rt_torch_torchtensor_mean"
            | "rt_torch_torchtensor_max"
            | "rt_torch_torchtensor_min"
            | "rt_torch_torchtensor_std"
            | "rt_torch_torchtensor_var"
            | "rt_torch_nn_mse_loss"
            | "rt_torch_nn_cross_entropy"
            | "rt_torch_nn_binary_cross_entropy"
            | "rt_torch_nn_nll_loss"
    )
}

fn interp_call_keeps_boxed_result(func_name: &str) -> bool {
    matches!(func_name, "rt_torch_torchtensor_shape")
}

fn vreg_is_text<M: Module>(ctx: &InstrContext<'_, M>, v: VReg) -> bool {
    matches!(ctx.vreg_types.get(&v).copied(), Some(TypeId::STRING))
}

fn compile_text_eq_with_identity_fast_path<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    lhs: cranelift_codegen::ir::Value,
    rhs: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    call_runtime_2(ctx, builder, "rt_string_eq", lhs, rhs)
}

/// Ensure a value is i64, extending smaller integer types and bitcasting floats if needed.
/// This is necessary because some values (e.g., from SFFI functions returning i32 or
/// float constants) may not be i64 even though runtime functions expect i64.
///
/// Uses `uextend` (zero-extend) for backward compatibility with the pre-FR-0002b
/// behavior — most non-shift call sites are widening runtime / SFFI return values
/// where zero-extending is either correct or indistinguishable.
fn ensure_i64(builder: &mut FunctionBuilder, val: cranelift_codegen::ir::Value) -> cranelift_codegen::ir::Value {
    ensure_i64_typed(builder, val, None)
}

/// Ensure a value is i64, picking `sextend`/`uextend` based on signedness hint.
///
/// FR-DRIVER-0002b: when `signed` is:
/// - `Some(true)`  → emit `sextend` (preserves sign bit of narrow signed ints).
/// - `Some(false)` → emit `uextend` (preserves magnitude of narrow unsigned ints).
/// - `None`        → emit `uextend` (backward-compat default).
///
/// Consumers that have a VReg in scope should call this via `ensure_i64_vreg` so
/// the signedness flows directly from `vreg_types`.
fn ensure_i64_typed(
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    signed: Option<bool>,
) -> cranelift_codegen::ir::Value {
    let val_type = builder.func.dfg.value_type(val);
    match val_type {
        types::I8 | types::I16 | types::I32 => {
            if signed == Some(true) {
                builder.ins().sextend(types::I64, val)
            } else {
                builder.ins().uextend(types::I64, val)
            }
        }
        types::F64 => builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val),
        types::F32 => {
            let promoted = builder.ins().fpromote(types::F64, val);
            builder
                .ins()
                .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), promoted)
        }
        _ => val,
    }
}

/// VReg-aware `ensure_i64`: looks up signedness from `vreg_types` and dispatches
/// between `sextend` and `uextend`. Shift-right LHS path uses `default_signed=true`
/// (Simple's integer types default signed); other callers pass `false` to preserve
/// the existing uextend-when-unknown behavior.
fn ensure_i64_vreg<M: Module>(
    ctx: &InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    vreg: VReg,
    default_signed: bool,
) -> cranelift_codegen::ir::Value {
    let signed = vreg_is_signed(ctx, vreg).or(Some(default_signed));
    ensure_i64_typed(builder, val, signed)
}

/// Coerce both operands to matching types for binary operations.
/// If either is float, convert the other to float too.
/// If both are int, ensure both are i64.
fn coerce_binop_operands(
    ctx: &InstrContext<'_, impl Module>,
    builder: &mut FunctionBuilder,
    lhs: cranelift_codegen::ir::Value,
    rhs: cranelift_codegen::ir::Value,
    left_vreg: VReg,
    right_vreg: VReg,
) -> (cranelift_codegen::ir::Value, cranelift_codegen::ir::Value, bool) {
    let lhs_type = builder.func.dfg.value_type(lhs);
    let rhs_type = builder.func.dfg.value_type(rhs);
    let lhs_is_float = lhs_type == types::F32 || lhs_type == types::F64;
    let rhs_is_float = rhs_type == types::F32 || rhs_type == types::F64;

    if lhs_is_float && rhs_is_float {
        // Both float - promote F32 to F64 if mismatched
        let (l, r) = if lhs_type == types::F32 && rhs_type == types::F64 {
            (builder.ins().fpromote(types::F64, lhs), rhs)
        } else if lhs_type == types::F64 && rhs_type == types::F32 {
            (lhs, builder.ins().fpromote(types::F64, rhs))
        } else {
            (lhs, rhs)
        };
        (l, r, true)
    } else if lhs_is_float && !rhs_is_float {
        // lhs float, rhs int - convert rhs to float
        let target_float = if lhs_type == types::F32 { types::F32 } else { types::F64 };
        let signed = vreg_is_signed(ctx, right_vreg);
        let rhs_i64 = ensure_i64_typed(builder, rhs, signed);
        let rhs_f = if signed == Some(false) {
            builder.ins().fcvt_from_uint(target_float, rhs_i64)
        } else {
            builder.ins().fcvt_from_sint(target_float, rhs_i64)
        };
        (lhs, rhs_f, true)
    } else if !lhs_is_float && rhs_is_float {
        // lhs int, rhs float - convert lhs to float
        let target_float = if rhs_type == types::F32 { types::F32 } else { types::F64 };
        let signed = vreg_is_signed(ctx, left_vreg);
        let lhs_i64 = ensure_i64_typed(builder, lhs, signed);
        let lhs_f = if signed == Some(false) {
            builder.ins().fcvt_from_uint(target_float, lhs_i64)
        } else {
            builder.ins().fcvt_from_sint(target_float, lhs_i64)
        };
        (lhs_f, rhs, true)
    } else {
        // Both int - ensure both are i64
        (ensure_i64(builder, lhs), ensure_i64(builder, rhs), false)
    }
}

pub(crate) fn compile_binop<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    op: BinOp,
    lhs: cranelift_codegen::ir::Value,
    rhs: cranelift_codegen::ir::Value,
    left_vreg: VReg,
    right_vreg: VReg,
) -> InstrResult<cranelift_codegen::ir::Value> {
    // FR-DRIVER-0002b: capture signedness from the LHS VReg *before* coercion
    // may widen/promote the value. Only the LHS signedness matters for picking
    // sshr vs ushr and sextend vs uextend on shift operations — the RHS is a
    // non-negative shift count and always widens uextend.
    let lhs_signed = vreg_is_signed(ctx, left_vreg);

    // A cross-block f64 operand is carried through an i64-typed Cranelift
    // Variable (cross-block VRegs are declared i64; `def_var` bitcasts f64->i64
    // to fit). When such a value reaches a binop it arrives as a Cranelift I64
    // value, so `coerce_binop_operands` — which infers float-ness from the
    // Cranelift value type — would misclassify it as an integer and emit
    // integer `iadd`/`imul`/… on the raw f64 bits (garbage; e.g. `a + b` on two
    // f64 params returned 0). `vreg_types` (built from MIR) still records the
    // true F64 type, so reinterpret the bits back to f64 here before coercion.
    let reinterpret_f64 = |builder: &mut FunctionBuilder, v: cranelift_codegen::ir::Value, vreg: VReg| {
        // F32 included: cross-block f32 values are carried as the bit pattern
        // of their PROMOTED f64 (see ensure_i64), so the same bitcast applies.
        if matches!(
            ctx.vreg_types.get(&vreg).copied(),
            Some(TypeId::F64) | Some(TypeId::F32)
        ) && builder.func.dfg.value_type(v) == types::I64
        {
            builder
                .ins()
                .bitcast(types::F64, cranelift_codegen::ir::MemFlags::new(), v)
        } else {
            v
        }
    };
    let lhs = reinterpret_f64(builder, lhs, left_vreg);
    let rhs = reinterpret_f64(builder, rhs, right_vreg);

    // FR-DRIVER-0002b: preserve the pre-coerce Values so the ShiftRight arm
    // can re-widen with the right extension. `coerce_binop_operands` calls
    // `ensure_i64` which unconditionally `uextend`s narrow ints; for a signed
    // i32 `-16`, that clears the sign bit before `sshr` ever runs, giving
    // `2147483640` instead of `-8`. Routing ShiftRight around the coerce
    // preserves the narrow original so `ensure_i64_typed(..., Some(true))`
    // can emit `sextend`.
    let pre_lhs = lhs;
    let pre_rhs = rhs;
    let pre_lhs_is_int = !matches!(builder.func.dfg.value_type(pre_lhs), types::F32 | types::F64);
    let pre_rhs_is_int = !matches!(builder.func.dfg.value_type(pre_rhs), types::F32 | types::F64);

    // Coerce operands to matching types (handles mixed int/float)
    let (lhs, rhs, is_float) = coerce_binop_operands(ctx, builder, lhs, rhs, left_vreg, right_vreg);
    let lhs_type = builder.func.dfg.value_type(lhs);

    let val = match op {
        BinOp::Add => {
            if is_float {
                builder.ins().fadd(lhs, rhs)
            } else {
                builder.ins().iadd(lhs, rhs)
            }
        }
        BinOp::Sub => {
            if is_float {
                builder.ins().fsub(lhs, rhs)
            } else {
                builder.ins().isub(lhs, rhs)
            }
        }
        BinOp::Mul => {
            if is_float {
                builder.ins().fmul(lhs, rhs)
            } else {
                builder.ins().imul(lhs, rhs)
            }
        }
        BinOp::Div => {
            if is_float {
                builder.ins().fdiv(lhs, rhs)
            } else if lhs_signed == Some(false) {
                builder.ins().udiv(lhs, rhs)
            } else {
                builder.ins().sdiv(lhs, rhs)
            }
        }
        BinOp::Mod => {
            if is_float {
                // Float modulo: a - floor(a/b) * b
                let div = builder.ins().fdiv(lhs, rhs);
                let floored = builder.ins().floor(div);
                let prod = builder.ins().fmul(floored, rhs);
                builder.ins().fsub(lhs, prod)
            } else {
                if lhs_signed == Some(false) {
                    builder.ins().urem(lhs, rhs)
                } else {
                    builder.ins().srem(lhs, rhs)
                }
            }
        }
        BinOp::BitAnd => {
            // Bitwise ops need integer operands
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().band(li, ri)
        }
        BinOp::BitOr => {
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().bor(li, ri)
        }
        BinOp::BitXor => {
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().bxor(li, ri)
        }
        BinOp::ShiftLeft => {
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().ishl(li, ri)
        }
        BinOp::ShiftRight => {
            // FR-DRIVER-0002b: dispatch sshr / ushr by LHS signedness.
            //
            // - Signed LHS (i8/i16/i32/i64, or unknown — Simple integers default
            //   signed): widen via `sextend` to preserve the sign bit into i64,
            //   then emit `sshr` (arithmetic shift right).
            // - Unsigned LHS (u8/u16/u32/u64): widen via `uextend` (zero-fill
            //   top bits) and emit `ushr` (logical shift right) so high-bit-set
            //   values (e.g. `0x80000000u32 >> 1`) do not leak the sign bit
            //   from an implicit `sshr`.
            //
            // The shift count (RHS) is always widened via `uextend` — shift
            // counts are non-negative.
            //
            // We widen from the *pre-coerce* values to preserve the narrow
            // original so `sextend` still sees the sign bit. After
            // `coerce_binop_operands`, `lhs` has already been `uextend`ed.
            let use_signed = lhs_signed.unwrap_or(true);
            if std::env::var("FR_DRIVER_0002B_TRACE").is_ok() {
                let lhs_ty = ctx.vreg_types.get(&left_vreg).copied();
                eprintln!(
                    "[shr-dispatch] left_vreg={:?} vreg_ty={:?} lhs_signed={:?} use_signed={}",
                    left_vreg, lhs_ty, lhs_signed, use_signed
                );
            }
            let li = if pre_lhs_is_int {
                ensure_i64_typed(builder, pre_lhs, Some(use_signed))
            } else {
                lhs
            };
            let ri = if pre_rhs_is_int {
                ensure_i64_typed(builder, pre_rhs, Some(false))
            } else {
                rhs
            };
            if use_signed {
                builder.ins().sshr(li, ri)
            } else {
                builder.ins().ushr(li, ri)
            }
        }
        BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
            if is_float {
                // Use native float comparison
                let cc = match op {
                    BinOp::Lt => FloatCC::LessThan,
                    BinOp::Gt => FloatCC::GreaterThan,
                    BinOp::LtEq => FloatCC::LessThanOrEqual,
                    BinOp::GtEq => FloatCC::GreaterThanOrEqual,
                    _ => unreachable!(),
                };
                let cmp_i8 = builder.ins().fcmp(cc, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else if vreg_is_text(ctx, left_vreg) && vreg_is_text(ctx, right_vreg) {
                // P0 fix (2026-07-22): text ordering compare. Mirrors the
                // vreg_is_text fast path BinOp::Eq already has just below
                // (compile_text_eq_with_identity_fast_path / rt_string_eq) --
                // previously only Eq/NotEq special-cased text operands here;
                // Lt/Gt/LtEq/GtEq fell straight into the raw-integer icmp arm
                // below, comparing string HANDLE/pointer values instead of
                // content (e.g. `"foo" < "bar"` was address-dependent, not
                // alphabetical). rt_text_cmp_any (runtime_native.c) returns a
                // strcmp-style signed result; compare that against 0 with the
                // requested predicate. See
                // doc/08_tracking/bug/sspec_test_path_false_green_undercount_2026-07-20.md.
                let cmp = call_runtime_2(ctx, builder, "rt_text_cmp_any", lhs, rhs);
                let zero = builder.ins().iconst(types::I64, 0);
                let cc = match op {
                    BinOp::Lt => IntCC::SignedLessThan,
                    BinOp::Gt => IntCC::SignedGreaterThan,
                    BinOp::LtEq => IntCC::SignedLessThanOrEqual,
                    BinOp::GtEq => IntCC::SignedGreaterThanOrEqual,
                    _ => unreachable!(),
                };
                let cmp_i8 = builder.ins().icmp(cc, cmp, zero);
                ensure_i64(builder, cmp_i8)
            } else {
                // Native integer comparison. Works correctly for raw untagged
                // integers (which is what native codegen uses). String ordering
                // via < > operators is handled by the vreg_is_text arm above.
                let use_unsigned = lhs_signed == Some(false) || vreg_is_signed(ctx, right_vreg) == Some(false);
                let lhs = ensure_i64_typed(builder, pre_lhs, Some(!use_unsigned));
                let rhs = ensure_i64_typed(builder, pre_rhs, Some(!use_unsigned));
                let cc = match (op, use_unsigned) {
                    (BinOp::Lt, true) => IntCC::UnsignedLessThan,
                    (BinOp::Gt, true) => IntCC::UnsignedGreaterThan,
                    (BinOp::LtEq, true) => IntCC::UnsignedLessThanOrEqual,
                    (BinOp::GtEq, true) => IntCC::UnsignedGreaterThanOrEqual,
                    (BinOp::Lt, false) => IntCC::SignedLessThan,
                    (BinOp::Gt, false) => IntCC::SignedGreaterThan,
                    (BinOp::LtEq, false) => IntCC::SignedLessThanOrEqual,
                    (BinOp::GtEq, false) => IntCC::SignedGreaterThanOrEqual,
                    _ => unreachable!(),
                };
                let cmp_i8 = builder.ins().icmp(cc, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            }
        }
        BinOp::Eq => {
            if is_float {
                // Use native float equality
                let cmp_i8 = builder.ins().fcmp(FloatCC::Equal, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else if vreg_is_text(ctx, left_vreg) && vreg_is_text(ctx, right_vreg) {
                compile_text_eq_with_identity_fast_path(ctx, builder, lhs, rhs)
            } else if vreg_is_native_equality_scalar(ctx, left_vreg) && vreg_is_native_equality_scalar(ctx, right_vreg)
            {
                let use_unsigned =
                    vreg_is_signed(ctx, left_vreg) == Some(false) || vreg_is_signed(ctx, right_vreg) == Some(false);
                let lhs = ensure_i64_typed(builder, lhs, Some(!use_unsigned));
                let rhs = ensure_i64_typed(builder, rhs, Some(!use_unsigned));
                let cmp_i8 = builder.ins().icmp(IntCC::Equal, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else {
                // Use rt_native_eq for safe equality of native codegen values.
                // Handles both raw untagged integers (icmp fast path) and
                // tagged heap strings (content comparison via rt_value_eq).
                call_runtime_2(ctx, builder, "rt_native_eq", lhs, rhs)
            }
        }
        BinOp::NotEq => {
            if is_float {
                // Use native float inequality
                let cmp_i8 = builder.ins().fcmp(FloatCC::NotEqual, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else if vreg_is_text(ctx, left_vreg) && vreg_is_text(ctx, right_vreg) {
                let eq = compile_text_eq_with_identity_fast_path(ctx, builder, lhs, rhs);
                let zero = builder.ins().iconst(types::I64, 0);
                let neq = builder.ins().icmp(IntCC::Equal, eq, zero);
                ensure_i64(builder, neq)
            } else if vreg_is_native_equality_scalar(ctx, left_vreg) && vreg_is_native_equality_scalar(ctx, right_vreg)
            {
                let use_unsigned =
                    vreg_is_signed(ctx, left_vreg) == Some(false) || vreg_is_signed(ctx, right_vreg) == Some(false);
                let lhs = ensure_i64_typed(builder, lhs, Some(!use_unsigned));
                let rhs = ensure_i64_typed(builder, rhs, Some(!use_unsigned));
                let cmp_i8 = builder.ins().icmp(IntCC::NotEqual, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else {
                // Use rt_native_neq for safe inequality of native codegen values.
                call_runtime_2(ctx, builder, "rt_native_neq", lhs, rhs)
            }
        }
        BinOp::Is => {
            // Identity comparison - bitcast floats to i64 for bit-level equality
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            let result = builder.ins().icmp(IntCC::Equal, li, ri);
            ensure_i64(builder, result)
        }
        BinOp::In | BinOp::NotIn => {
            // Ensure both operands are i64 for runtime function call
            let lhs_i64 = ensure_i64(builder, lhs);
            let rhs_i64 = ensure_i64(builder, rhs);
            let contains_raw = call_runtime_2(ctx, builder, "rt_contains", rhs_i64, lhs_i64);
            let result = ensure_i64(builder, contains_raw);
            if matches!(op, BinOp::NotIn) {
                let one = builder.ins().iconst(types::I64, 1);
                builder.ins().bxor(result, one)
            } else {
                result
            }
        }
        BinOp::And | BinOp::AndSuspend => {
            let lhs_bool = if is_float {
                let zero_f = if lhs_type == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().f64const(0.0)
                };
                builder.ins().fcmp(FloatCC::NotEqual, lhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, lhs, 0)
            };
            let rhs_type = builder.func.dfg.value_type(rhs);
            let rhs_is_float = rhs_type == types::F32 || rhs_type == types::F64;
            let rhs_bool = if rhs_is_float {
                let zero_f = if rhs_type == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().f64const(0.0)
                };
                builder.ins().fcmp(FloatCC::NotEqual, rhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, rhs, 0)
            };
            let result = builder.ins().band(lhs_bool, rhs_bool);
            ensure_i64(builder, result)
        }
        BinOp::Or | BinOp::OrSuspend => {
            let lhs_bool = if is_float {
                let zero_f = if lhs_type == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().f64const(0.0)
                };
                builder.ins().fcmp(FloatCC::NotEqual, lhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, lhs, 0)
            };
            let rhs_type = builder.func.dfg.value_type(rhs);
            let rhs_is_float = rhs_type == types::F32 || rhs_type == types::F64;
            let rhs_bool = if rhs_is_float {
                let zero_f = if rhs_type == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().f64const(0.0)
                };
                builder.ins().fcmp(FloatCC::NotEqual, rhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, rhs, 0)
            };
            let result = builder.ins().bor(lhs_bool, rhs_bool);
            ensure_i64(builder, result)
        }
        BinOp::Pow => {
            if is_float {
                // Float power via libm pow (rt_math_pow, real f64 ABI). The old
                // integer-exponent fmul loop truncated fractional exponents:
                // `x ** 0.5` compiled to x**0 == 1.0 (broke math_sqrt under JIT).
                let rhs_type = builder.func.dfg.value_type(rhs);
                let lhs_f64 = if lhs_type == types::F32 {
                    builder.ins().fpromote(types::F64, lhs)
                } else {
                    lhs
                };
                let rhs_f64 = if rhs_type == types::F32 {
                    builder.ins().fpromote(types::F64, rhs)
                } else if rhs_type.is_float() {
                    rhs
                } else {
                    builder.ins().fcvt_from_sint(types::F64, rhs)
                };
                let res = call_runtime_2(ctx, builder, "rt_math_pow", lhs_f64, rhs_f64);
                if lhs_type == types::F32 {
                    builder.ins().fdemote(types::F32, res)
                } else {
                    res
                }
            } else {
                let loop_header = builder.create_block();
                let loop_body = builder.create_block();
                let loop_exit = builder.create_block();

                builder.append_block_param(loop_header, types::I64);
                builder.append_block_param(loop_header, types::I64);
                builder.append_block_param(loop_exit, types::I64);

                let one = builder.ins().iconst(types::I64, 1);
                builder.ins().jump(loop_header, &[one, rhs]);

                builder.switch_to_block(loop_header);
                let result_param = builder.block_params(loop_header)[0];
                let exp_param = builder.block_params(loop_header)[1];
                let zero = builder.ins().iconst(types::I64, 0);
                let cond = builder.ins().icmp(IntCC::SignedGreaterThan, exp_param, zero);
                builder.ins().brif(cond, loop_body, &[], loop_exit, &[result_param]);
                builder.seal_block(loop_body);
                builder.seal_block(loop_exit);

                builder.switch_to_block(loop_body);
                let new_result = builder.ins().imul(result_param, lhs);
                let new_exp = builder.ins().isub(exp_param, one);
                builder.ins().jump(loop_header, &[new_result, new_exp]);
                builder.seal_block(loop_header);

                builder.switch_to_block(loop_exit);
                builder.block_params(loop_exit)[0]
            }
        }
        BinOp::MatMul => {
            // Matrix multiplication (@) - Simple Math #1930-#1939
            // Codegen requires runtime library support for dynamic array operations
            // Use interpreter mode (default) for full matrix multiplication support
            return Err(
                "Matrix multiplication (@) requires runtime library, use interpreter mode (already implemented)"
                    .to_string(),
            );
        }
        BinOp::PipeForward => {
            // Pipe forward requires function call at runtime
            return Err("Pipe forward (|>) requires interpreter mode for function dispatch".to_string());
        }
        BinOp::Parallel => {
            // Parallel execution requires async runtime
            return Err("Parallel operator (//) requires interpreter mode for concurrent execution".to_string());
        }
        BinOp::Compose => {
            // Function composition (>>) should be desugared to lambda before codegen
            return Err("Compose operator (>>) should be desugared before native codegen".to_string());
        }
        BinOp::LayerConnect => {
            // Layer connect (~>) requires ML runtime
            return Err("Layer connect operator (~>) requires ML runtime support".to_string());
        }
    };
    Ok(val)
}

/// Compile built-in I/O function calls (print, println, eprint, eprintln, etc.)
/// Returns Some(result_value) if the function was handled, None if not a built-in I/O function.
pub(crate) fn compile_builtin_io_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    args: &[VReg],
    _dest: &Option<VReg>,
) -> InstrResult<Option<cranelift_codegen::ir::Value>> {
    match func_name {
        "input" | "spl_input" => {
            // Read a line from stdin
            let read_fn = "rt_read_stdin_line";
            if let Some(&func_id) = ctx.runtime_funcs.get(read_fn) {
                let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                let call = adapted_call(builder, func_ref, &[]);
                let result = builder.inst_results(call)[0];
                return Ok(Some(result));
            }
            let nil = builder.ins().iconst(types::I64, 0);
            Ok(Some(nil))
        }
        "int" | "i64" => {
            // Convert string to integer: calls rt_string_to_int_lenient (returns
            // raw i64), then re-box as RuntimeValue via rt_value_int. Task #118:
            // the generic int(x) builtin is a TOTAL, non-erroring, leading-digit
            // -prefix parse ("4.2" -> 4, "abc"/"" -> 0) — distinct from the
            // stricter whole-string rt_string_to_int used by .to_int()/.parse_int().
            if args.is_empty() {
                let zero = builder.ins().iconst(types::I64, 0);
                return Ok(Some(zero));
            }
            let arg_val = match ctx.vreg_values.get(&args[0]) {
                Some(&v) => v,
                None => builder.ins().iconst(types::I64, 0),
            };
            // Call rt_string_to_int_lenient to get raw i64
            if let Some(&to_int_id) = ctx.runtime_funcs.get("rt_string_to_int_lenient") {
                let to_int_ref = ctx.module.declare_func_in_func(to_int_id, builder.func);
                let call = adapted_call(builder, to_int_ref, &[arg_val]);
                let raw_int = builder.inst_results(call)[0];
                // Re-box as RuntimeValue via rt_value_int
                if let Some(&value_int_id) = ctx.runtime_funcs.get("rt_value_int") {
                    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);
                    let call2 = adapted_call(builder, value_int_ref, &[raw_int]);
                    let result = builder.inst_results(call2)[0];
                    return Ok(Some(result));
                }
                return Ok(Some(raw_int));
            }
            let zero = builder.ins().iconst(types::I64, 0);
            Ok(Some(zero))
        }
        "str" | "to_string" | "to_text" => {
            // Convert value to string: calls rt_to_string directly.
            // Arguments should already be RuntimeValues (tagged ints, heap strings, etc.)
            if args.is_empty() {
                let nil = builder.ins().iconst(types::I64, 0);
                return Ok(Some(nil));
            }
            let arg_val = match ctx.vreg_values.get(&args[0]) {
                Some(&v) => v,
                None => builder.ins().iconst(types::I64, 0),
            };
            if let Some(&to_str_id) = ctx.runtime_funcs.get("rt_to_string") {
                let to_str_ref = ctx.module.declare_func_in_func(to_str_id, builder.func);
                let call = adapted_call(builder, to_str_ref, &[arg_val]);
                let result = builder.inst_results(call)[0];
                return Ok(Some(result));
            }
            let nil = builder.ins().iconst(types::I64, 0);
            Ok(Some(nil))
        }
        "print" | "println" | "eprint" | "eprintln" | "print_raw" | "eprint_raw" | "spl_print" | "spl_println"
        | "spl_eprint" | "spl_eprintln" | "spl_print_raw" | "spl_eprint_raw" => {
            // Determine which runtime function to use
            // Note: In Simple, 'print' adds a newline (Python 3 convention)
            // print_raw prints without newline
            // Accepts both bare names and spl_ prefixed names (safe symbol exports).
            let (print_value_fn, print_str_fn) = match func_name {
                "print" | "spl_print" => ("rt_println_value", "rt_println_str"),
                "println" | "spl_println" => ("rt_println_value", "rt_println_str"),
                "print_raw" | "spl_print_raw" => ("rt_print_value", "rt_print_str"),
                "eprint" | "spl_eprint" => ("rt_eprint_value", "rt_eprint_str"),
                "eprintln" | "spl_eprintln" => ("rt_eprintln_value", "rt_eprintln_str"),
                "eprint_raw" | "spl_eprint_raw" => ("rt_eprint_value", "rt_eprint_str"),
                _ => unreachable!(),
            };

            // For each argument, call the appropriate print function
            for (i, arg) in args.iter().enumerate() {
                // Add space between arguments (except first)
                if i > 0 {
                    // Print a space separator
                    let space_data_id = declare_named_bytes(ctx, b" ")?;
                    let space_gv = ctx.module.declare_data_in_func(space_data_id, builder.func);
                    let space_ptr = builder.ins().global_value(types::I64, space_gv);
                    let space_len = builder.ins().iconst(types::I64, 1);

                    // Use the base print_str function (not println) for space separator
                    let base_str_fn = match func_name {
                        "print" | "spl_print" => "rt_print_str",
                        "println" | "spl_println" => "rt_print_str",
                        "eprintln" | "spl_eprintln" => "rt_eprint_str",
                        _ => print_str_fn,
                    };
                    call_runtime_2_void(ctx, builder, base_str_fn, space_ptr, space_len);
                }

                // Print the argument value using rt_print_value / rt_println_value
                // For the last arg of print/println/eprintln, use the ln variant
                let is_last = i == args.len() - 1;
                let fn_to_use = if is_last
                    && matches!(
                        func_name,
                        "print" | "println" | "eprintln" | "spl_print" | "spl_println" | "spl_eprintln"
                    ) {
                    print_value_fn
                } else {
                    // Use non-newline variant for intermediate args
                    match func_name {
                        "print" | "spl_print" => "rt_print_value",
                        "println" | "spl_println" => "rt_print_value",
                        "eprintln" | "spl_eprintln" => "rt_eprint_value",
                        _ => print_value_fn,
                    }
                };

                let arg_val = match ctx.vreg_values.get(arg) {
                    Some(&v) => v,
                    None => return Err(format!("print: arg vreg {:?} not found", arg)),
                };
                call_runtime_1_void(ctx, builder, fn_to_use, arg_val);
            }

            // Handle empty print (just prints nothing or newline)
            if args.is_empty()
                && matches!(
                    func_name,
                    "print" | "println" | "eprintln" | "spl_print" | "spl_println" | "spl_eprintln"
                )
            {
                // Print just a newline
                let newline_data_id = declare_named_bytes(ctx, b"\n")?;
                let newline_gv = ctx.module.declare_data_in_func(newline_data_id, builder.func);
                let newline_ptr = builder.ins().global_value(types::I64, newline_gv);
                let newline_len = builder.ins().iconst(types::I64, 1);

                let base_str_fn = if matches!(func_name, "print" | "println" | "spl_print" | "spl_println") {
                    "rt_print_str"
                } else {
                    "rt_eprint_str"
                };
                call_runtime_2_void(ctx, builder, base_str_fn, newline_ptr, newline_len);
            }

            // Return nil (0) for void functions
            let nil = builder.ins().iconst(types::I64, 0);
            Ok(Some(nil))
        }
        // Not a built-in I/O function
        _ => Ok(None),
    }
}

pub(crate) fn compile_interp_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    func_name: &str,
    args: &[VReg],
    boxed_result: bool,
) -> InstrResult<()> {
    let argc = builder.ins().iconst(types::I64, args.len() as i64);
    let argv = if args.is_empty() {
        builder.ins().iconst(types::I64, 0)
    } else {
        let byte_len = builder.ins().iconst(types::I64, (args.len() * 8) as i64);
        call_runtime_1(ctx, builder, "rt_alloc", byte_len)
    };

    for (index, arg) in args.iter().enumerate() {
        let mut arg_val = match ctx.vreg_values.get(arg) {
            Some(&v) => v,
            None => return Err(format!("interp_call: arg vreg {:?} not found", arg)),
        };
        match ctx.vreg_types.get(arg).copied() {
            Some(TypeId::BOOL) => {
                arg_val = call_runtime_1(ctx, builder, "rt_value_bool", arg_val);
            }
            Some(TypeId::I8 | TypeId::I16 | TypeId::I32) => {
                if builder.func.dfg.value_type(arg_val) != types::I64 {
                    arg_val = builder.ins().sextend(types::I64, arg_val);
                }
                arg_val = call_runtime_1(ctx, builder, "rt_value_int", arg_val);
            }
            Some(TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::CHAR) => {
                if builder.func.dfg.value_type(arg_val) != types::I64 {
                    arg_val = builder.ins().uextend(types::I64, arg_val);
                }
                arg_val = call_runtime_1(ctx, builder, "rt_value_int", arg_val);
            }
            Some(TypeId::I64 | TypeId::U64) => {
                arg_val = call_runtime_1(ctx, builder, "rt_value_int", arg_val);
            }
            Some(TypeId::F64) => {
                arg_val = call_runtime_1(ctx, builder, "rt_value_float", arg_val);
            }
            _ => {}
        }
        builder.ins().store(MemFlags::new(), arg_val, argv, (index * 8) as i32);
    }

    let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;

    let result = call_runtime_4(ctx, builder, "rt_interp_call", name_ptr, name_len, argc, argv);

    if let Some(d) = dest {
        // rt_interp_call returns a boxed RuntimeValue. Extern declarations
        // routed here by the hybrid transform (JIT-unresolvable rt_*/spl_*
        // symbols, e.g. rt_torch_cuda_available() -> bool in a torch-less
        // build) have raw scalar/handle destinations, so unbox — otherwise a
        // NaN-boxed `false` reads as truthy in compiled conditions. Call
        // dests carry no entry in vreg_types, so the SFFI naming convention
        // is the reliable signal here.
        //
        // EXCEPTION: when the callee's declared return type is a heap/composite
        // value (tuple/text/array — `boxed_result`), unboxing to a raw i64
        // strips the NaN-box tag and corrupts the downstream `rt_tuple_get` /
        // `rt_string_*` reads. Keep those boxed so compiled consumers (e.g.
        // `val (a,b,c) = rt_http_request(...)`) read them correctly. Scalar
        // returns keep the historical unbox unchanged.
        let is_extern_bridge = func_name.starts_with("rt_") || func_name.starts_with("spl_");
        let keep_boxed_result = boxed_result || interp_call_keeps_boxed_result(func_name);
        let value = if !keep_boxed_result
            && (ctx.vreg_types.get(d).copied() == Some(TypeId::F64) || interp_call_returns_f64(func_name))
        {
            call_runtime_1(ctx, builder, "rt_value_as_float", result)
        } else if !keep_boxed_result && (is_extern_bridge || vreg_is_native_equality_scalar(ctx, *d)) {
            call_runtime_1(ctx, builder, "rt_value_raw_i64", result)
        } else {
            result
        };
        ctx.vreg_values.insert(*d, value);
    }
    Ok(())
}
