// Helper functions for instruction compilation.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use super::{InstrContext, InstrResult};
use crate::mir::VReg;

/// Helper to get a VReg value, returning tagged nil (3) if missing.
/// This handles cases where control flow or complex patterns leave VRegs undefined.
/// Note: Creating default values can cause SSA violations in some control flow patterns.
/// We create the value in the entry block to minimize domination issues.
pub(crate) fn get_vreg_or_default<M: Module>(
    ctx: &InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    vreg: &VReg,
) -> cranelift_codegen::ir::Value {
    if let Some(val) = ctx.vreg_values.get(vreg) {
        return *val;
    }

    // Missing VReg value indicates a bug in MIR SSA construction or codegen
    // (e.g., incomplete phi coverage). Fallbacks silently produced bad code
    // during bootstrap, so fail fast when debugging.
    if std::env::var("SIMPLE_STRICT_VREG").is_ok() {
        // Emit immediate context to stderr so bootstrap logs show the offending site
        eprintln!(
            "[strict-vreg] missing value for {:?} in function {}",
            vreg, ctx.func.name
        );
        panic!(
            "codegen: missing VReg value for {:?} in function {}",
            vreg, ctx.func.name
        );
    }

    // Default: tagged nil (TAG_SPECIAL=0b011 | SPECIAL_NIL=0 = 3)
    builder.ins().iconst(types::I64, 3)
}

/// Helper to create a string constant in module data and return (ptr, len) values.
/// Uses content-based naming for deterministic output and deduplication.
pub(crate) fn create_string_constant<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    text: &str,
) -> InstrResult<(cranelift_codegen::ir::Value, cranelift_codegen::ir::Value)> {
    let bytes = text.as_bytes();
    let data_id = declare_named_bytes(ctx, bytes)?;

    let global_val = ctx.module.declare_data_in_func(data_id, builder.func);
    let ptr = builder.ins().global_value(types::I64, global_val);
    let len = builder.ins().iconst(types::I64, bytes.len() as i64);

    Ok((ptr, len))
}

/// FNV-1a 64-bit hash of byte slice — used for content-based data naming.
fn fnv1a_hash(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Declare a named data segment from raw bytes using content-based FNV-1a hash.
/// Returns the DataId. Handles deduplication via deterministic naming.
pub(crate) fn declare_named_bytes<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    bytes: &[u8],
) -> InstrResult<cranelift_module::DataId> {
    let name = format!(".Ldata_{:016x}", fnv1a_hash(bytes));
    match ctx
        .module
        .declare_data(&name, cranelift_module::Linkage::Local, false, false)
    {
        Ok(id) => {
            let mut data_desc = cranelift_module::DataDescription::new();
            data_desc.define(bytes.to_vec().into_boxed_slice());
            let _ = ctx.module.define_data(id, &data_desc);
            Ok(id)
        }
        Err(e) => Err(e.to_string()),
    }
}

/// Create a null-terminated C string constant and return a pointer value.
/// Uses content-based naming for deterministic output and deduplication.
pub(crate) fn create_cstring_constant<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    text: &str,
) -> InstrResult<cranelift_codegen::ir::Value> {
    let mut bytes = text.as_bytes().to_vec();
    bytes.push(0);
    let data_id = declare_named_bytes(ctx, &bytes)?;
    let global_val = ctx.module.declare_data_in_func(data_id, builder.func);
    let ptr = builder.ins().global_value(types::I64, global_val);
    Ok(ptr)
}

/// Safely extend a value to i64, skipping if already i64.
/// Handles int types (uextend) and float types (bitcast).
pub(crate) fn safe_extend_to_i64(
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let ty = builder.func.dfg.value_type(val);
    if ty == types::I64 {
        val
    } else if ty.is_int() && ty.bits() < 64 {
        builder.ins().uextend(types::I64, val)
    } else if ty == types::F64 {
        builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val)
    } else if ty == types::F32 {
        let promoted = builder.ins().fpromote(types::F64, val);
        builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), promoted)
    } else {
        val
    }
}

/// Ensure a value is i64, converting floats via bitcast.
/// Use this before passing values to functions that expect i64.
/// Uses uextend (zero-extend) to preserve unsigned semantics.
pub(crate) fn ensure_i64_for_call(
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let ty = builder.func.dfg.value_type(val);
    if ty == types::I64 {
        val
    } else if ty.is_int() && ty.bits() < 64 {
        builder.ins().uextend(types::I64, val)
    } else if ty == types::F64 {
        builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val)
    } else if ty == types::F32 {
        let promoted = builder.ins().fpromote(types::F64, val);
        builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), promoted)
    } else {
        val
    }
}

/// Call a function with automatic argument type adaptation.
/// Ensures arguments match the function signature types, handling:
/// - int width conversions (sextend/ireduce)
/// - float→int (bitcast f64→i64 for RuntimeValue, fcvt_to_sint otherwise)
/// - int→float (fcvt_from_sint)
/// - float width conversions (fpromote/fdemote)
/// - missing arguments (padded with zero)
/// - extra arguments (truncated)
pub(crate) fn adapted_call(
    builder: &mut FunctionBuilder,
    func_ref: cranelift_codegen::ir::FuncRef,
    args: &[cranelift_codegen::ir::Value],
) -> cranelift_codegen::ir::Inst {
    let sig_ref = builder.func.dfg.ext_funcs[func_ref].signature;
    let expected_types: Vec<cranelift_codegen::ir::Type> = builder.func.dfg.signatures[sig_ref]
        .params
        .iter()
        .map(|p| p.value_type)
        .collect();

    let mut adapted = Vec::with_capacity(expected_types.len());
    for (i, &expected_ty) in expected_types.iter().enumerate() {
        if i < args.len() {
            adapted.push(adapt_value_to_type(builder, args[i], expected_ty));
        } else {
            // Missing arg — pad with default zero value
            adapted.push(default_for_type(builder, expected_ty));
        }
    }
    builder.ins().call(func_ref, &adapted)
}

// ============================================================================
// C1: call_runtime_N helpers — promoted from methods.rs private helpers to pub
// ============================================================================

/// Call a runtime function with no arguments (arity-0, void return).
/// The function must be pre-declared in `ctx.runtime_funcs`.
#[inline]
pub fn call_runtime_0<M: Module>(ctx: &mut InstrContext<'_, M>, builder: &mut FunctionBuilder, func_name: &str) {
    let func_id = ctx
        .runtime_funcs
        .get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, ctx.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[]);
}

/// Call a runtime function with one argument and return its result.
/// The function must be pre-declared in `ctx.runtime_funcs`.
#[inline]
pub fn call_runtime_1<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx
        .runtime_funcs
        .get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, ctx.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg]);
    builder.inst_results(call)[0]
}

/// Call a runtime function with one argument, discarding the return value.
/// Use this for void runtime fns like rt_print_value, rt_actor_reply, rt_condition_probe.
/// The function must be pre-declared in `ctx.runtime_funcs`.
#[inline]
pub fn call_runtime_1_void<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg: cranelift_codegen::ir::Value,
) {
    let func_id = ctx
        .runtime_funcs
        .get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, ctx.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[arg]);
}

/// Call a runtime function with two arguments and return its result.
/// The function must be pre-declared in `ctx.runtime_funcs`.
#[inline]
pub fn call_runtime_2<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx
        .runtime_funcs
        .get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, ctx.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg1, arg2]);
    builder.inst_results(call)[0]
}

/// Call a runtime function with two arguments, discarding the return value.
/// The function must be pre-declared in `ctx.runtime_funcs`.
#[inline]
pub fn call_runtime_2_void<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
) {
    let func_id = ctx
        .runtime_funcs
        .get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, ctx.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[arg1, arg2]);
}

/// Call a runtime function with three arguments and return its result.
/// The function must be pre-declared in `ctx.runtime_funcs`.
#[inline]
pub fn call_runtime_3<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
    arg3: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx
        .runtime_funcs
        .get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, ctx.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg1, arg2, arg3]);
    builder.inst_results(call)[0]
}

/// Call a runtime function with three arguments, discarding the return value.
/// Use this for void runtime fns like rt_condition_probe.
/// The function must be pre-declared in `ctx.runtime_funcs`.
#[inline]
pub fn call_runtime_3_void<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
    arg3: cranelift_codegen::ir::Value,
) {
    let func_id = ctx
        .runtime_funcs
        .get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, ctx.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[arg1, arg2, arg3]);
}

// ============================================================================
// C2: declare_uniform_i64_import — cache-check + sig-build + declare + cache
// ============================================================================

/// Look up or declare a uniform import (all I64 params → I64 return) and
/// return the cached `FuncId`.
///
/// Returns `Ok(FuncId)` on success, `Err(ModuleError)` if `declare_function`
/// fails and the name is not already cached. Each call site is responsible for
/// its own error recovery (e.g., fall through to NIL, store null, or fallback
/// to `rt_method_not_found`).
///
/// The `_builder` parameter is retained for API uniformity with other helpers;
/// signature building does not emit IR instructions.
#[inline]
pub fn declare_uniform_i64_import<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    name: &str,
    n_params: usize,
) -> Result<cranelift_module::FuncId, Box<cranelift_module::ModuleError>> {
    use cranelift_codegen::ir::{AbiParam, Signature};
    use cranelift_module::Linkage;

    if let Some(&existing) = ctx.func_ids.get(name) {
        return Ok(existing);
    }
    let mut sig = Signature::new(crate::codegen::shared::platform_call_conv());
    for _ in 0..n_params {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));
    let result = ctx
        .module
        .declare_function(name, Linkage::Import, &sig)
        .map_err(Box::new);
    if let Ok(id) = &result {
        ctx.func_ids.insert(name.to_string(), *id);
    }
    result
}

/// Adapt a single value to match an expected Cranelift type.
fn adapt_value_to_type(
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    expected_ty: cranelift_codegen::ir::Type,
) -> cranelift_codegen::ir::Value {
    let actual_ty = builder.func.dfg.value_type(val);
    if actual_ty == expected_ty {
        return val;
    }
    // int → int (use uextend to preserve unsigned semantics —
    // sextend turns u16 0xFFFF into i64 -1, breaking PCI vendor checks etc.)
    if actual_ty.is_int() && expected_ty.is_int() {
        if actual_ty.bits() < expected_ty.bits() {
            return builder.ins().uextend(expected_ty, val);
        } else {
            return builder.ins().ireduce(expected_ty, val);
        }
    }
    // float → int (bitcast for RuntimeValue preservation)
    if actual_ty.is_float() && expected_ty.is_int() {
        if actual_ty == types::F64 && expected_ty == types::I64 {
            return builder
                .ins()
                .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val);
        }
        if actual_ty == types::F32 {
            let promoted = builder.ins().fpromote(types::F64, val);
            if expected_ty == types::I64 {
                return builder
                    .ins()
                    .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), promoted);
            }
        }
        return builder.ins().fcvt_to_sint(expected_ty, val);
    }
    // int → float
    if actual_ty.is_int() && expected_ty.is_float() {
        return builder.ins().fcvt_from_sint(expected_ty, val);
    }
    // float → float
    if actual_ty.is_float() && expected_ty.is_float() {
        if actual_ty == expected_ty {
            return val; // same type, no conversion needed
        } else if actual_ty.bits() < expected_ty.bits() {
            return builder.ins().fpromote(expected_ty, val);
        } else {
            return builder.ins().fdemote(expected_ty, val);
        }
    }
    // Fallback: use as-is
    val
}

/// Create a default zero value for a given Cranelift type.
fn default_for_type(builder: &mut FunctionBuilder, ty: cranelift_codegen::ir::Type) -> cranelift_codegen::ir::Value {
    if ty.is_int() {
        builder.ins().iconst(ty, 0)
    } else if ty == types::F32 {
        builder.ins().f32const(0.0)
    } else if ty == types::F64 {
        builder.ins().f64const(0.0)
    } else {
        builder.ins().iconst(types::I64, 0)
    }
}

/// Helper to perform indirect call with result handling.
/// Automatically adapts argument count and types to match the signature.
pub(crate) fn indirect_call_with_result<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    sig_ref: cranelift_codegen::ir::SigRef,
    fn_ptr: cranelift_codegen::ir::Value,
    call_args: &[cranelift_codegen::ir::Value],
    dest: &Option<VReg>,
) {
    // Adapt args to match the indirect call signature
    let sig = &builder.func.dfg.signatures[sig_ref];
    let expected_count = sig.params.len();
    let expected_types: Vec<cranelift_codegen::ir::Type> = sig.params.iter().map(|p| p.value_type).collect();

    let mut adapted = Vec::with_capacity(expected_count);
    for (i, &expected_ty) in expected_types.iter().enumerate() {
        if i < call_args.len() {
            adapted.push(adapt_value_to_type(builder, call_args[i], expected_ty));
        } else {
            adapted.push(default_for_type(builder, expected_ty));
        }
    }
    // Truncate extra args (don't pass more than signature expects)

    let call = builder.ins().call_indirect(sig_ref, fn_ptr, &adapted);

    if let Some(d) = dest {
        let results = builder.inst_results(call);
        if !results.is_empty() {
            ctx.vreg_values.insert(*d, results[0]);
        } else {
            // Tagged nil (3) for missing return values
            let nil = builder.ins().iconst(types::I64, 3);
            ctx.vreg_values.insert(*d, nil);
        }
    }
}
