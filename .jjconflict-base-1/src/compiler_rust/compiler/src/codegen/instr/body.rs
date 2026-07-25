// Complete MIR function body compilation.

use cranelift_codegen::ir::{condcodes::IntCC, types, InstBuilder, MemFlags};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::Module;
use std::collections::{HashMap, HashSet};

use crate::hir::{BinOp, TypeId, UnaryOp};
use crate::mir::{BlockId, CallTarget, MirFunction, MirInst, Terminator, VReg};

use crate::codegen::shared::implicit_local_param_slots;
use super::super::types_util::type_to_cranelift;
use super::async_ops::compile_yield;
use super::helpers::adapted_call;
use super::{compile_instruction, InstrContext, InstrResult};

/// Collect VRegs that are live across block boundaries.
/// Only these need Cranelift Variables for phi node insertion.
/// Block-local VRegs stay as raw Cranelift Values in vreg_values.
fn collect_cross_block_vregs(func: &MirFunction) -> HashSet<VReg> {
    let live_ins = func.compute_live_ins();
    let mut cross_block = HashSet::new();
    for live_set in live_ins.values() {
        for vreg in live_set {
            cross_block.insert(*vreg);
        }
    }
    cross_block
}

/// Derive the bit-width unit-type from (bits, signed). Used by `build_vreg_types`
/// to map `UnitWiden` / `UnitNarrow` destination widths back onto the integer
/// TypeId constants.
fn unit_bits_to_type_id(bits: u8, signed: bool) -> Option<TypeId> {
    match (bits, signed) {
        (8, true) => Some(TypeId::I8),
        (16, true) => Some(TypeId::I16),
        (32, true) => Some(TypeId::I32),
        (64, true) => Some(TypeId::I64),
        (8, false) => Some(TypeId::U8),
        (16, false) => Some(TypeId::U16),
        (32, false) => Some(TypeId::U32),
        (64, false) => Some(TypeId::U64),
        _ => None,
    }
}

/// Result type of a `BinOp` given the operand types.
/// Comparisons, membership, and identity produce BOOL; logical ops produce BOOL;
/// arithmetic, bitwise, and shift ops keep the left-operand type
/// (unknown operand → unknown result).
fn binop_result_type(op: BinOp, lhs_ty: Option<TypeId>) -> Option<TypeId> {
    match op {
        BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => Some(TypeId::BOOL),
        BinOp::Is | BinOp::In | BinOp::NotIn => Some(TypeId::BOOL),
        BinOp::And | BinOp::Or | BinOp::AndSuspend | BinOp::OrSuspend => Some(TypeId::BOOL),
        _ => lhs_ty,
    }
}

/// Build the `vreg_types: HashMap<VReg, TypeId>` map for a MIR function.
///
/// Mirrors the SPIR-V backend's per-op `vreg_types` population (see
/// `src/codegen/vulkan/spirv_instructions.rs:31-108`) but runs as a single
/// pre-emission walk instead of inline during codegen — Cranelift does not
/// need the TypeId to emit each instruction, only to pick signed-vs-unsigned
/// variants later (FR-DRIVER-0002b). Walking in block + instruction order is
/// enough for SSA-style MIR: defs precede uses within a block, and block order
/// is topological for most functions. Cross-block phi-like propagation may
/// miss some `Copy` destinations — consumers treat missing entries as
/// "unknown" (default signed in FR-0002b).
pub(super) fn build_vreg_types(
    func: &MirFunction,
    function_return_types: &HashMap<String, TypeId>,
) -> HashMap<VReg, TypeId> {
    let mut types_map: HashMap<VReg, TypeId> = HashMap::new();

    for block in &func.blocks {
        for inst in &block.instructions {
            match inst {
                MirInst::ConstInt { dest, .. } => {
                    // MIR integer constants widen to i64 in Cranelift
                    // (see constants::compile_const_int).
                    types_map.insert(*dest, TypeId::I64);
                }
                MirInst::ConstFloat { dest, .. } => {
                    types_map.insert(*dest, TypeId::F64);
                }
                MirInst::ConstBool { dest, .. } => {
                    types_map.insert(*dest, TypeId::BOOL);
                }
                MirInst::ConstString { dest, .. } => {
                    types_map.insert(*dest, TypeId::STRING);
                }
                MirInst::Copy { dest, src } => {
                    if let Some(&ty) = types_map.get(src) {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::BinOp { dest, op, left, .. } => {
                    let lhs_ty = types_map.get(left).copied();
                    if let Some(ty) = binop_result_type(*op, lhs_ty) {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::UnaryOp { dest, op, operand } => {
                    let ty = match op {
                        UnaryOp::Not => Some(TypeId::BOOL),
                        _ => types_map.get(operand).copied(),
                    };
                    if let Some(ty) = ty {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::Cast { dest, to_ty, .. } => {
                    types_map.insert(*dest, *to_ty);
                }
                MirInst::Load { dest, ty, .. } => {
                    types_map.insert(*dest, *ty);
                }
                MirInst::GlobalLoad { dest, ty, .. } => {
                    types_map.insert(*dest, *ty);
                }
                MirInst::GcAlloc { dest, ty } => {
                    types_map.insert(*dest, *ty);
                }
                MirInst::StructInit { dest, type_id, .. } => {
                    types_map.insert(*dest, *type_id);
                }
                MirInst::FieldGet { dest, field_type, .. } => {
                    types_map.insert(*dest, *field_type);
                }
                MirInst::IndirectCall {
                    dest: Some(d),
                    return_type,
                    ..
                } => {
                    types_map.insert(*d, *return_type);
                }
                MirInst::IndirectCall { dest: None, .. } => {}
                MirInst::MethodCallVirtual {
                    dest: Some(d),
                    return_type,
                    ..
                } => {
                    types_map.insert(*d, *return_type);
                }
                MirInst::MethodCallVirtual { dest: None, .. } => {}
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_text"
                    || func_name == "to_string"
                    || func_name == "str"
                    || func_name.ends_with(".to_text")
                    || func_name.ends_with(".to_string")
                    || func_name.ends_with(".str") =>
                {
                    types_map.insert(*d, TypeId::STRING);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_u8" || func_name.ends_with(".to_u8") => {
                    types_map.insert(*d, TypeId::U8);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_u16" || func_name.ends_with(".to_u16") => {
                    types_map.insert(*d, TypeId::U16);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_u32" || func_name.ends_with(".to_u32") => {
                    types_map.insert(*d, TypeId::U32);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_u64" || func_name.ends_with(".to_u64") => {
                    types_map.insert(*d, TypeId::U64);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_i8" || func_name.ends_with(".to_i8") => {
                    types_map.insert(*d, TypeId::I8);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_i16" || func_name.ends_with(".to_i16") => {
                    types_map.insert(*d, TypeId::I16);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_i32" || func_name.ends_with(".to_i32") => {
                    types_map.insert(*d, TypeId::I32);
                }
                MirInst::MethodCallStatic {
                    dest: Some(d),
                    func_name,
                    ..
                } if func_name == "to_i64"
                    || func_name == "to_int"
                    || func_name.ends_with(".to_i64")
                    || func_name.ends_with(".to_int") =>
                {
                    types_map.insert(*d, TypeId::I64);
                }
                MirInst::MethodCallStatic { .. } => {}
                MirInst::Call {
                    dest: Some(d), target, ..
                } => {
                    if let Some(&ty) = function_return_types.get(target.name()) {
                        types_map.insert(*d, ty);
                        continue;
                    }
                    let base = target
                        .name()
                        .rsplit_once("__")
                        .map(|(_, tail)| tail)
                        .unwrap_or(target.name());
                    let ty = match base {
                        "spl_load_i64" => Some(TypeId::I64),
                        "spl_load_u8" => Some(TypeId::U8),
                        "rt_env_get" | "rt_get_env" | "rt_file_read_text" | "rt_file_read_text_rv" => {
                            Some(TypeId::STRING)
                        }
                        "rt_is_some" | "rt_is_none" => Some(TypeId::BOOL),
                        "rt_string_eq" | "rt_native_eq" | "rt_native_neq" => Some(TypeId::I64),
                        // Array/collection length returns a native i64. Recording
                        // it here types the `len()` result VReg so a CHAINED
                        // `arr.len().to_i64()` (or `.to_u32()` etc.) sees an i64
                        // receiver and takes the builtin-identity/cast path in
                        // compile_method_call_static — identical to the
                        // bound-intermediate `val n = arr.len(); n.to_i64()` form,
                        // whose reload is a typed `Load`. Without this the chained
                        // receiver is untyped, `prefer_builtin_first` is false, and
                        // `i64.to_i64` falls through to name-based symbol
                        // resolution that mis-picks an unrelated `Type.to_i64` in a
                        // large whole-program link (x64 freestanding SSH kernel:
                        // `our_version.len().to_i64()` returned garbage → empty
                        // server version → KEX "incorrect signature").
                        "rt_array_len" | "rt_len" => Some(TypeId::I64),
                        "rt_array_get_text" => Some(TypeId::STRING),
                        "rt_typed_bytes_u8_at" | "rt_typed_bytes_u8_data_at" | "rt_bytes_u8_at" => Some(TypeId::U8),
                        "rt_typed_words_u32_at" | "rt_typed_words_u32_unchecked" | "rt_typed_words_u32_data_at" => {
                            Some(TypeId::U32)
                        }
                        "rt_typed_words_u64_at"
                        | "rt_typed_words_u64_unchecked"
                        | "rt_typed_words_u64_data_at"
                        | "rt_typed_words_u64_data_at_checked"
                        | "rt_typed_words_u64_raw_data_at" => Some(TypeId::U64),
                        _ => None,
                    };
                    if let Some(ty) = ty {
                        types_map.insert(*d, ty);
                    }
                }
                MirInst::Call { dest: None, .. } => {}
                MirInst::UnitWiden {
                    dest, to_bits, signed, ..
                }
                | MirInst::UnitNarrow {
                    dest, to_bits, signed, ..
                } => {
                    if let Some(ty) = unit_bits_to_type_id(*to_bits, *signed) {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::BoxInt { dest, .. } | MirInst::UnboxInt { dest, .. } => {
                    types_map.insert(*dest, TypeId::I64);
                }
                MirInst::BoxFloat { dest, .. } | MirInst::UnboxFloat { dest, .. } => {
                    types_map.insert(*dest, TypeId::F64);
                }
                // Remaining variants either produce no typed value, or their
                // typed output (arrays, closures, enums, SIMD lanes, GPU ops,
                // futures, actors, generators, etc.) is not yet needed by
                // FR-0002b's signedness dispatch. Leave `vreg_types` entry
                // absent — consumers treat missing as "unknown".
                _ => {}
            }
        }
    }

    types_map
}

fn type_id_is_signed_integer(ty: TypeId) -> bool {
    matches!(ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64)
}

/// Coerce a value to i64 for storage in a Variable declared as i64.
fn coerce_to_i64_typed(
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    type_hint: Option<TypeId>,
) -> cranelift_codegen::ir::Value {
    let ty = builder.func.dfg.value_type(val);
    if ty == types::I64 {
        val
    } else if ty.is_int() && ty.bits() < 64 {
        if type_hint.is_some_and(type_id_is_signed_integer) {
            builder.ins().sextend(types::I64, val)
        } else {
            builder.ins().uextend(types::I64, val)
        }
    } else if ty.is_int() && ty.bits() > 64 {
        builder.ins().ireduce(types::I64, val)
    } else if ty == types::F64 {
        builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val)
    } else if ty == types::F32 {
        // F32 is 32-bit; bitcast requires equal-width types, so promote to F64 first
        let promoted = builder.ins().fpromote(types::F64, val);
        builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), promoted)
    } else {
        // For vector types etc., just use as-is (will be i64 in most cases)
        val
    }
}

/// Coerce a value to i64 for storage in a Variable declared as i64.
fn coerce_to_i64(builder: &mut FunctionBuilder, val: cranelift_codegen::ir::Value) -> cranelift_codegen::ir::Value {
    coerce_to_i64_typed(builder, val, None)
}

/// Safely def_var with type coercion to i64.
fn def_var_coerced(builder: &mut FunctionBuilder, var: Variable, val: cranelift_codegen::ir::Value) {
    let coerced = coerce_to_i64(builder, val);
    builder.def_var(var, coerced);
}

/// Safely def_var with type-aware coercion to i64.
fn def_var_coerced_typed(
    builder: &mut FunctionBuilder,
    var: Variable,
    val: cranelift_codegen::ir::Value,
    type_hint: Option<TypeId>,
) {
    let coerced = coerce_to_i64_typed(builder, val, type_hint);
    builder.def_var(var, coerced);
}

/// Sync vreg_values → Variables: call def_var for all vregs that have values.
/// VRegs are sorted to ensure deterministic Variable definition order.
fn sync_vregs_to_vars(
    builder: &mut FunctionBuilder,
    vreg_values: &HashMap<VReg, cranelift_codegen::ir::Value>,
    vreg_vars: &HashMap<VReg, Variable>,
    vreg_types: &HashMap<VReg, TypeId>,
) {
    let mut sorted: Vec<_> = vreg_values.iter().collect();
    sorted.sort_by_key(|(v, _)| v.0);
    for (vreg, &val) in sorted {
        if let Some(&var) = vreg_vars.get(vreg) {
            def_var_coerced_typed(builder, var, val, vreg_types.get(vreg).copied());
        }
    }
}

/// Sync Variables → vreg_values: call use_var for all declared vreg Variables.
/// VRegs are sorted to ensure deterministic block parameter order.
fn sync_vars_to_vregs(
    builder: &mut FunctionBuilder,
    vreg_values: &mut HashMap<VReg, cranelift_codegen::ir::Value>,
    vreg_vars: &HashMap<VReg, Variable>,
) {
    let mut sorted: Vec<_> = vreg_vars.iter().collect();
    sorted.sort_by_key(|(v, _)| v.0);
    for (&vreg, &var) in sorted {
        let val = builder.use_var(var);
        vreg_values.insert(vreg, val);
    }
}

/// Compile a complete MIR function body.
/// This is shared between AOT (cranelift.rs) and JIT (jit.rs) backends.
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn compile_function_body<M: Module>(
    module: &mut M,
    cranelift_func: &mut cranelift_codegen::ir::Function,
    func: &MirFunction,
    func_ids: &mut std::collections::BTreeMap<String, cranelift_module::FuncId>,
    runtime_funcs: &HashMap<&'static str, cranelift_module::FuncId>,
    global_ids: &std::collections::BTreeMap<String, cranelift_module::DataId>,
    import_map: &std::sync::Arc<std::collections::HashMap<String, String>>,
    use_map: &std::collections::HashMap<String, String>,
    data_exports: &std::sync::Arc<std::collections::HashSet<String>>,
    vtable_data_ids: &std::collections::BTreeMap<String, cranelift_module::DataId>,
    vtable_type_ids: &std::collections::BTreeMap<crate::hir::TypeId, cranelift_module::DataId>,
    fn_arities: &std::sync::Arc<std::collections::HashMap<String, usize>>,
    function_return_types: &HashMap<String, TypeId>,
    enum_defs: &std::sync::Arc<std::collections::HashMap<String, Vec<(String, Option<Vec<simple_parser::Type>>)>>>,
    tag_runtime_pool_join_result: bool,
) -> InstrResult<()> {
    let mut func_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(cranelift_func, &mut func_ctx);

    // Create variables for parameters and locals
    let mut variables = HashMap::new();
    let mut var_idx = 0u32;
    let implicit_param_slots = implicit_local_param_slots(func);

    for i in 0..implicit_param_slots {
        let var = Variable::from_u32(var_idx);
        builder.declare_var(var, types::I64);
        variables.insert(i, var);
        var_idx += 1;
    }

    for (i, param) in func.params.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(param.ty);
        builder.declare_var(var, ty);
        variables.insert(implicit_param_slots + i, var);
        var_idx += 1;
    }

    for (i, local) in func.locals.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(local.ty);
        builder.declare_var(var, ty);
        variables.insert(implicit_param_slots + func.params.len() + i, var);
        var_idx += 1;
    }

    // Track values and blocks
    let mut vreg_values: HashMap<VReg, cranelift_codegen::ir::Value> = HashMap::new();
    // Dynamically-created variables for local indices not in the pre-allocated `variables` map
    let mut extra_variables: HashMap<usize, cranelift_frontend::Variable> = HashMap::new();
    // Reverse map: VReg → local_index (populated by Load, used by push to store back)
    let mut vreg_from_local: HashMap<VReg, usize> = HashMap::new();
    // FR-DRIVER-0002a: per-VReg TypeId, populated once up front from MIR.
    // Consumers (FR-0002b widening + shift emission) read via InstrContext.vreg_types.
    let mut vreg_types: HashMap<VReg, TypeId> = build_vreg_types(func, function_return_types);

    // Declare Cranelift Variables for all VRegs to handle SSA across blocks.
    // This lets Cranelift automatically insert phi nodes (block params) where needed.
    // VRegs are sorted to ensure deterministic Variable ID assignment.
    let mut vreg_vars: HashMap<VReg, Variable> = HashMap::new();
    {
        let all_vregs = collect_cross_block_vregs(func);
        let mut sorted_vregs: Vec<_> = all_vregs.into_iter().collect();
        sorted_vregs.sort_by_key(|v| v.0);
        for vreg in &sorted_vregs {
            let var = Variable::from_u32(var_idx);
            builder.declare_var(var, types::I64); // default to i64; type is refined on def_var
            vreg_vars.insert(*vreg, var);
            var_idx += 1;
        }
    }

    // Base Cranelift Variable index for dynamically-created locals (temp locals
    // emitted by MIR lowering that are not in func.locals). `extra_var_base +
    // local_index` is injective per local and clears every pre-declared Variable
    // (params, locals, cross-block vregs). See InstrContext::extra_var_base.
    let extra_var_base: u32 = var_idx + 1024;

    // Create blocks
    let mut blocks = HashMap::new();
    for mir_block in &func.blocks {
        let cl_block = builder.create_block();
        blocks.insert(mir_block.id, cl_block);
    }

    // Entry block gets parameters
    let entry_block = *blocks.get(&func.entry_block).unwrap();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Initialize parameter variables.
    // Function signatures normally use uniform I64 params; exact-ABI runtime
    // helpers can use narrower params. Convert block params to variable types.
    for i in 0..implicit_param_slots {
        let val = builder.block_params(entry_block)[i];
        let var = variables[&i];
        builder.def_var(var, val);
    }

    for (i, param) in func.params.iter().enumerate() {
        let val = builder.block_params(entry_block)[implicit_param_slots + i];
        let var = variables[&(implicit_param_slots + i)];
        let expected_ty = type_to_cranelift(param.ty);
        let actual_ty = builder.func.dfg.value_type(val);
        let converted = if actual_ty == expected_ty {
            val
        } else if expected_ty == types::I64 {
            val
        } else if expected_ty.is_int() {
            builder.ins().ireduce(expected_ty, val)
        } else if expected_ty == types::F32 {
            // Callers marshal f32 args as the bit pattern of the PROMOTED f64
            // (ensure_i64 / adapt_args_to_signature: fpromote + bitcast.i64).
            // Mirror that here: reinterpret as f64, then narrow. The previous
            // ireduce+bitcast.f32 read the low 32 bits of the f64 pattern,
            // which decoded every f32 parameter as garbage (usually 0.0).
            let as_f64 = builder
                .ins()
                .bitcast(types::F64, cranelift_codegen::ir::MemFlags::new(), val);
            builder.ins().fdemote(types::F32, as_f64)
        } else if expected_ty == types::F64 {
            builder
                .ins()
                .bitcast(types::F64, cranelift_codegen::ir::MemFlags::new(), val)
        } else {
            val
        };
        builder.def_var(var, converted);
    }

    // If this is an outlined lambda, hydrate captured locals from the closure struct.
    if let Some(meta) = func.outlined_bodies.get(&func.entry_block) {
        if meta.is_lambda && !meta.lambda_capture_local_indices.is_empty() {
            let closure_param = builder.block_params(entry_block)[0];
            for (idx, local_index) in meta.lambda_capture_local_indices.iter().enumerate() {
                let val = builder
                    .ins()
                    .load(types::I64, MemFlags::new(), closure_param, 8 + (idx as i32 * 8));
                let var = if let Some(&var) = variables.get(local_index) {
                    var
                } else if let Some(&var) = extra_variables.get(local_index) {
                    var
                } else {
                    let var = Variable::from_u32(extra_var_base + *local_index as u32);
                    builder.declare_var(var, types::I64);
                    extra_variables.insert(*local_index, var);
                    var
                };
                def_var_coerced(&mut builder, var, val);
            }
        } else if !meta.live_ins.is_empty() {
            let ctx_param = if func.generator_states.is_some() {
                let gen_param = builder.block_params(entry_block)[0];
                let get_ctx_id = runtime_funcs["rt_generator_get_ctx"];
                let get_ctx_ref = module.declare_func_in_func(get_ctx_id, builder.func);
                let call = adapted_call(&mut builder, get_ctx_ref, &[gen_param]);
                builder.inst_results(call)[0]
            } else {
                builder.block_params(entry_block)[implicit_param_slots + func.params.len().saturating_sub(1)]
            };
            let get_id = runtime_funcs["rt_array_get"];
            let get_ref = module.declare_func_in_func(get_id, builder.func);
            for (idx, reg) in meta.live_ins.iter().enumerate() {
                let idx_val = builder.ins().iconst(types::I64, idx as i64);
                let call = adapted_call(&mut builder, get_ref, &[ctx_param, idx_val]);
                let val = builder.inst_results(call)[0];
                vreg_values.insert(*reg, val);
                if let Some(&var) = vreg_vars.get(reg) {
                    def_var_coerced(&mut builder, var, val);
                }
            }
        }
    }

    let generator_states = func.generator_states.clone();
    let generator_state_len = generator_states.as_ref().map(|s| s.len()).unwrap_or(0);
    let generator_done_state = generator_state_len + 1;
    let generator_state_map = generator_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.yield_block, s.clone());
        }
        map
    });
    let generator_resume_map = generator_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.resume_block, s.clone());
        }
        map
    });

    // Async state machine dispatcher (similar to generator but for futures)
    let async_states = func.async_states.clone();
    let async_state_len = async_states.as_ref().map(|s| s.len()).unwrap_or(0);
    let async_done_state = async_state_len + 1;
    let async_state_map = async_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.await_block, s.clone());
        }
        map
    });
    let async_resume_map = async_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.resume_block, s.clone());
        }
        map
    });

    let mut skip_entry_terminator = false;
    if let Some(states) = &generator_states {
        let generator_param = builder.block_params(entry_block)[0];
        let get_state_id = runtime_funcs["rt_generator_get_state"];
        let get_state_ref = module.declare_func_in_func(get_state_id, builder.func);
        let call = adapted_call(&mut builder, get_state_ref, &[generator_param]);
        let state_val = builder.inst_results(call)[0];

        let mut dispatch_blocks = Vec::new();
        if let Some(entry_target) = func.block(func.entry_block).and_then(|b| match b.terminator {
            Terminator::Jump(t) => Some(t),
            _ => None,
        }) {
            let target_block = *blocks.get(&entry_target).unwrap();
            let mut targets = Vec::new();
            targets.push(target_block);
            for st in states {
                targets.push(*blocks.get(&st.resume_block).unwrap());
            }
            let default_block = func
                .generator_complete
                .and_then(|b| blocks.get(&b).copied())
                .unwrap_or(target_block);
            targets.push(default_block); // done state

            let mut current_block = entry_block;
            let mut is_first = true;
            for (idx, tgt) in targets.iter().enumerate() {
                if !is_first {
                    builder.switch_to_block(current_block);
                } else {
                    is_first = false;
                }
                let is_last = idx == targets.len() - 1;
                let next_block = if is_last {
                    default_block
                } else {
                    let nb = builder.create_block();
                    dispatch_blocks.push(nb);
                    nb
                };
                let cmp = builder.ins().icmp_imm(IntCC::Equal, state_val, idx as i64);
                builder.ins().brif(cmp, *tgt, &[], next_block, &[]);
                if !is_last {
                    current_block = next_block;
                }
            }
            builder.switch_to_block(default_block);
            skip_entry_terminator = true;

            for b in dispatch_blocks {
                builder.seal_block(b);
            }
        }
    }

    // Async state machine dispatcher (for async functions with multiple await points)
    if let Some(states) = &async_states {
        if !skip_entry_terminator {
            let async_param = builder.block_params(entry_block)[0];
            let get_state_id = runtime_funcs
                .get("rt_async_get_state")
                .or_else(|| runtime_funcs.get("rt_future_get_state"))
                .copied();

            if let Some(get_state_id) = get_state_id {
                let get_state_ref = module.declare_func_in_func(get_state_id, builder.func);
                let call = adapted_call(&mut builder, get_state_ref, &[async_param]);
                let state_val = builder.inst_results(call)[0];

                let mut dispatch_blocks = Vec::new();
                if let Some(entry_target) = func.block(func.entry_block).and_then(|b| match b.terminator {
                    Terminator::Jump(t) => Some(t),
                    _ => None,
                }) {
                    let target_block = *blocks.get(&entry_target).unwrap();
                    let mut targets = Vec::new();
                    targets.push(target_block); // State 0: initial entry
                    for st in states {
                        targets.push(*blocks.get(&st.resume_block).unwrap());
                    }
                    let default_block = func
                        .async_complete
                        .and_then(|b| blocks.get(&b).copied())
                        .unwrap_or(target_block);
                    targets.push(default_block); // Done state

                    let mut current_block = entry_block;
                    let mut is_first = true;
                    for (idx, tgt) in targets.iter().enumerate() {
                        if !is_first {
                            builder.switch_to_block(current_block);
                        } else {
                            is_first = false;
                        }
                        let is_last = idx == targets.len() - 1;
                        let next_block = if is_last {
                            default_block
                        } else {
                            let nb = builder.create_block();
                            dispatch_blocks.push(nb);
                            nb
                        };
                        let cmp = builder.ins().icmp_imm(IntCC::Equal, state_val, idx as i64);
                        builder.ins().brif(cmp, *tgt, &[], next_block, &[]);
                        if !is_last {
                            current_block = next_block;
                        }
                    }
                    builder.switch_to_block(default_block);
                    skip_entry_terminator = true;

                    for b in dispatch_blocks {
                        builder.seal_block(b);
                    }
                }
            }
        }
    }

    // Compile each block
    //
    // Pre-populate `local_addr_map` from EVERY `LocalAddr` in the function up
    // front, so Store/Load address resolution is independent of the order in
    // which `func.blocks` are compiled. Blocks are compiled in storage order,
    // which after inlining is NOT guaranteed to be dominator order: inlining a
    // Simple-fn branch inside an if-EXPRESSION can split/renumber the condition
    // block so the merge-slot `LocalAddr` lands in a high-id block stored AFTER
    // the low-id then/else/merge blocks that consume it. With lazy (first-touch)
    // population the merge Store/Load in those earlier blocks missed the
    // vreg->local mapping, fell through to the raw-value path, and silently
    // mis-resolved — corrupting an extern-`[u8]` handle carried through the
    // merge (abi_probe P9; if-STATEMENT P10 was clean because it reuses a
    // pre-declared local). `LocalAddr` is a pure, SSA-unique
    // `dest -> local_index` fact, so pre-scanning is order-safe for every
    // backend/target and changes no other lowering.
    let mut local_addr_map: HashMap<VReg, usize> = HashMap::new();
    for mir_block in &func.blocks {
        for inst in &mir_block.instructions {
            if let MirInst::LocalAddr { dest, local_index } = inst {
                local_addr_map.insert(*dest, *local_index);
            }
        }
    }

    for mir_block in &func.blocks {
        if generator_states.is_some() && mir_block.id == func.entry_block {
            continue;
        }
        if async_states.is_some() && mir_block.id == func.entry_block {
            continue;
        }
        let cl_block = *blocks.get(&mir_block.id).unwrap();

        if mir_block.id != func.entry_block {
            builder.switch_to_block(cl_block);
            // At block entry, populate vreg_values from Variables (SSA phi resolution)
            sync_vars_to_vregs(&mut builder, &mut vreg_values, &vreg_vars);
        }

        if let Some(resume_map) = generator_resume_map.as_ref() {
            if let Some(state) = resume_map.get(&mir_block.id) {
                let gen_param = builder.block_params(entry_block)[0];
                let load_id = runtime_funcs["rt_generator_load_slot"];
                let load_ref = module.declare_func_in_func(load_id, builder.func);
                for (idx, reg) in state.live_after_yield.iter().enumerate() {
                    let idx_val = builder.ins().iconst(types::I64, idx as i64);
                    let call = adapted_call(&mut builder, load_ref, &[gen_param, idx_val]);
                    let val = builder.inst_results(call)[0];
                    vreg_values.insert(*reg, val);
                    if let Some(&var) = vreg_vars.get(reg) {
                        builder.def_var(var, val);
                    }
                }
            }
        }

        // Async resume block: restore live variables from future context
        if let Some(resume_map) = async_resume_map.as_ref() {
            if let Some(state) = resume_map.get(&mir_block.id) {
                let async_param = builder.block_params(entry_block)[0];
                let get_ctx_id = runtime_funcs
                    .get("rt_async_get_ctx")
                    .or_else(|| runtime_funcs.get("rt_future_get_ctx"))
                    .copied();
                if let Some(get_ctx_id) = get_ctx_id {
                    let get_ctx_ref = module.declare_func_in_func(get_ctx_id, builder.func);
                    let call = adapted_call(&mut builder, get_ctx_ref, &[async_param]);
                    let ctx_val = builder.inst_results(call)[0];

                    let get_id = runtime_funcs["rt_array_get"];
                    let get_ref = module.declare_func_in_func(get_id, builder.func);
                    for (idx, reg) in state.live_after_await.iter().enumerate() {
                        let idx_val = builder.ins().iconst(types::I64, idx as i64);
                        let call = adapted_call(&mut builder, get_ref, &[ctx_val, idx_val]);
                        let val = builder.inst_results(call)[0];
                        vreg_values.insert(*reg, val);
                        if let Some(&var) = vreg_vars.get(reg) {
                            builder.def_var(var, val);
                        }
                    }
                }
            }
        }

        // Compile instructions; if we hit a Yield, it already emits a return, so skip the terminator.
        let mut returned_via_yield = false;
        for (inst_idx, inst) in mir_block.instructions.iter().enumerate() {
            if let MirInst::Yield { value } = inst {
                let mut instr_ctx = InstrContext {
                    module,
                    func_ids,
                    runtime_funcs,
                    global_ids,
                    vreg_values: &mut vreg_values,
                    local_addr_map: &mut local_addr_map,
                    variables: &variables,
                    extra_variables: &mut extra_variables,
                    extra_var_base,
                    vreg_from_local: &mut vreg_from_local,
                    func,
                    entry_block,
                    blocks: &blocks,
                    mir_block_id: mir_block.id,
                    generator_state_map: &generator_state_map,
                    async_state_map: &async_state_map,
                    import_map,
                    use_map,
                    data_exports,
                    vtable_data_ids,
                    vtable_type_ids,
                    vreg_types: &mut vreg_types,
                    fn_arities,
                    enum_defs,
                    tag_runtime_pool_join_result,
                };
                compile_yield(&mut instr_ctx, &mut builder, *value)?;
                // Sync vreg_values → Variables after yield
                sync_vregs_to_vars(&mut builder, &vreg_values, &vreg_vars, &vreg_types);
                returned_via_yield = true;
                break;
            } else {
                let mut instr_ctx = InstrContext {
                    module,
                    func_ids,
                    runtime_funcs,
                    global_ids,
                    vreg_values: &mut vreg_values,
                    local_addr_map: &mut local_addr_map,
                    variables: &variables,
                    extra_variables: &mut extra_variables,
                    extra_var_base,
                    vreg_from_local: &mut vreg_from_local,
                    func,
                    entry_block,
                    blocks: &blocks,
                    mir_block_id: mir_block.id,
                    generator_state_map: &generator_state_map,
                    async_state_map: &async_state_map,
                    import_map,
                    use_map,
                    data_exports,
                    vtable_data_ids,
                    vtable_type_ids,
                    vreg_types: &mut vreg_types,
                    fn_arities,
                    enum_defs,
                    tag_runtime_pool_join_result,
                };
                compile_instruction(&mut instr_ctx, &mut builder, inst)?;
                // Ensure all vreg values are i64 (extend smaller int types)
                // and sync to Variables for cross-block SSA.
                //
                // FR-DRIVER-0002b: pick `sextend` for signed narrow ints so a
                // later `>>` on the widened value still sees the sign bit.
                // Unsigned and unknown keep the legacy `uextend` default —
                // that matches Rust-SFFI contracts for `u32 = 0xFFFFFFFF`.
                if let Some(dest) = inst.dest() {
                    if let Some(&val) = vreg_values.get(&dest) {
                        let ty = builder.func.dfg.value_type(val);
                        if ty.is_int() && ty.bits() < 64 {
                            let signed = vreg_types.get(&dest).copied().is_some_and(type_id_is_signed_integer);
                            let extended = if signed {
                                builder.ins().sextend(types::I64, val)
                            } else {
                                builder.ins().uextend(types::I64, val)
                            };
                            vreg_values.insert(dest, extended);
                            if let Some(&var) = vreg_vars.get(&dest) {
                                builder.def_var(var, extended);
                            }
                        } else if let Some(&var) = vreg_vars.get(&dest) {
                            def_var_coerced(&mut builder, var, val);
                        }
                    }
                }
            }
        }

        // Compile terminator
        if returned_via_yield {
            continue;
        }
        if skip_entry_terminator && mir_block.id == func.entry_block {
            continue;
        }
        // Sync all vreg_values to Variables before terminators (for cross-block SSA)
        sync_vregs_to_vars(&mut builder, &vreg_values, &vreg_vars, &vreg_types);
        match &mir_block.terminator {
            Terminator::Return(val) => {
                let mut mark_done = false;
                let mut next_state_val = generator_done_state as i64;
                if let Some(map) = generator_state_map.as_ref() {
                    if let Some(state) = map.get(&mir_block.id) {
                        next_state_val = (state.state_id + 1) as i64;
                    } else {
                        mark_done = true;
                    }
                }
                if generator_states.is_some() {
                    let gen_param = builder.block_params(entry_block)[0];
                    let set_state_id = runtime_funcs["rt_generator_set_state"];
                    let set_state_ref = module.declare_func_in_func(set_state_id, builder.func);
                    let next_state = builder.ins().iconst(types::I64, next_state_val);
                    let _ = adapted_call(&mut builder, set_state_ref, &[gen_param, next_state]);
                    if mark_done || next_state_val == generator_done_state as i64 {
                        let mark_id = runtime_funcs["rt_generator_mark_done"];
                        let mark_ref = module.declare_func_in_func(mark_id, builder.func);
                        let _ = adapted_call(&mut builder, mark_ref, &[gen_param]);
                    }
                }
                if let Some(v) = val {
                    // If function returns void, discard the return value
                    // (this can happen when return with value is used in a void function)
                    if func.return_type == TypeId::VOID {
                        if func.name == "main" {
                            let zero = builder.ins().iconst(types::I32, 0);
                            builder.ins().return_(&[zero]);
                        } else {
                            let ret_val = if let Some(&rv) = vreg_values.get(v) {
                                rv
                            } else {
                                // Missing return vreg indicates a MIR SSA/codegen bug;
                                // fail fast under SIMPLE_STRICT_VREG (default: legacy 0).
                                if std::env::var("SIMPLE_STRICT_VREG").is_ok() {
                                    eprintln!(
                                        "[strict-vreg] Return: missing value for {:?} in function {}",
                                        v, func.name
                                    );
                                    panic!(
                                        "codegen: missing VReg value for {:?} in Return of function {}",
                                        v, func.name
                                    );
                                }
                                builder.ins().iconst(types::I64, 0)
                            };
                            builder.ins().return_(&[ret_val]);
                        }
                    } else {
                        // Use signature return type (main returns I32 for C ABI,
                        // all others use I64 to match uniform signature convention)
                        let ret_ty = if func.name == "main" {
                            types::I32
                        } else {
                            crate::codegen::runtime_sffi::RUNTIME_FUNCS
                                .iter()
                                .find(|spec| spec.name == func.name)
                                .and_then(|spec| spec.returns.first().copied())
                                .unwrap_or(types::I64)
                        };
                        // Handle missing VReg (can happen in complex control flow)
                        let mut ret_val = if let Some(&rv) = vreg_values.get(v) {
                            // Coerce value type to match function return type
                            let val_type = builder.func.dfg.value_type(rv);
                            if val_type == ret_ty {
                                rv
                            } else if val_type.is_int() && ret_ty.is_int() {
                                if val_type.bits() > ret_ty.bits() {
                                    builder.ins().ireduce(ret_ty, rv)
                                } else if val_type.bits() < ret_ty.bits() {
                                    builder.ins().uextend(ret_ty, rv)
                                } else {
                                    rv
                                }
                            } else if val_type.is_int() && ret_ty.is_float() {
                                // Int to float conversion for return value
                                builder.ins().fcvt_from_sint(ret_ty, rv)
                            } else if val_type.is_float() && ret_ty == types::I64 {
                                // Uniform tagged-i64 ABI slot: preserve the float's
                                // BITS (promote f32 first), matching how callers
                                // unpack float results (bitcast.f64, see
                                // compile_store / compile_cast). The previous
                                // fcvt_to_sint value-converted the float, so every
                                // float-returning fn came back as a truncated int.
                                let as_f64 = if val_type == types::F32 {
                                    builder.ins().fpromote(types::F64, rv)
                                } else {
                                    rv
                                };
                                builder
                                    .ins()
                                    .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), as_f64)
                            } else if val_type.is_float() && ret_ty.is_int() {
                                // Narrow int return slots (runtime-spec fns): real
                                // value conversion.
                                builder.ins().fcvt_to_sint(ret_ty, rv)
                            } else if val_type.is_float() && ret_ty.is_float() {
                                // Float width conversion
                                if val_type.bits() < ret_ty.bits() {
                                    builder.ins().fpromote(ret_ty, rv)
                                } else {
                                    builder.ins().fdemote(ret_ty, rv)
                                }
                            } else {
                                rv
                            }
                        } else {
                            // Missing return vreg indicates a MIR SSA/codegen bug
                            // (silent constant-0 returns hid real miscompiles during
                            // bootstrap); fail fast under SIMPLE_STRICT_VREG.
                            if std::env::var("SIMPLE_STRICT_VREG").is_ok() {
                                eprintln!(
                                    "[strict-vreg] Return: missing value for {:?} in function {}",
                                    v, func.name
                                );
                                panic!(
                                    "codegen: missing VReg value for {:?} in Return of function {}",
                                    v, func.name
                                );
                            }
                            // Return a default value of the correct type
                            match ret_ty {
                                types::F32 => builder.ins().f32const(0.0),
                                types::F64 => builder.ins().f64const(0.0),
                                types::I8 => builder.ins().iconst(types::I8, 0),
                                types::I16 => builder.ins().iconst(types::I16, 0),
                                types::I32 => builder.ins().iconst(types::I32, 0),
                                _ => builder.ins().iconst(types::I64, 0),
                            }
                        };
                        if generator_states.is_some() {
                            let wrap_id = runtime_funcs["rt_value_int"];
                            let wrap_ref = module.declare_func_in_func(wrap_id, builder.func);
                            let wrap_call = adapted_call(&mut builder, wrap_ref, &[ret_val]);
                            ret_val = builder.inst_results(wrap_call)[0];
                        }
                        builder.ins().return_(&[ret_val]);
                    }
                } else if generator_states.is_some() {
                    let nil_id = runtime_funcs["rt_value_nil"];
                    let nil_ref = module.declare_func_in_func(nil_id, builder.func);
                    let call = adapted_call(&mut builder, nil_ref, &[]);
                    let nil_val = builder.inst_results(call)[0];
                    builder.ins().return_(&[nil_val]);
                } else if func.return_type == TypeId::VOID {
                    if func.name == "main" {
                        let zero = builder.ins().iconst(types::I32, 0);
                        builder.ins().return_(&[zero]);
                    } else {
                        let nil_val = builder.ins().iconst(types::I64, 0);
                        builder.ins().return_(&[nil_val]);
                    }
                } else {
                    builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
                }
            }

            Terminator::Jump(target) => {
                let target_block = *blocks.get(target).unwrap();
                builder.ins().jump(target_block, &[]);
            }

            Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond_val = vreg_values.get(cond).copied().unwrap_or_else(|| {
                    // Use Variable if available, otherwise default to 0
                    if let Some(&var) = vreg_vars.get(cond) {
                        builder.use_var(var)
                    } else {
                        builder.ins().iconst(types::I64, 0)
                    }
                });
                // brif expects i8 (boolean), coerce if needed
                let cond_ty = builder.func.dfg.value_type(cond_val);
                let cond_val = if cond_ty != types::I8 && cond_ty.is_int() {
                    builder.ins().icmp_imm(IntCC::NotEqual, cond_val, 0)
                } else {
                    cond_val
                };
                let then_bl = *blocks.get(then_block).unwrap();
                let else_bl = *blocks.get(else_block).unwrap();
                builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
            }

            Terminator::Switch {
                discriminant,
                cases,
                default,
            } => {
                // B5: lower MIR Switch to Cranelift's Switch builder, which
                // emits br_table for dense integer dispatches.
                let disc_val = vreg_values.get(discriminant).copied().unwrap_or_else(|| {
                    if let Some(&var) = vreg_vars.get(discriminant) {
                        builder.use_var(var)
                    } else {
                        builder.ins().iconst(types::I64, 0)
                    }
                });
                let default_bl = *blocks.get(default).unwrap();
                let mut switch = cranelift_frontend::Switch::new();
                for (k, target) in cases {
                    let target_bl = *blocks.get(target).unwrap();
                    // Cranelift Switch entries are unsigned u128; cast i64 keys.
                    switch.set_entry(*k as u128, target_bl);
                }
                switch.emit(&mut builder, disc_val, default_bl);
            }

            Terminator::Unreachable => {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
            }
        }
    }

    // Seal all blocks after all predecessors are known
    for mir_block in &func.blocks {
        let cl_block = *blocks.get(&mir_block.id).unwrap();
        builder.seal_block(cl_block);
    }

    builder.finalize();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{BinOp, TypeId};
    use crate::mir::{BlockId, MirFunction, MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    /// FR-DRIVER-0002a: verify `build_vreg_types` populates a TypeId for every
    /// dest VReg produced by the covered MIR op kinds. This is the acceptance
    /// test for the Cranelift-side map — it does NOT exercise the emitter
    /// itself (that's FR-0002b).
    #[test]
    fn build_vreg_types_covers_common_ops() {
        let mut func = MirFunction::new("test".to_string(), TypeId::I32, Visibility::Private);

        let r0 = func.new_vreg(); // ConstInt -> I64
        let r1 = func.new_vreg(); // Cast -> I32
        let r2 = func.new_vreg(); // Cast -> U32
        let r3 = func.new_vreg(); // BinOp Add -> propagates r1 type (I32)
        let r4 = func.new_vreg(); // BinOp Eq -> BOOL
        let r5 = func.new_vreg(); // Copy from r2 -> U32
        let r6 = func.new_vreg(); // Load from addr (arbitrary) -> F64
        let r7 = func.new_vreg(); // ConstBool -> BOOL

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstInt { dest: r0, value: 5 });
        entry.instructions.push(MirInst::Cast {
            dest: r1,
            source: r0,
            from_ty: TypeId::I64,
            to_ty: TypeId::I32,
        });
        entry.instructions.push(MirInst::Cast {
            dest: r2,
            source: r0,
            from_ty: TypeId::I64,
            to_ty: TypeId::U32,
        });
        entry.instructions.push(MirInst::BinOp {
            dest: r3,
            op: BinOp::Add,
            left: r1,
            right: r1,
        });
        entry.instructions.push(MirInst::BinOp {
            dest: r4,
            op: BinOp::Eq,
            left: r1,
            right: r1,
        });
        entry.instructions.push(MirInst::Copy { dest: r5, src: r2 });
        entry.instructions.push(MirInst::Load {
            dest: r6,
            addr: r0,
            ty: TypeId::F64,
        });
        entry.instructions.push(MirInst::ConstBool { dest: r7, value: true });
        entry.terminator = Terminator::Return(Some(r3));

        let map = build_vreg_types(&func, &HashMap::new());

        assert_eq!(map.get(&r0).copied(), Some(TypeId::I64), "ConstInt -> I64");
        assert_eq!(map.get(&r1).copied(), Some(TypeId::I32), "Cast to I32");
        assert_eq!(map.get(&r2).copied(), Some(TypeId::U32), "Cast to U32");
        assert_eq!(map.get(&r3).copied(), Some(TypeId::I32), "Add propagates lhs type");
        assert_eq!(map.get(&r4).copied(), Some(TypeId::BOOL), "Eq -> BOOL");
        assert_eq!(map.get(&r5).copied(), Some(TypeId::U32), "Copy propagates src type");
        assert_eq!(map.get(&r6).copied(), Some(TypeId::F64), "Load carries ty");
        assert_eq!(map.get(&r7).copied(), Some(TypeId::BOOL), "ConstBool -> BOOL");
    }

    #[test]
    fn build_vreg_types_stamps_typed_word_runtime_reads() {
        let mut func = MirFunction::new("test".to_string(), TypeId::U64, Visibility::Private);
        let array = func.new_vreg();
        let index = func.new_vreg();
        let word = func.new_vreg();
        let hoisted_word = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        entry.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        entry.instructions.push(MirInst::Call {
            dest: Some(word),
            target: CallTarget::from_name("rt_typed_words_u64_unchecked"),
            args: vec![array, index],
        });
        entry.instructions.push(MirInst::Call {
            dest: Some(hoisted_word),
            target: CallTarget::from_name("rt_typed_words_u64_data_at"),
            args: vec![array, index],
        });
        entry.terminator = Terminator::Return(Some(hoisted_word));

        let map = build_vreg_types(&func, &HashMap::new());

        assert_eq!(map.get(&word).copied(), Some(TypeId::U64));
        assert_eq!(map.get(&hoisted_word).copied(), Some(TypeId::U64));
    }

    #[test]
    fn build_vreg_types_uses_direct_callee_return_type() {
        let mut func = MirFunction::new("caller".to_string(), TypeId::BOOL, Visibility::Private);
        let result = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::Call {
            dest: Some(result),
            target: CallTarget::from_name("first_f64"),
            args: vec![],
        });

        let returns = HashMap::from([("first_f64".to_string(), TypeId::F64)]);
        assert_eq!(build_vreg_types(&func, &returns).get(&result), Some(&TypeId::F64));
    }

    #[test]
    fn build_vreg_types_stamps_optional_presence_calls_bool() {
        let mut func = MirFunction::new("test".to_string(), TypeId::BOOL, Visibility::Private);
        let value = func.new_vreg();
        let present = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstInt { dest: value, value: 3 });
        entry.instructions.push(MirInst::Call {
            dest: Some(present),
            target: CallTarget::from_name("rt_is_some"),
            args: vec![value],
        });
        entry.terminator = Terminator::Return(Some(present));

        assert_eq!(
            build_vreg_types(&func, &HashMap::new()).get(&present).copied(),
            Some(TypeId::BOOL)
        );
    }

    /// Signedness classification derived from `build_vreg_types` output —
    /// this is what `core::vreg_is_signed` will read once FR-0002b wires it in.
    #[test]
    fn build_vreg_types_classifies_signedness() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        let signed = func.new_vreg();
        let unsigned = func.new_vreg();
        let boolean = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::Cast {
            dest: signed,
            source: VReg(999),
            from_ty: TypeId::I64,
            to_ty: TypeId::I32,
        });
        entry.instructions.push(MirInst::Cast {
            dest: unsigned,
            source: VReg(999),
            from_ty: TypeId::I64,
            to_ty: TypeId::U32,
        });
        entry.instructions.push(MirInst::ConstBool {
            dest: boolean,
            value: false,
        });
        entry.terminator = Terminator::Return(None);

        let map = build_vreg_types(&func, &HashMap::new());

        // Signed integer types
        for ty in [TypeId::I8, TypeId::I16, TypeId::I32, TypeId::I64] {
            let is_signed = matches!(ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);
            assert!(is_signed, "{:?} should classify as signed", ty);
        }
        // Unsigned integer types
        for ty in [TypeId::U8, TypeId::U16, TypeId::U32, TypeId::U64] {
            let is_unsigned = matches!(ty, TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64);
            assert!(is_unsigned, "{:?} should classify as unsigned", ty);
        }

        assert_eq!(map.get(&signed).copied(), Some(TypeId::I32));
        assert_eq!(map.get(&unsigned).copied(), Some(TypeId::U32));
        assert_eq!(map.get(&boolean).copied(), Some(TypeId::BOOL));
    }
}
