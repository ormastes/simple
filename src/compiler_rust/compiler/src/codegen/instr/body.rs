// Complete MIR function body compilation.

use cranelift_codegen::ir::{condcodes::IntCC, types, InstBuilder};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::Module;
use std::collections::{HashMap, HashSet};

use crate::hir::{BinOp, TypeId, UnaryOp};
use crate::mir::{BlockId, MirFunction, MirInst, Terminator, VReg};

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

/// Result type of a `BinOp` given the operand types. Comparisons + membership
/// + identity produce BOOL; logical ops produce BOOL; arithmetic / bitwise /
/// shift ops keep the left-operand type (unknown operand → unknown result).
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
pub(super) fn build_vreg_types(func: &MirFunction) -> HashMap<VReg, TypeId> {
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
                MirInst::IndirectCall { dest, return_type, .. } => {
                    if let Some(d) = dest {
                        types_map.insert(*d, *return_type);
                    }
                }
                MirInst::MethodCallVirtual { dest, return_type, .. } => {
                    if let Some(d) = dest {
                        types_map.insert(*d, *return_type);
                    }
                }
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

/// Coerce a value to i64 for storage in a Variable declared as i64.
fn coerce_to_i64(builder: &mut FunctionBuilder, val: cranelift_codegen::ir::Value) -> cranelift_codegen::ir::Value {
    let ty = builder.func.dfg.value_type(val);
    if ty == types::I64 {
        val
    } else if ty.is_int() && ty.bits() < 64 {
        builder.ins().uextend(types::I64, val)
    } else if ty.is_int() && ty.bits() > 64 {
        builder.ins().ireduce(types::I64, val)
    } else if ty.is_float() {
        builder
            .ins()
            .bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val)
    } else {
        // For vector types etc., just use as-is (will be i64 in most cases)
        val
    }
}

/// Safely def_var with type coercion to i64.
fn def_var_coerced(builder: &mut FunctionBuilder, var: Variable, val: cranelift_codegen::ir::Value) {
    let coerced = coerce_to_i64(builder, val);
    builder.def_var(var, coerced);
}

/// Sync vreg_values → Variables: call def_var for all vregs that have values.
/// VRegs are sorted to ensure deterministic Variable definition order.
fn sync_vregs_to_vars(
    builder: &mut FunctionBuilder,
    vreg_values: &HashMap<VReg, cranelift_codegen::ir::Value>,
    vreg_vars: &HashMap<VReg, Variable>,
) {
    let mut sorted: Vec<_> = vreg_values.iter().collect();
    sorted.sort_by_key(|(v, _)| v.0);
    for (vreg, &val) in sorted {
        if let Some(&var) = vreg_vars.get(vreg) {
            def_var_coerced(builder, var, val);
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
#[allow(clippy::too_many_arguments)]
pub fn compile_function_body<M: Module>(
    module: &mut M,
    cranelift_func: &mut cranelift_codegen::ir::Function,
    func: &MirFunction,
    func_ids: &mut std::collections::BTreeMap<String, cranelift_module::FuncId>,
    runtime_funcs: &HashMap<&'static str, cranelift_module::FuncId>,
    global_ids: &std::collections::BTreeMap<String, cranelift_module::DataId>,
    import_map: &std::sync::Arc<std::collections::HashMap<String, String>>,
    use_map: &std::collections::HashMap<String, String>,
    vtable_data_ids: &std::collections::BTreeMap<String, cranelift_module::DataId>,
    vtable_type_ids: &std::collections::BTreeMap<crate::hir::TypeId, cranelift_module::DataId>,
) -> InstrResult<()> {
    let mut func_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(cranelift_func, &mut func_ctx);

    // Create variables for parameters and locals
    let mut variables = HashMap::new();
    let mut var_idx = 0u32;

    for (i, param) in func.params.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(param.ty);
        builder.declare_var(var, ty);
        variables.insert(i, var);
        var_idx += 1;
    }

    for (i, local) in func.locals.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(local.ty);
        builder.declare_var(var, ty);
        variables.insert(func.params.len() + i, var);
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
    let mut vreg_types: HashMap<VReg, TypeId> = build_vreg_types(func);

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
    // Function signature uses uniform I64 for all params, but variables may be
    // declared with narrower types. Convert block params to match variable types.
    for (i, param) in func.params.iter().enumerate() {
        let val = builder.block_params(entry_block)[i]; // Always I64 from signature
        let var = variables[&i];
        let expected_ty = type_to_cranelift(param.ty);
        let converted = if expected_ty == types::I64 {
            val
        } else if expected_ty.is_int() {
            builder.ins().ireduce(expected_ty, val)
        } else if expected_ty == types::F32 {
            let as_i32 = builder.ins().ireduce(types::I32, val);
            builder
                .ins()
                .bitcast(types::F32, cranelift_codegen::ir::MemFlags::new(), as_i32)
        } else if expected_ty == types::F64 {
            builder
                .ins()
                .bitcast(types::F64, cranelift_codegen::ir::MemFlags::new(), val)
        } else {
            val
        };
        builder.def_var(var, converted);
    }

    // If this is an outlined body with captures, load them from ctx (last param).
    if let Some(meta) = func.outlined_bodies.get(&func.entry_block) {
        if !meta.live_ins.is_empty() {
            let ctx_param = if func.generator_states.is_some() {
                let gen_param = builder.block_params(entry_block)[0];
                let get_ctx_id = runtime_funcs["rt_generator_get_ctx"];
                let get_ctx_ref = module.declare_func_in_func(get_ctx_id, builder.func);
                let call = adapted_call(&mut builder, get_ctx_ref, &[gen_param]);
                builder.inst_results(call)[0]
            } else {
                builder.block_params(entry_block)[func.params.len().saturating_sub(1)]
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
    let mut local_addr_map: HashMap<VReg, usize> = HashMap::new();

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
                    vreg_from_local: &mut vreg_from_local,
                    func,
                    entry_block,
                    blocks: &blocks,
                    mir_block_id: mir_block.id,
                    generator_state_map: &generator_state_map,
                    async_state_map: &async_state_map,
                    import_map,
                    use_map,
                    vtable_data_ids,
                    vtable_type_ids,
                    vreg_types: &mut vreg_types,
                };
                compile_yield(&mut instr_ctx, &mut builder, *value)?;
                // Sync vreg_values → Variables after yield
                sync_vregs_to_vars(&mut builder, &vreg_values, &vreg_vars);
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
                    vreg_from_local: &mut vreg_from_local,
                    func,
                    entry_block,
                    blocks: &blocks,
                    mir_block_id: mir_block.id,
                    generator_state_map: &generator_state_map,
                    async_state_map: &async_state_map,
                    import_map,
                    use_map,
                    vtable_data_ids,
                    vtable_type_ids,
                    vreg_types: &mut vreg_types,
                };
                compile_instruction(&mut instr_ctx, &mut builder, inst)?;
                // Ensure all vreg values are i64 (extend smaller int types)
                // and sync to Variables for cross-block SSA.
                //
                // FR-DRIVER-0002b: pick `sextend` for signed narrow ints so a
                // later `>>` on the widened value still sees the sign bit.
                // Unsigned and unknown keep the legacy `uextend` default —
                // that matches Rust-FFI contracts for `u32 = 0xFFFFFFFF`.
                if let Some(dest) = inst.dest() {
                    if let Some(&val) = vreg_values.get(&dest) {
                        let ty = builder.func.dfg.value_type(val);
                        if ty.is_int() && ty.bits() < 64 {
                            let signed = matches!(
                                vreg_types.get(&dest).copied(),
                                Some(TypeId::I8) | Some(TypeId::I16) | Some(TypeId::I32) | Some(TypeId::I64)
                            );
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
        sync_vregs_to_vars(&mut builder, &vreg_values, &vreg_vars);
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
                            // C main() must return 0 for success
                            let zero = builder.ins().iconst(types::I32, 0);
                            builder.ins().return_(&[zero]);
                        } else {
                            builder.ins().return_(&[]);
                        }
                    } else {
                        // Use signature return type (main returns I32 for C ABI,
                        // all others use I64 to match uniform signature convention)
                        let ret_ty = if func.name == "main" {
                            types::I32
                        } else {
                            // Signature uses I64 for all non-main returns
                            types::I64
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
                            } else if val_type.is_float() && ret_ty.is_int() {
                                // Float to int conversion for return value
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
                        builder.ins().return_(&[]);
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

        let map = build_vreg_types(&func);

        assert_eq!(map.get(&r0).copied(), Some(TypeId::I64), "ConstInt -> I64");
        assert_eq!(map.get(&r1).copied(), Some(TypeId::I32), "Cast to I32");
        assert_eq!(map.get(&r2).copied(), Some(TypeId::U32), "Cast to U32");
        assert_eq!(map.get(&r3).copied(), Some(TypeId::I32), "Add propagates lhs type");
        assert_eq!(map.get(&r4).copied(), Some(TypeId::BOOL), "Eq -> BOOL");
        assert_eq!(map.get(&r5).copied(), Some(TypeId::U32), "Copy propagates src type");
        assert_eq!(map.get(&r6).copied(), Some(TypeId::F64), "Load carries ty");
        assert_eq!(map.get(&r7).copied(), Some(TypeId::BOOL), "ConstBool -> BOOL");
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

        let map = build_vreg_types(&func);

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
