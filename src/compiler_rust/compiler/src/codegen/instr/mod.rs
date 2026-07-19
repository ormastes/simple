//! Unified instruction compilation for both AOT (cranelift.rs) and JIT (jit.rs) backends.
//!
//! This module provides instruction compilation that works with any Cranelift Module type,
//! eliminating the duplication between cranelift_instr.rs and jit_instr.rs.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};

use crate::hir::{BinOp, PointerKind, TypeId, UnaryOp};
use crate::mir::{
    BindingStep, BlockId, ContractKind, FStringPart, MirFunction, MirInst, MirLiteral, MirPattern, ParallelBackend,
    PatternBinding, Terminator, UnitOverflowBehavior, VReg,
};

use super::shared::get_func_block_addr;
use super::types_util::{type_id_size, type_id_to_cranelift, type_to_cranelift};

// Declare submodules
pub mod actors;
pub mod async_ops;
pub mod basic_ops;
pub mod body;
pub mod calls;
pub mod closures_structs;
pub mod collections;
pub mod constants;
pub mod contracts;
pub mod core;
pub mod coverage;
pub mod enum_union;
pub mod extern_classes;
pub mod fields;
pub mod helpers;
pub mod interpreter;
pub mod memory;
pub mod methods;
pub mod parallel;
pub mod pattern;
pub mod pointers;
pub mod result;
pub mod simd_stubs;
pub mod units;

// Re-export key functions for backward compatibility
pub use body::compile_function_body;

// Import compile_* functions from submodules for use in compile_instruction
use actors::{
    compile_actor_join, compile_actor_recv, compile_actor_reply, compile_actor_send, compile_await,
    compile_generator_next,
};
use async_ops::{compile_actor_spawn, compile_future_create, compile_generator_create, compile_yield};
use basic_ops::{compile_cast, compile_copy, compile_spread, compile_unary_op};
use calls::compile_call;
use closures_structs::{
    compile_closure_create, compile_indirect_call, compile_method_call_static, compile_method_call_virtual,
    compile_struct_init,
};
use collections::{
    compile_array_lit, compile_const_string, compile_dict_lit, compile_fstring_format, compile_gpu_atomic,
    compile_gpu_atomic_cmpxchg, compile_index_get, compile_index_set, compile_slice_op, compile_tuple_lit,
    compile_vec_blend, compile_vec_extract, compile_vec_lit, compile_vec_math, compile_vec_reduction,
    compile_vec_select, compile_vec_shuffle, compile_vec_with,
};
use constants::{compile_const_bool, compile_const_float, compile_const_int, compile_const_symbol};
use contracts::compile_contract_check;
use core::{compile_binop, compile_builtin_io_call, compile_interp_call, vreg_is_signed};
use coverage::{compile_condition_probe, compile_decision_probe, compile_path_probe};
use enum_union::{
    compile_enum_discriminant, compile_enum_payload, compile_union_discriminant, compile_union_payload,
    compile_union_wrap,
};
use extern_classes::compile_extern_method_call;
use fields::{compile_field_get, compile_field_set};
use interpreter::{compile_contract_old_capture, compile_interp_eval};
use memory::{compile_gc_alloc, compile_get_element_ptr, compile_load, compile_local_addr, compile_store, compile_wait};
use methods::compile_builtin_method;
use parallel::{compile_par_filter, compile_par_for_each, compile_par_map, compile_par_reduce};
use pattern::{compile_enum_unit, compile_enum_with, compile_pattern_bind, compile_pattern_test};
use pointers::{compile_pointer_deref, compile_pointer_new, compile_pointer_ref};
use result::{compile_option_none, compile_option_some, compile_result_err, compile_result_ok, compile_try_unwrap};
use simd_stubs::{
    compile_neighbor_load, compile_vec_clamp, compile_vec_fma, compile_vec_gather, compile_vec_load,
    compile_vec_masked_load, compile_vec_masked_store, compile_vec_max_vec, compile_vec_min_vec, compile_vec_recip,
    compile_vec_scatter, compile_vec_store,
};
use units::{compile_unit_bound_check, compile_unit_narrow, compile_unit_saturate, compile_unit_widen};

/// Context for instruction compilation, holding all state needed to compile MIR instructions.
pub struct InstrContext<'a, M: Module> {
    pub module: &'a mut M,
    pub func_ids: &'a mut std::collections::BTreeMap<String, cranelift_module::FuncId>,
    pub runtime_funcs: &'a HashMap<&'static str, cranelift_module::FuncId>,
    pub global_ids: &'a std::collections::BTreeMap<String, cranelift_module::DataId>,
    pub vreg_values: &'a mut HashMap<VReg, cranelift_codegen::ir::Value>,
    pub local_addr_map: &'a mut HashMap<VReg, usize>,
    pub variables: &'a HashMap<usize, cranelift_frontend::Variable>,
    /// Dynamically-created variables for local indices not pre-allocated in `variables`.
    /// MIR lowering can create temp locals beyond the pre-allocated count.
    pub extra_variables: &'a mut HashMap<usize, cranelift_frontend::Variable>,
    /// Base Cranelift Variable index for dynamically-created locals.
    /// Computed once per function as (params + locals + cross-block vregs) + margin,
    /// so `extra_var_base + local_index` is injective per local and can never
    /// collide with pre-declared Variables. (The previous formula
    /// `variables.len() + extra_variables.len() + 1000 + local_index` depended on
    /// first-touch order: locals A and B collided whenever
    /// A + extras_at_first_touch(A) == B + extras_at_first_touch(B), silently
    /// aliasing two distinct locals onto one Variable — see flat_ast_to_module
    /// stage4 SIGSEGV, 2026-06-10.)
    pub extra_var_base: u32,
    /// Reverse map: VReg → local_index, for VRegs produced by Load from a local.
    /// Used by push codegen to store the new array pointer back to the local Variable.
    pub vreg_from_local: &'a mut HashMap<VReg, usize>,
    pub func: &'a MirFunction,
    pub entry_block: cranelift_codegen::ir::Block,
    pub blocks: &'a HashMap<BlockId, cranelift_codegen::ir::Block>,
    pub mir_block_id: BlockId,
    pub generator_state_map: &'a Option<HashMap<BlockId, crate::mir::GeneratorState>>,
    pub async_state_map: &'a Option<HashMap<BlockId, crate::mir::AsyncState>>,
    /// Import map for cross-module function resolution (raw name → mangled name).
    pub import_map: &'a std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Per-module use map: local imported name → mangled name from `use` statements.
    pub use_map: &'a std::collections::HashMap<String, String>,
    /// Mangled module-level data exports, used to distinguish imported data from
    /// imported functions when lowering cross-module GlobalLoad.
    pub data_exports: &'a std::sync::Arc<std::collections::HashSet<String>>,
    /// Vtable data IDs: struct_name → DataId for trait-impl structs.
    /// Used by compile_struct_init to write vtable_ptr at offset 0.
    pub vtable_data_ids: &'a std::collections::BTreeMap<String, cranelift_module::DataId>,
    /// Vtable data IDs by TypeId (HIR TypeId → DataId).
    /// Used by MirInst::StructInit which has type_id, not struct_name.
    pub vtable_type_ids: &'a std::collections::BTreeMap<crate::hir::TypeId, cranelift_module::DataId>,
    /// Per-VReg TypeId map derived from MIR.
    ///
    /// Mirrors the SPIR-V backend's `vreg_types` field (spirv_builder.rs:66). Populated
    /// once up front from `MirFunction` by `body::build_vreg_types` and passed through
    /// by `&mut` so future widening / binop helpers can dispatch on signedness.
    ///
    /// FR-DRIVER-0002a infrastructure — currently read-only for consumers; written only
    /// during the pre-emit walk. Missing entries mean "unknown type" (treat as signed by
    /// default when FR-0002b lands).
    pub vreg_types: &'a mut HashMap<VReg, TypeId>,
    /// Mangled function name → declared parameter count for cross-module free functions.
    pub fn_arities: &'a std::sync::Arc<std::collections::HashMap<String, usize>>,
    /// Global enum definitions with payload field types.
    pub enum_defs:
        &'a std::sync::Arc<std::collections::HashMap<String, Vec<(String, Option<Vec<simple_parser::Type>>)>>>,
    /// Native-project builds currently lower escaped runtime-pool closure
    /// returns as raw typed integers. Regular interpreter/native paths already
    /// pass a Simple RuntimeValue through rt_pool_join.
    pub tag_runtime_pool_join_result: bool,
}

impl<'a, M: Module> InstrContext<'a, M> {
    /// Get a vreg value, returning an error instead of panicking if not found
    pub fn get_vreg(&self, vreg: &VReg) -> InstrResult<cranelift_codegen::ir::Value> {
        self.vreg_values
            .get(vreg)
            .copied()
            .ok_or_else(|| format!("vreg {:?} not found in vreg_values", vreg))
    }

    /// Construct a minimal `InstrContext` for integration tests.
    ///
    /// Accepts a `HashMap<String, FuncId>` (which tests hold naturally) and
    /// leaks the keys to produce the `&'static str` keys required by the field.
    /// All auxiliary maps are heap-allocated and leaked for `'static` lifetime.
    ///
    /// # Safety / leaks
    /// This function leaks memory intentionally — it is only for test use.
    #[doc(hidden)]
    pub fn new_for_test(
        module: &'a mut M,
        runtime_funcs_by_string: &HashMap<String, cranelift_module::FuncId>,
    ) -> InstrContext<'a, M> {
        use crate::hir::TypeId;
        use crate::mir::MirFunction;
        use simple_parser::ast::Visibility;

        // Convert String keys → &'static str via Box::leak
        let mut static_map: HashMap<&'static str, cranelift_module::FuncId> =
            HashMap::with_capacity(runtime_funcs_by_string.len());
        for (k, v) in runtime_funcs_by_string {
            let leaked: &'static str = Box::leak(k.clone().into_boxed_str());
            static_map.insert(leaked, *v);
        }
        let runtime_funcs: &'static HashMap<&'static str, cranelift_module::FuncId> = Box::leak(Box::new(static_map));

        // Leak auxiliary maps so we can take &'a mut references
        let func_ids: &'a mut std::collections::BTreeMap<String, cranelift_module::FuncId> =
            Box::leak(Box::new(std::collections::BTreeMap::new()));
        let global_ids: &'static std::collections::BTreeMap<String, cranelift_module::DataId> =
            Box::leak(Box::new(std::collections::BTreeMap::new()));
        let vreg_values: &'a mut HashMap<VReg, cranelift_codegen::ir::Value> = Box::leak(Box::new(HashMap::new()));
        let local_addr_map: &'a mut HashMap<VReg, usize> = Box::leak(Box::new(HashMap::new()));
        let variables: &'static HashMap<usize, cranelift_frontend::Variable> = Box::leak(Box::new(HashMap::new()));
        let extra_variables: &'a mut HashMap<usize, cranelift_frontend::Variable> = Box::leak(Box::new(HashMap::new()));
        let vreg_from_local: &'a mut HashMap<VReg, usize> = Box::leak(Box::new(HashMap::new()));
        let blocks: &'static HashMap<BlockId, cranelift_codegen::ir::Block> = Box::leak(Box::new(HashMap::new()));
        let generator_state_map: &'static Option<HashMap<BlockId, crate::mir::GeneratorState>> =
            Box::leak(Box::new(None));
        let async_state_map: &'static Option<HashMap<BlockId, crate::mir::AsyncState>> = Box::leak(Box::new(None));
        let import_map: &'static std::sync::Arc<std::collections::HashMap<String, String>> =
            Box::leak(Box::new(std::sync::Arc::new(std::collections::HashMap::new())));
        let use_map: &'static std::collections::HashMap<String, String> =
            Box::leak(Box::new(std::collections::HashMap::new()));
        let fn_arities: &'static std::sync::Arc<std::collections::HashMap<String, usize>> =
            Box::leak(Box::new(std::sync::Arc::new(std::collections::HashMap::new())));
        let enum_defs: &'static std::sync::Arc<
            std::collections::HashMap<String, Vec<(String, Option<Vec<simple_parser::Type>>)>>,
        > = Box::leak(Box::new(std::sync::Arc::new(std::collections::HashMap::new())));
        let data_exports: &'static std::sync::Arc<std::collections::HashSet<String>> =
            Box::leak(Box::new(std::sync::Arc::new(std::collections::HashSet::new())));
        let vtable_data_ids: &'static std::collections::BTreeMap<String, cranelift_module::DataId> =
            Box::leak(Box::new(std::collections::BTreeMap::new()));
        let vtable_type_ids: &'static std::collections::BTreeMap<TypeId, cranelift_module::DataId> =
            Box::leak(Box::new(std::collections::BTreeMap::new()));
        let vreg_types: &'a mut HashMap<VReg, TypeId> = Box::leak(Box::new(HashMap::new()));

        // Minimal dummy MirFunction
        let func: &'static MirFunction = Box::leak(Box::new(MirFunction::new(
            "__test__".to_string(),
            TypeId::I64,
            Visibility::Private,
        )));

        // Dummy entry block (block 0)
        let entry_block = cranelift_codegen::ir::Block::with_number(0).unwrap();

        InstrContext {
            module,
            func_ids,
            runtime_funcs,
            global_ids,
            vreg_values,
            local_addr_map,
            variables,
            extra_variables,
            extra_var_base: 1000,
            vreg_from_local,
            func,
            entry_block,
            blocks,
            mir_block_id: BlockId(0),
            generator_state_map,
            async_state_map,
            import_map,
            use_map,
            data_exports,
            vtable_data_ids,
            vtable_type_ids,
            vreg_types,
            fn_arities,
            enum_defs,
            tag_runtime_pool_join_result: false,
        }
    }
}

/// Result type for instruction compilation - uses String errors for genericity
pub type InstrResult<T> = Result<T, String>;

fn looks_like_const_data_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
}

/// Adjust a MIR field byte-offset for the 8-byte vtable pointer that
/// trait-implementing structs carry at offset 0.
///
/// MIR lowering emits raw `field_index * 8` offsets with no vtable header
/// awareness; the StructInit codegen arm shifts them +8 when the struct type
/// appears in `vtable_type_ids` (the authoritative set of types that actually
/// got a vtable data object emitted). Field access must mirror that shift, or
/// `obj.field0` loads the vtable slot instead of the field. Keyed on the same
/// `vtable_type_ids` map so constructor writes and field reads can never
/// disagree. When the receiver's static type is unknown (not in `vreg_types`)
/// or has no vtable, the offset is returned unchanged.
fn effective_field_offset<M: Module>(ctx: &InstrContext<'_, M>, object: VReg, byte_offset: u32) -> u32 {
    if let Some(&type_id) = ctx.vreg_types.get(&object) {
        if ctx.vtable_type_ids.contains_key(&type_id) {
            return byte_offset + 8;
        }
    }
    byte_offset
}

pub fn compile_instruction<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    inst: &MirInst,
) -> InstrResult<()> {
    match inst {
        MirInst::ConstInt { dest, value } => {
            compile_const_int(ctx, builder, *dest, *value)?;
        }

        MirInst::ConstFloat { dest, value } => {
            compile_const_float(ctx, builder, *dest, *value)?;
        }

        MirInst::ConstBool { dest, value } => {
            compile_const_bool(ctx, builder, *dest, *value)?;
        }

        MirInst::Copy { dest, src } => {
            compile_copy(ctx, builder, *dest, *src)?;
        }

        MirInst::BinOp { dest, op, left, right } => {
            let lhs = ctx.vreg_values.get(left).copied().unwrap_or_else(|| {
                // Missing VReg, use default 0
                builder.ins().iconst(types::I64, 0)
            });
            let rhs = ctx.vreg_values.get(right).copied().unwrap_or_else(|| {
                // Missing VReg, use default 0
                builder.ins().iconst(types::I64, 0)
            });
            // FR-DRIVER-0002b: pass VRegs through so compile_binop can read
            // operand signedness from `ctx.vreg_types` for sshr/ushr dispatch.
            let val = compile_binop(ctx, builder, *op, lhs, rhs, *left, *right)?;
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::Cast {
            dest,
            source,
            from_ty,
            to_ty,
        } => {
            compile_cast(ctx, builder, *dest, *source, *from_ty, *to_ty)?;
        }

        MirInst::LocalAddr { dest, local_index } => {
            compile_local_addr(ctx, builder, *dest, *local_index)?;
        }

        MirInst::Load { dest, addr, .. } => {
            compile_load(ctx, builder, *dest, *addr)?;
        }

        MirInst::Store { addr, value, .. } => {
            compile_store(ctx, builder, *addr, *value)?;
        }

        MirInst::GlobalLoad { dest, global_name, ty } => {
            if let Some(global_id) = ctx.global_ids.get(global_name) {
                let global_ref = ctx.module.declare_data_in_func(*global_id, builder.func);
                let global_addr = builder.ins().global_value(types::I64, global_ref);
                let val = builder
                    .ins()
                    .load(type_id_to_cranelift(*ty), MemFlags::new(), global_addr, 0);
                ctx.vreg_values.insert(*dest, val);
            } else if looks_like_const_data_name(global_name) {
                if let Some(resolved) = ctx
                    .use_map
                    .get(global_name.as_str())
                    .or_else(|| ctx.import_map.get(global_name.as_str()))
                {
                    let symbol = resolved.replace('.', "_dot_");
                    match ctx
                        .module
                        .declare_data(&symbol, cranelift_module::Linkage::Import, true, false)
                    {
                        Ok(data_id) => {
                            let global_ref = ctx.module.declare_data_in_func(data_id, builder.func);
                            let global_addr = builder.ins().global_value(types::I64, global_ref);
                            let val = builder
                                .ins()
                                .load(type_id_to_cranelift(*ty), MemFlags::new(), global_addr, 0);
                            ctx.vreg_values.insert(*dest, val);
                        }
                        Err(_) => {
                            let val = builder.ins().iconst(types::I64, 0);
                            ctx.vreg_values.insert(*dest, val);
                        }
                    }
                } else {
                    let val = builder.ins().iconst(types::I64, 0);
                    ctx.vreg_values.insert(*dest, val);
                }
            } else if let Some(&func_id) = ctx.func_ids.get(global_name) {
                // Function reference used as a value (e.g., from MIR GlobalLoad of an
                // imported function). Materialize it as the same heap closure shape
                // used by ClosureCreate so values survive parameter passing and array
                // storage before a later IndirectCall.
                let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                let closure_size = builder.ins().iconst(types::I64, 16);
                let closure_ptr = helpers::call_runtime_1(ctx, builder, "rt_alloc", closure_size);
                let fn_addr = builder.ins().func_addr(types::I64, func_ref);
                let direct_marker = builder.ins().iconst(types::I64, 0x5344_4952_4543_5446);
                builder.ins().store(MemFlags::new(), fn_addr, closure_ptr, 0);
                builder.ins().store(MemFlags::new(), direct_marker, closure_ptr, 8);
                ctx.vreg_values.insert(*dest, closure_ptr);
            } else if let Some(resolved) = ctx
                .use_map
                .get(global_name.as_str())
                .or_else(|| ctx.import_map.get(global_name.as_str()))
            {
                let symbol = resolved.replace('.', "_dot_");
                let is_data_export = ctx.data_exports.contains(resolved) || ctx.data_exports.contains(&symbol);
                if is_data_export {
                    match ctx
                        .module
                        .declare_data(&symbol, cranelift_module::Linkage::Import, true, false)
                    {
                        Ok(data_id) => {
                            let global_ref = ctx.module.declare_data_in_func(data_id, builder.func);
                            let global_addr = builder.ins().global_value(types::I64, global_ref);
                            let val = builder
                                .ins()
                                .load(type_id_to_cranelift(*ty), MemFlags::new(), global_addr, 0);
                            ctx.vreg_values.insert(*dest, val);
                        }
                        Err(_) => {
                            let val = builder.ins().iconst(types::I64, 0);
                            ctx.vreg_values.insert(*dest, val);
                        }
                    }
                } else {
                    // Cross-module function reference used as a value.
                    // Data exports are handled above so imported top-level vals do
                    // not get lowered to function addresses.
                    let call_conv = crate::codegen::shared::platform_call_conv();
                    let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
                    sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                    sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                    if let Ok(fid) = ctx
                        .module
                        .declare_function(&symbol, cranelift_module::Linkage::Import, &sig)
                    {
                        ctx.func_ids.entry(global_name.clone()).or_insert(fid);
                        let func_ref = ctx.module.declare_func_in_func(fid, builder.func);
                        let closure_size = builder.ins().iconst(types::I64, 16);
                        let closure_ptr = helpers::call_runtime_1(ctx, builder, "rt_alloc", closure_size);
                        let fn_addr = builder.ins().func_addr(types::I64, func_ref);
                        let direct_marker = builder.ins().iconst(types::I64, 0x5344_4952_4543_5446);
                        builder.ins().store(MemFlags::new(), fn_addr, closure_ptr, 0);
                        builder.ins().store(MemFlags::new(), direct_marker, closure_ptr, 8);
                        ctx.vreg_values.insert(*dest, closure_ptr);
                    } else {
                        match ctx
                            .module
                            .declare_data(&symbol, cranelift_module::Linkage::Import, true, false)
                        {
                            Ok(data_id) => {
                                let global_ref = ctx.module.declare_data_in_func(data_id, builder.func);
                                let global_addr = builder.ins().global_value(types::I64, global_ref);
                                let val =
                                    builder
                                        .ins()
                                        .load(type_id_to_cranelift(*ty), MemFlags::new(), global_addr, 0);
                                ctx.vreg_values.insert(*dest, val);
                            }
                            Err(_) => {
                                let val = builder.ins().iconst(types::I64, 0);
                                ctx.vreg_values.insert(*dest, val);
                            }
                        }
                    }
                }
            } else {
                // Truly unresolved - likely a local variable that MIR incorrectly
                // treated as a global. Use zero to allow compilation to proceed.
                let val = builder.ins().iconst(types::I64, 0);
                ctx.vreg_values.insert(*dest, val);
            }
        }

        MirInst::GlobalStore { global_name, value, ty } => {
            if let Some(global_id) = ctx.global_ids.get(global_name) {
                let global_ref = ctx.module.declare_data_in_func(*global_id, builder.func);
                let global_addr = builder.ins().global_value(types::I64, global_ref);
                let val = ctx
                    .vreg_values
                    .get(value)
                    .ok_or_else(|| format!("GlobalStore: vreg {:?} not found", value))?;
                builder.ins().store(MemFlags::new(), *val, global_addr, 0);
            } else if let Some(resolved) = ctx
                .use_map
                .get(global_name.as_str())
                .or_else(|| ctx.import_map.get(global_name.as_str()))
            {
                // Cross-module global store: resolve via import/use maps
                let symbol = resolved.replace('.', "_dot_");
                if let Ok(data_id) = ctx
                    .module
                    .declare_data(&symbol, cranelift_module::Linkage::Import, true, false)
                {
                    let global_ref = ctx.module.declare_data_in_func(data_id, builder.func);
                    let global_addr = builder.ins().global_value(types::I64, global_ref);
                    let val = ctx
                        .vreg_values
                        .get(value)
                        .ok_or_else(|| format!("GlobalStore: vreg {:?} not found", value))?;
                    builder.ins().store(MemFlags::new(), *val, global_addr, 0);
                }
            }
            // If still not found, silently skip the store
        }

        MirInst::UnaryOp { dest, op, operand } => {
            compile_unary_op(ctx, builder, *dest, *op, *operand)?;
        }

        MirInst::Call { dest, target, args } => {
            compile_call(ctx, builder, dest, target, args)?;
        }

        MirInst::InlineAsm { instructions, volatile } => {
            let symbol = crate::codegen::inline_asm::register_inline_asm(instructions, *volatile);
            let func_id = if let Some(func_id) = ctx.func_ids.get(&symbol).copied() {
                func_id
            } else {
                let sig = Signature::new(super::shared::platform_call_conv());
                let func_id = ctx
                    .module
                    .declare_function(&symbol, Linkage::Import, &sig)
                    .map_err(|e| e.to_string())?;
                ctx.func_ids.insert(symbol, func_id);
                func_id
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            builder.ins().call(func_ref, &[]);
        }

        MirInst::GetElementPtr { dest, base, index } => {
            compile_get_element_ptr(ctx, builder, *dest, *base, *index)?;
        }

        MirInst::GcAlloc { dest, ty } => {
            compile_gc_alloc(ctx, builder, *dest, *ty)?;
        }

        MirInst::Wait { dest, target } => {
            compile_wait(ctx, builder, *dest, *target)?;
        }

        MirInst::InterpCall {
            dest,
            func_name,
            args,
            boxed_result,
        } => {
            compile_interp_call(ctx, builder, dest, func_name, args, *boxed_result)?;
        }

        MirInst::InterpEval { dest, expr_index } => {
            compile_interp_eval(ctx, builder, *dest, *expr_index as usize)?;
        }

        MirInst::ArrayLit { dest, elements } => {
            compile_array_lit(ctx, builder, *dest, elements);
        }

        MirInst::TupleLit { dest, elements } => {
            compile_tuple_lit(ctx, builder, *dest, elements);
        }

        MirInst::VecLit { dest, elements } => {
            compile_vec_lit(ctx, builder, *dest, elements);
        }

        MirInst::VecSum { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_sum");
        }

        MirInst::VecProduct { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_product");
        }

        MirInst::VecMin { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_min");
        }

        MirInst::VecMax { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_max");
        }

        MirInst::VecAll { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_all");
        }

        MirInst::VecAny { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_any");
        }

        MirInst::VecExtract { dest, vector, index } => {
            compile_vec_extract(ctx, builder, *dest, *vector, *index);
        }

        MirInst::VecWith {
            dest,
            vector,
            index,
            value,
        } => {
            compile_vec_with(ctx, builder, *dest, *vector, *index, *value);
        }

        MirInst::VecSqrt { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_sqrt");
        }

        MirInst::VecAbs { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_abs");
        }

        MirInst::VecFloor { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_floor");
        }

        MirInst::VecCeil { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_ceil");
        }

        MirInst::VecRound { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_round");
        }

        MirInst::VecShuffle { dest, source, indices } => {
            compile_vec_shuffle(ctx, builder, *dest, *source, *indices);
        }

        MirInst::VecBlend {
            dest,
            first,
            second,
            indices,
        } => {
            compile_vec_blend(ctx, builder, *dest, *first, *second, *indices);
        }

        MirInst::VecSelect {
            dest,
            mask,
            if_true,
            if_false,
        } => {
            compile_vec_select(ctx, builder, *dest, *mask, *if_true, *if_false);
        }

        MirInst::GpuAtomic { dest, op, ptr, value } => {
            compile_gpu_atomic(ctx, builder, *dest, *op, *ptr, *value);
        }

        MirInst::GpuAtomicCmpXchg {
            dest,
            ptr,
            expected,
            desired,
        } => {
            compile_gpu_atomic_cmpxchg(ctx, builder, *dest, *ptr, *expected, *desired);
        }

        MirInst::DictLit { dest, keys, values } => {
            compile_dict_lit(ctx, builder, *dest, keys, values);
        }

        MirInst::IndexGet {
            dest,
            collection,
            index,
        } => {
            compile_index_get(ctx, builder, *dest, *collection, *index);
        }

        MirInst::IndexSet {
            collection,
            index,
            value,
        } => {
            compile_index_set(ctx, builder, *collection, *index, *value);
        }

        MirInst::SliceOp {
            dest,
            collection,
            start,
            end,
            step,
        } => {
            compile_slice_op(ctx, builder, *dest, *collection, *start, *end, *step);
        }

        MirInst::Spread { dest, source } => {
            compile_spread(ctx, builder, *dest, *source)?;
        }

        MirInst::ConstString { dest, value } => {
            compile_const_string(ctx, builder, *dest, value)?;
        }

        MirInst::ConstSymbol { dest, value } => {
            compile_const_symbol(ctx, builder, *dest, value)?;
        }

        MirInst::FStringFormat { dest, parts } => {
            compile_fstring_format(ctx, builder, *dest, parts)?;
        }

        MirInst::ClosureCreate {
            dest,
            func_name,
            closure_size,
            capture_offsets,
            capture_types: _,
            captures,
            body_block: _,
            lambda_params: _,
        } => {
            compile_closure_create(
                ctx,
                builder,
                *dest,
                func_name,
                *closure_size as usize,
                capture_offsets,
                captures,
            );
        }

        MirInst::IndirectCall {
            dest,
            callee,
            param_types,
            return_type,
            args,
            effect: _,
        } => {
            compile_indirect_call(ctx, builder, dest, *callee, param_types, *return_type, args);
        }

        MirInst::StructInit {
            dest,
            type_id,
            struct_name,
            struct_size,
            field_offsets,
            field_types,
            field_values,
        } => {
            // Intercept builtin type "constructors" that should be conversion calls
            if *type_id == TypeId::STRING && field_values.len() == 1 {
                // str(x) → rt_to_string(x)
                // Value is already a tagged RuntimeValue (BoxInt inserted by MIR lowering
                // for integer-typed fields, or already tagged from function calls).
                let arg_val = ctx
                    .vreg_values
                    .get(&field_values[0])
                    .copied()
                    .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
                if let Some(&to_str_id) = ctx.runtime_funcs.get("rt_to_string") {
                    let to_str_ref = ctx.module.declare_func_in_func(to_str_id, builder.func);
                    let call = helpers::adapted_call(builder, to_str_ref, &[arg_val]);
                    let result = builder.inst_results(call)[0];
                    ctx.vreg_values.insert(*dest, result);
                } else {
                    ctx.vreg_values.insert(*dest, arg_val);
                }
            } else if *type_id == TypeId::I64 && field_values.len() == 1 {
                // int(x) → rt_string_to_int(x)
                let arg_val = ctx
                    .vreg_values
                    .get(&field_values[0])
                    .copied()
                    .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
                if let Some(&str_to_int_id) = ctx.runtime_funcs.get("rt_string_to_int") {
                    let str_to_int_ref = ctx.module.declare_func_in_func(str_to_int_id, builder.func);
                    let call = helpers::adapted_call(builder, str_to_int_ref, &[arg_val]);
                    let result = builder.inst_results(call)[0];
                    ctx.vreg_values.insert(*dest, result);
                } else {
                    ctx.vreg_values.insert(*dest, arg_val);
                }
            } else {
                // Check if this struct type has a vtable (implements a trait).
                //
                // `type_id` is only unique WITHIN the HIR module that allocated
                // it (per-module `TypeIdAllocator` restarts at 16 for every
                // module) — unrelated structs in different modules routinely
                // land on the same numeric `type_id` (observed: SoftwareBackend,
                // BaremetalBackend, CpuBackend, IntelBackend, ... all landed on
                // TypeId(155) in one native-build). `vtable_type_ids` is a
                // whole-program map, so keying it on the raw `type_id` alone
                // silently aliases unrelated structs' vtables onto each other
                // (whichever struct's impl is emitted last wins the slot).
                // Prefer the collision-free `struct_name` (resolved from the
                // LOCAL per-module type registry at lowering time) via
                // `vtable_data_ids`; fall back to the old `type_id` lookup only
                // when no name is available (e.g. synthetic/test StructInits).
                // See bug
                // simpleos_native_build_field_defaults_and_boxed_trait_dispatch_2026-07-16
                // Symptom B (boxed SoftwareBackend trait dispatch faulted
                // because the RenderBackend vtable it needed had been silently
                // overwritten by an unrelated Engine2DExtended vtable sharing
                // the same colliding `type_id`).
                let vtable_data_id = struct_name
                    .as_deref()
                    .and_then(|name| ctx.vtable_data_ids.get(name))
                    .copied()
                    .or_else(|| ctx.vtable_type_ids.get(type_id).copied());
                // If has_vtable, field offsets from MIR are 0,8,16,... but must be +8 at codegen
                let shifted_offsets: Vec<u32>;
                let effective_offsets = if vtable_data_id.is_some() {
                    shifted_offsets = field_offsets.iter().map(|o| o + 8).collect();
                    shifted_offsets.as_slice()
                } else {
                    field_offsets.as_slice()
                };
                // Adjust struct_size to include vtable ptr slot
                let effective_size = if vtable_data_id.is_some() {
                    *struct_size as usize + 8
                } else {
                    *struct_size as usize
                };
                compile_struct_init(
                    ctx,
                    builder,
                    *dest,
                    effective_size,
                    effective_offsets,
                    field_types,
                    field_values,
                    vtable_data_id,
                );
            }
        }

        MirInst::FieldGet {
            dest,
            object,
            byte_offset,
            field_type,
        } => {
            // MIR lowering emits raw `field_index * 8` offsets that do not account
            // for the 8-byte vtable pointer stored at offset 0 of structs that
            // implement a trait. The StructInit arm shifts those offsets +8 (keyed
            // on `vtable_type_ids`); field access must apply the identical shift or
            // it reads the vtable slot as field 0 (a truncated pointer, not the
            // field). Keyed on the same authoritative set so the two never disagree.
            let off = effective_field_offset(ctx, *object, *byte_offset);
            compile_field_get(ctx, builder, *dest, *object, off as usize, *field_type)?;
        }

        MirInst::FieldSet {
            object,
            byte_offset,
            field_type,
            value,
        } => {
            let off = effective_field_offset(ctx, *object, *byte_offset);
            compile_field_set(ctx, builder, *object, off as usize, *field_type, *value)?;
        }

        MirInst::MethodCallStatic {
            dest,
            receiver,
            func_name,
            args,
        } => {
            compile_method_call_static(ctx, builder, dest, *receiver, func_name, args)?;
        }

        MirInst::MethodCallVirtual {
            dest,
            receiver,
            vtable_slot,
            param_types,
            return_type,
            args,
        } => {
            compile_method_call_virtual(
                ctx,
                builder,
                dest,
                *receiver,
                *vtable_slot as usize,
                param_types,
                *return_type,
                args,
            );
        }

        MirInst::BuiltinMethod {
            dest,
            receiver,
            receiver_type,
            method,
            args,
        } => {
            compile_builtin_method(ctx, builder, dest, *receiver, receiver_type, method, args)?;
        }

        MirInst::ExternMethodCall {
            dest,
            receiver,
            class_name,
            method_name,
            is_static,
            args,
        } => {
            compile_extern_method_call(
                ctx,
                builder,
                dest,
                receiver.as_ref().copied(),
                class_name,
                method_name,
                *is_static,
                args,
            )?;
        }

        MirInst::PatternTest { dest, subject, pattern } => {
            compile_pattern_test(ctx, builder, *dest, *subject, pattern);
        }

        MirInst::PatternBind { dest, subject, binding } => {
            compile_pattern_bind(ctx, builder, *dest, *subject, binding);
        }

        MirInst::EnumDiscriminant { dest, value } => {
            compile_enum_discriminant(ctx, builder, *dest, *value)?;
        }

        MirInst::EnumPayload { dest, value } => {
            compile_enum_payload(ctx, builder, *dest, *value)?;
        }

        MirInst::EnumUnit {
            dest,
            enum_name: _,
            variant_name,
        } => {
            compile_enum_unit(ctx, builder, *dest, variant_name);
        }

        MirInst::EnumWith {
            dest,
            enum_name: _,
            variant_name,
            payload,
        } => {
            compile_enum_with(ctx, builder, *dest, variant_name, *payload);
        }

        // Union type instructions - reuse enum runtime functions with type index
        MirInst::UnionDiscriminant { dest, value } => {
            compile_union_discriminant(ctx, builder, *dest, *value)?;
        }

        MirInst::UnionPayload {
            dest,
            value,
            type_index: _,
        } => {
            compile_union_payload(ctx, builder, *dest, *value)?;
        }

        MirInst::UnionWrap {
            dest,
            value,
            type_index,
        } => {
            compile_union_wrap(ctx, builder, *dest, *value, *type_index as u32)?;
        }

        MirInst::FutureCreate { dest, body_block } => {
            compile_future_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Await { dest, future } => {
            compile_await(ctx, builder, *dest, *future)?;
        }

        MirInst::ActorSpawn { dest, body_block } => {
            compile_actor_spawn(ctx, builder, *dest, *body_block);
        }

        MirInst::ActorSend { actor, message } => {
            compile_actor_send(ctx, builder, *actor, *message)?;
        }

        MirInst::ActorRecv { dest } => {
            compile_actor_recv(ctx, builder, *dest)?;
        }

        MirInst::ActorJoin { dest, actor } => {
            compile_actor_join(ctx, builder, *dest, *actor)?;
        }

        MirInst::ActorReply { message } => {
            compile_actor_reply(ctx, builder, *message)?;
        }

        MirInst::GeneratorCreate { dest, body_block } => {
            compile_generator_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Yield { value } => {
            return compile_yield(ctx, builder, *value);
        }

        MirInst::GeneratorNext { dest, generator } => {
            compile_generator_next(ctx, builder, *dest, *generator)?;
        }

        MirInst::TryUnwrap {
            dest,
            value,
            error_block,
            error_dest,
        } => {
            compile_try_unwrap(ctx, builder, *dest, *value, *error_block, *error_dest);
        }

        MirInst::OptionSome { dest, value } => {
            compile_option_some(ctx, builder, *dest, *value);
        }

        MirInst::OptionNone { dest } => {
            compile_option_none(ctx, builder, *dest);
        }

        MirInst::ResultOk { dest, value } => {
            compile_result_ok(ctx, builder, *dest, *value);
        }

        MirInst::ResultErr { dest, value } => {
            compile_result_err(ctx, builder, *dest, *value);
        }

        MirInst::ContractCheck {
            condition,
            kind,
            func_name,
            message,
        } => {
            compile_contract_check(ctx, builder, *condition, *kind, func_name, message.as_deref())?;
        }

        MirInst::ContractOldCapture { dest, value } => {
            compile_contract_old_capture(ctx, builder, *dest, *value)?;
        }

        // Coverage instrumentation probes
        MirInst::DecisionProbe {
            result,
            decision_id,
            file,
            line,
            column,
        } => {
            compile_decision_probe(ctx, builder, *result, *decision_id, file, *line, *column)?;
        }

        MirInst::ConditionProbe {
            decision_id,
            condition_id,
            result,
            file,
            line,
            column,
        } => {
            compile_condition_probe(ctx, builder, *decision_id, *condition_id, *result, file, *line, *column)?;
        }

        MirInst::PathProbe { path_id, block_id } => {
            compile_path_probe(ctx, builder, *path_id, *block_id)?;
        }

        MirInst::UnitBoundCheck {
            value,
            unit_name,
            min,
            max,
            overflow,
        } => {
            compile_unit_bound_check(ctx, builder, *value, unit_name, *min, *max, *overflow)?;
        }

        MirInst::UnitWiden {
            dest,
            value,
            from_bits,
            to_bits,
            signed,
        } => {
            compile_unit_widen(ctx, builder, *dest, *value, *from_bits, *to_bits, *signed)?;
        }

        MirInst::UnitNarrow {
            dest,
            value,
            from_bits,
            to_bits,
            signed,
            overflow,
        } => {
            compile_unit_narrow(ctx, builder, *dest, *value, *from_bits, *to_bits, *signed, *overflow)?;
        }

        MirInst::UnitSaturate { dest, value, min, max } => {
            compile_unit_saturate(ctx, builder, *dest, *value, *min, *max)?;
        }

        // Pointer instructions
        MirInst::PointerNew { dest, kind, value } => {
            compile_pointer_new(ctx, builder, *dest, *kind, *value)?;
        }

        MirInst::PointerRef { dest, kind, source } => {
            compile_pointer_ref(ctx, builder, *dest, *kind, *source)?;
        }

        MirInst::PointerDeref { dest, pointer, kind } => {
            compile_pointer_deref(ctx, builder, *dest, *pointer, *kind)?;
        }

        // GPU instructions
        MirInst::GpuGlobalId { dest, dim } => {
            super::instr_gpu::compile_gpu_global_id(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuLocalId { dest, dim } => {
            super::instr_gpu::compile_gpu_local_id(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuGroupId { dest, dim } => {
            super::instr_gpu::compile_gpu_group_id(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuGlobalSize { dest, dim } => {
            super::instr_gpu::compile_gpu_global_size(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuLocalSize { dest, dim } => {
            super::instr_gpu::compile_gpu_local_size(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuNumGroups { dest, dim } => {
            super::instr_gpu::compile_gpu_num_groups(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuBarrier => {
            super::instr_gpu::compile_gpu_barrier(ctx, builder)?;
        }

        MirInst::GpuMemFence { scope } => {
            super::instr_gpu::compile_gpu_mem_fence(ctx, builder, *scope)?;
        }

        MirInst::GpuSharedAlloc {
            dest,
            element_type,
            size,
        } => {
            super::instr_gpu::compile_gpu_shared_alloc(ctx, builder, *dest, *element_type, *size)?;
        }

        MirInst::GpuLoadF64 { dest, ptr, index } => {
            super::instr_gpu::compile_gpu_load_f64(ctx, builder, *dest, *ptr, *index)?;
        }

        MirInst::GpuStoreF64 { ptr, index, value } => {
            super::instr_gpu::compile_gpu_store_f64(ctx, builder, *ptr, *index, *value)?;
        }

        MirInst::GpuLoadI64 { dest, ptr, index } => {
            super::instr_gpu::compile_gpu_load_i64(ctx, builder, *dest, *ptr, *index)?;
        }

        MirInst::GpuStoreI64 { ptr, index, value } => {
            super::instr_gpu::compile_gpu_store_i64(ctx, builder, *ptr, *index, *value)?;
        }

        MirInst::NeighborLoad { dest, array, direction } => {
            compile_neighbor_load(ctx, builder, *dest, *array, *direction)?;
        }

        // SIMD load/store operations
        MirInst::VecLoad {
            dest,
            array,
            offset,
            lanes,
        } => {
            compile_vec_load(ctx, builder, *dest, *array, *offset, *lanes)?;
        }

        MirInst::VecStore { source, array, offset } => {
            compile_vec_store(ctx, builder, *source, *array, *offset)?;
        }

        MirInst::VecGather { dest, array, indices } => {
            compile_vec_gather(ctx, builder, *dest, *array, *indices)?;
        }

        MirInst::VecScatter { source, array, indices } => {
            compile_vec_scatter(ctx, builder, *source, *array, *indices)?;
        }

        MirInst::VecFma { dest, a, b, c } => {
            compile_vec_fma(ctx, builder, *dest, *a, *b, *c)?;
        }

        MirInst::VecRecip { dest, source } => {
            compile_vec_recip(ctx, builder, *dest, *source)?;
        }

        MirInst::VecMaskedLoad {
            dest,
            array,
            offset,
            mask,
            default,
        } => {
            compile_vec_masked_load(ctx, builder, *dest, *array, *offset, *mask, *default)?;
        }

        MirInst::VecMaskedStore {
            source,
            array,
            offset,
            mask,
        } => {
            compile_vec_masked_store(ctx, builder, *source, *array, *offset, *mask)?;
        }

        MirInst::VecMinVec { dest, a, b } => {
            compile_vec_min_vec(ctx, builder, *dest, *a, *b)?;
        }

        MirInst::VecMaxVec { dest, a, b } => {
            compile_vec_max_vec(ctx, builder, *dest, *a, *b)?;
        }

        MirInst::VecClamp { dest, source, lo, hi } => {
            compile_vec_clamp(ctx, builder, *dest, *source, *lo, *hi)?;
        }

        // Parallel iterator operations
        MirInst::ParMap {
            dest,
            input,
            closure,
            backend,
        } => {
            compile_par_map(ctx, builder, *dest, *input, *closure, *backend)?;
        }

        MirInst::ParReduce {
            dest,
            input,
            initial,
            closure,
            backend,
        } => {
            compile_par_reduce(ctx, builder, *dest, *input, *initial, *closure, *backend)?;
        }

        MirInst::ParFilter {
            dest,
            input,
            predicate,
            backend,
        } => {
            compile_par_filter(ctx, builder, *dest, *input, *predicate, *backend)?;
        }

        MirInst::ParForEach {
            input,
            closure,
            backend,
        } => {
            compile_par_for_each(ctx, builder, *input, *closure, *backend)?;
        }

        // Memory safety instructions
        MirInst::Drop { value, ty } => {
            // Drop is a no-op for primitive types
            // Primitive types: void, bool, integers (i8-i64, u8-u64), floats (f32, f64), string, nil
            let is_primitive = matches!(
                *ty,
                crate::hir::TypeId::VOID
                    | crate::hir::TypeId::BOOL
                    | crate::hir::TypeId::I8
                    | crate::hir::TypeId::I16
                    | crate::hir::TypeId::I32
                    | crate::hir::TypeId::I64
                    | crate::hir::TypeId::U8
                    | crate::hir::TypeId::U16
                    | crate::hir::TypeId::U32
                    | crate::hir::TypeId::U64
                    | crate::hir::TypeId::F32
                    | crate::hir::TypeId::F64
                    | crate::hir::TypeId::STRING
                    | crate::hir::TypeId::NIL
            );

            if !is_primitive {
                // Non-primitive types may need destructor calls
                // For now, we don't have a Drop trait in Simple, so this is a no-op
                // Future enhancement: look up Drop trait implementation in trait registry
                // and generate: call drop_fn(value)
                //
                // Implementation steps when Drop trait is added:
                // 1. Check if type implements Drop trait via ctx.module.trait_impls
                // 2. If yes, get the drop method function pointer
                // 3. Generate: builder.ins().call(drop_fn, &[value])
                //
                // For reference-counted types (Rc, Arc), the ref-count decrement
                // is handled by MirInst::RcDecrement / MirInst::WeakDecrement
                let _ = value; // Suppress unused warning
            }
        }

        MirInst::EndScope { local_index } => {
            // No-op at runtime - this is just a marker for lifetime analysis
            let _ = local_index; // Suppress unused warnings
        }

        // Value boxing instructions for SFFI boundary
        MirInst::BoxInt { dest, value } => {
            // Box integer as RuntimeValue: (value << 3) | TAG_INT
            // TAG_INT is 0, so this is equivalent to value << 3
            //
            // DEFECT B (symmetric to UnboxInt Task #123): a value that is ALREADY a
            // tagged RuntimeValue heap handle (a user enum/struct/class = TypeId >= 16,
            // or ANY/STRING) must NOT be re-boxed — `handle << 3` shifts its TAG_HEAP
            // bits away and corrupts the pointer, so a later
            // rt_enum_discriminant/rt_enum_payload reads a garbage/nil payload
            // ("field access on nil receiver" in freestanding one-binary builds). Pass
            // it through verbatim; UnboxInt already passes TAG_HEAP through.
            let src_ty = ctx.vreg_types.get(value).copied();
            if matches!(src_ty, Some(t) if t == TypeId::ANY || t.0 >= 16) {
                let handle = ctx
                    .vreg_values
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
                ctx.vreg_values.insert(*dest, handle);
                return Ok(());
            }
            let mut val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                // Missing VReg, use default 0
                builder.ins().iconst(types::I64, 0)
            });
            // Ensure value is i64 - some paths may produce i32 (e.g., SFFI returns).
            // FR-DRIVER-0002b: pick `sextend` for signed VRegs so negative i8/i16/i32
            // values survive the widen. Unsigned and unknown keep the old `uextend`.
            let val_type = builder.func.dfg.value_type(val);
            if val_type == types::I32 || val_type == types::I8 || val_type == types::I16 {
                if vreg_is_signed(ctx, *value) == Some(true) {
                    val = builder.ins().sextend(types::I64, val);
                } else {
                    val = builder.ins().uextend(types::I64, val);
                }
            } else if val_type == types::F64 {
                // Defensive: MIR lowering should have emitted BoxFloat for an f64
                // VReg, but in practice float VRegs (e.g. result of `fmul` from
                // float multiplication) sometimes flow into BoxInt — for example
                // when a float literal is passed to a method whose lowering only
                // inserts BoxInt. Without this branch cranelift emits an
                // `ishl.f64` and the verifier rejects the function (observed in
                // browser_engine `_apply_opacity`). Bitcast preserves the
                // bit-pattern as i64 so the subsequent `ishl … 3` is well-typed
                // and the value round-trips through UnboxFloat-style consumers
                // that re-bitcast i64 → f64.
                val = builder.ins().bitcast(types::I64, MemFlags::new(), val);
            } else if val_type == types::F32 {
                let promoted = builder.ins().fpromote(types::F64, val);
                val = builder.ins().bitcast(types::I64, MemFlags::new(), promoted);
            }
            let three = builder.ins().iconst(types::I64, 3);
            let boxed = builder.ins().ishl(val, three);
            ctx.vreg_values.insert(*dest, boxed);
        }

        MirInst::BoxFloat { dest, value } => {
            // Heap-box for LOSSLESS container floats via rt_value_float(f64),
            // which allocates a HeapFloat storing the full double and returns a
            // tagged heap pointer. The old inline (bits>>3)<<3|TAG_FLOAT zeroed
            // the low 3 mantissa bits, so [0.1][0] != 0.1.
            let mut val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                // Missing VReg, use default 0
                builder.ins().f64const(0.0)
            });
            // f32 VRegs (e.g. struct fields typed f32) flow into BoxFloat too and
            // must be promoted; a raw i64 bit-pattern (defensive) is bitcast back.
            let vt = builder.func.dfg.value_type(val);
            if vt == types::F32 {
                val = builder.ins().fpromote(types::F64, val);
            } else if vt == types::I64 {
                val = builder.ins().bitcast(types::F64, MemFlags::new(), val);
            }
            let boxed = helpers::call_runtime_1(ctx, builder, "rt_value_float", val);
            ctx.vreg_values.insert(*dest, boxed);
        }

        MirInst::UnboxInt { dest, value } => {
            // Unbox RuntimeValue to integer. Task #123: runtime-tag-aware. Only a tagged
            // native scalar (low 3 bits == TAG_INT == 0) is shifted (value >> 3, arithmetic
            // for sign extension); a heap pointer (TAG_HEAP, low bit set), float or special
            // passes through verbatim. This is provably safe: BoxInt always produces
            // low3==0 so tagged scalars still shift, and heap pointers are `ptr | 1` so they
            // never falsely shift. It fixes DEFECT A — `.unwrap()` / dict-get on an
            // Option/enum wrapping a HEAP enum lowers to rt_enum_payload + UnboxInt, and the
            // unconditional >>3 mangled the heap pointer (env `Dict<text,Value>` nested-heap
            // payload nil-ed; enumdict corruption).
            let val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                // Missing VReg, use default 0
                builder.ins().iconst(types::I64, 0)
            });
            let three = builder.ins().iconst(types::I64, 3);
            let seven = builder.ins().iconst(types::I64, 7);
            let tag = builder.ins().band(val, seven);
            let is_int = builder.ins().icmp_imm(IntCC::Equal, tag, 0);
            let shifted = builder.ins().sshr(val, three);
            let is_true = builder.ins().icmp_imm(IntCC::Equal, val, 11);
            let is_false = builder.ins().icmp_imm(IntCC::Equal, val, 19);
            let is_bool = builder.ins().bor(is_true, is_false);
            let zero = builder.ins().iconst(types::I64, 0);
            let one = builder.ins().iconst(types::I64, 1);
            let raw_bool = builder.ins().select(is_true, one, zero);
            let int_or_value = builder.ins().select(is_int, shifted, val);
            let unboxed = builder.ins().select(is_bool, raw_bool, int_or_value);
            ctx.vreg_values.insert(*dest, unboxed);
        }

        MirInst::UnboxFloat { dest, value } => {
            // Unbox RuntimeValue to float via rt_value_as_float(RuntimeValue) ->
            // f64, which reads the heap-boxed float (or a legacy inline
            // TAG_FLOAT) losslessly, mirroring BoxFloat above.
            let val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                // Missing VReg, use default 0
                builder.ins().iconst(types::I64, 0)
            });
            let unboxed = helpers::call_runtime_1(ctx, builder, "rt_value_as_float", val);
            ctx.vreg_values.insert(*dest, unboxed);
        }
    }
    Ok(())
}
