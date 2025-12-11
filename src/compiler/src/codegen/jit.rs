//! JIT (Just-In-Time) compilation module using Cranelift.
//!
//! This module provides JIT compilation for Simple functions, allowing
//! the interpreter to compile hot paths to native code at runtime.

use std::collections::{HashMap, HashSet};

use cranelift_codegen::ir::{
    condcodes::IntCC, types, AbiParam, InstBuilder, MemFlags, Signature, UserFuncName,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use target_lexicon::Triple;
use thiserror::Error;

use crate::hir::{BinOp, TypeId, UnaryOp};
use crate::mir::{
    lower_generator, LocalKind, MirFunction, MirInst, MirLocal, MirModule, Terminator, VReg,
    Visibility,
};

use super::runtime_ffi::RUNTIME_FUNCS;
use super::types_util::{type_id_to_cranelift, type_id_size, type_to_cranelift};

#[derive(Error, Debug)]
pub enum JitError {
    #[error("JIT compilation error: {0}")]
    Compilation(String),

    #[error("Unsupported type: {0:?}")]
    UnsupportedType(TypeId),

    #[error("Unknown function: {0}")]
    UnknownFunction(String),

    #[error("Module error: {0}")]
    ModuleError(String),
}

pub type JitResult<T> = Result<T, JitError>;

/// JIT compiler for Simple functions.
///
/// Compiles MIR functions to native code that can be executed directly.
pub struct JitCompiler {
    module: JITModule,
    ctx: Context,
    func_ids: HashMap<String, cranelift_module::FuncId>,
    /// Map of function names to their native function pointers
    compiled_funcs: HashMap<String, *const u8>,
    /// Runtime function IDs for calling FFI functions
    runtime_funcs: HashMap<&'static str, cranelift_module::FuncId>,
    /// Lazily created no-op body stub used when we don't outline a body_block yet.
    #[allow(dead_code)]
    body_stub: Option<cranelift_module::FuncId>,
}

// Safety: The compiled function pointers are only valid while JitCompiler is alive
// and we don't share them across threads without synchronization.
unsafe impl Send for JitCompiler {}

impl JitCompiler {
    /// Create a new JIT compiler.
    pub fn new() -> JitResult<Self> {
        let mut settings_builder = settings::builder();
        settings_builder.set("opt_level", "speed").unwrap();
        // Enable position-independent code for JIT
        settings_builder.set("is_pic", "true").unwrap();

        let flags = Flags::new(settings_builder);
        let triple = Triple::host();

        let isa = cranelift_codegen::isa::lookup(triple.clone())
            .map_err(|e| JitError::Compilation(e.to_string()))?
            .finish(flags)
            .map_err(|e| JitError::Compilation(e.to_string()))?;

        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let mut module = JITModule::new(builder);
        let ctx = module.make_context();

        // Declare runtime functions
        let runtime_funcs = Self::declare_runtime_functions(&mut module)?;

        Ok(Self {
            module,
            ctx,
            func_ids: HashMap::new(),
            compiled_funcs: HashMap::new(),
            runtime_funcs,
            body_stub: None,
        })
    }

    /// Create or return a no-op body stub (fn() -> void) and return its FuncId.
    #[allow(dead_code)]
    fn ensure_body_stub(&mut self) -> JitResult<cranelift_module::FuncId> {
        if let Some(id) = self.body_stub {
            return Ok(id);
        }

        let call_conv = CallConv::SystemV;
        let sig = Signature::new(call_conv);
        let func_id = self
            .module
            .declare_function("__simple_body_stub", Linkage::Local, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;

        let mut ctx = self.module.make_context();
        ctx.func.signature = Signature::new(call_conv);
        ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        {
            let mut fb_ctx = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
            let block = builder.create_block();
            builder.switch_to_block(block);
            builder.seal_block(block);
            builder.ins().return_(&[]);
            builder.finalize();
        }

        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        self.module.clear_context(&mut ctx);
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::ModuleError(e.to_string()))?;

        self.body_stub = Some(func_id);
        Ok(func_id)
    }

    /// Return a function address for an outlined MIR block. Panics if not declared.
    fn func_block_addr(
        func_ids: &HashMap<String, cranelift_module::FuncId>,
        module: &mut JITModule,
        parent_name: &str,
        block: crate::mir::BlockId,
        builder: &mut FunctionBuilder,
    ) -> cranelift_codegen::ir::Value {
        let name = format!("{}_outlined_{}", parent_name, block.0);
        let func_id = *func_ids
            .get(&name)
            .unwrap_or_else(|| panic!("outlined function {name} not declared"));
        let func_ref = module.declare_func_in_func(func_id, builder.func);
        builder.ins().func_addr(types::I64, func_ref)
    }

    /// Declare external runtime functions for FFI using shared specifications.
    fn declare_runtime_functions(
        module: &mut JITModule,
    ) -> JitResult<HashMap<&'static str, cranelift_module::FuncId>> {
        let mut funcs = HashMap::new();
        let call_conv = CallConv::SystemV;

        for spec in RUNTIME_FUNCS {
            let sig = spec.build_signature(call_conv);
            let id = module
                .declare_function(spec.name, Linkage::Import, &sig)
                .map_err(|e| JitError::ModuleError(e.to_string()))?;
            funcs.insert(spec.name, id);
        }

        Ok(funcs)
    }

    /// Compile a MIR module and return function pointers.
    pub fn compile_module(&mut self, mir: &MirModule) -> JitResult<()> {
        let functions = self.expand_with_outlined(mir);

        // First pass: declare all functions
        for func in &functions {
            let sig = Self::build_signature(func);
            let linkage = if func.is_public() {
                Linkage::Export
            } else {
                Linkage::Local
            };

            let func_id = self
                .module
                .declare_function(&func.name, linkage, &sig)
                .map_err(|e| JitError::ModuleError(e.to_string()))?;

            self.func_ids.insert(func.name.clone(), func_id);
        }

        // Second pass: compile function bodies
        for func in &functions {
            self.compile_function(func)?;
        }

        // Finalize all functions (make them executable)
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::ModuleError(e.to_string()))?;

        // Store function pointers
        for func in &functions {
            if let Some(&func_id) = self.func_ids.get(&func.name) {
                let ptr = self.module.get_finalized_function(func_id);
                self.compiled_funcs.insert(func.name.clone(), ptr);
            }
        }

        Ok(())
    }

    /// Expand MIR with outlined functions for each body_block use.
    fn expand_with_outlined(&self, mir: &MirModule) -> Vec<MirFunction> {
        let mut functions = mir.functions.clone();
        let mut seen = HashSet::new();
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum BodyKind {
            Actor,
            Generator,
            Future,
        }
        for func in &mir.functions {
            let live_ins_map = func.compute_live_ins();
            for block in &func.blocks {
                for inst in &block.instructions {
                    let body_info = match inst {
                        MirInst::ActorSpawn { body_block, .. } => {
                            Some((*body_block, BodyKind::Actor))
                        }
                        MirInst::GeneratorCreate { body_block, .. } => {
                            Some((*body_block, BodyKind::Generator))
                        }
                        MirInst::FutureCreate { body_block, .. } => {
                            Some((*body_block, BodyKind::Future))
                        }
                        _ => None,
                    };
                    if let Some((body_block, kind)) = body_info {
                        let name = format!("{}_outlined_{}", func.name, body_block.0);
                        if seen.contains(&name) {
                            continue;
                        }
                        seen.insert(name.clone());
                        // Outline by cloning the parent function; switch entry to the body_block,
                        // clear outlined metadata, force void return, and append ctx param.
                        let mut outlined = func.clone();
                        outlined.name = name.clone();
                        outlined.visibility = Visibility::Private;
                        outlined.entry_block = body_block;
                        outlined.return_type = match kind {
                            BodyKind::Generator | BodyKind::Future => crate::hir::TypeId::I64,
                            BodyKind::Actor => crate::hir::TypeId::VOID,
                        };
                        outlined.outlined_bodies.clear();
                        outlined.retain_reachable_from(body_block);
                        // Only strip returns for actors (void bodies)
                        if kind == BodyKind::Actor {
                            for b in &mut outlined.blocks {
                                if let Terminator::Return(Some(_)) = b.terminator {
                                    b.terminator = Terminator::Return(None);
                                }
                            }
                        }

                        if kind == BodyKind::Generator {
                            outlined.params.clear();
                            outlined.params.push(MirLocal {
                                name: "generator".to_string(),
                                ty: crate::hir::TypeId::I64,
                                kind: LocalKind::Parameter,
                            });
                        } else {
                            outlined.params.push(MirLocal {
                                name: "ctx".to_string(),
                                ty: crate::hir::TypeId::I64,
                                kind: LocalKind::Parameter,
                            });
                        }
                        let mut live_ins: Vec<_> = live_ins_map
                            .get(&body_block)
                            .cloned()
                            .unwrap_or_default()
                            .into_iter()
                            .collect();
                        live_ins.sort_by_key(|v| v.0);
                        if let Some(orig) = functions.iter_mut().find(|f| f.name == func.name) {
                            orig.outlined_bodies.insert(
                                body_block,
                                crate::mir::OutlinedBody {
                                    name: name.clone(),
                                    live_ins: live_ins.clone(),
                                    frame_slots: None,
                                },
                            );
                        }
                        outlined
                            .outlined_bodies
                            .insert(body_block, crate::mir::OutlinedBody { name: name.clone(), live_ins: live_ins.clone(), frame_slots: None });
                        let outlined = match kind {
                            BodyKind::Generator => {
                                let lowered = lower_generator(&outlined, body_block);
                                let slots = lowered
                                    .states
                                    .iter()
                                    .map(|s| s.live_after_yield.len())
                                    .max()
                                    .unwrap_or(0);
                                if let Some(orig) = functions.iter_mut().find(|f| f.name == func.name)
                                {
                                    if let Some(meta) = orig.outlined_bodies.get_mut(&body_block) {
                                        meta.frame_slots = Some(slots);
                                    }
                                }
                                let mut lowered_func = lowered.rewritten;
                                if let Some(meta) = lowered_func.outlined_bodies.get_mut(&body_block)
                                {
                                    meta.frame_slots = Some(slots);
                                }
                                lowered_func
                            }
                            _ => outlined,
                        };
                        functions.push(outlined);
                    }
                }
            }
        }
        functions
    }

    /// Get the native function pointer for a compiled function.
    ///
    /// # Safety
    /// The caller must ensure the function signature matches the expected type.
    pub fn get_function_ptr(&self, name: &str) -> Option<*const u8> {
        self.compiled_funcs.get(name).copied()
    }

    /// Call a compiled function that takes no arguments and returns i64.
    ///
    /// # Safety
    /// The function must have been compiled with the correct signature.
    pub unsafe fn call_i64_void(&self, name: &str) -> JitResult<i64> {
        let ptr = self
            .get_function_ptr(name)
            .ok_or_else(|| JitError::UnknownFunction(name.to_string()))?;

        let func: fn() -> i64 = std::mem::transmute(ptr);
        Ok(func())
    }

    /// Call a compiled function that takes one i64 argument and returns i64.
    ///
    /// # Safety
    /// The function must have been compiled with the correct signature.
    pub unsafe fn call_i64_i64(&self, name: &str, arg: i64) -> JitResult<i64> {
        let ptr = self
            .get_function_ptr(name)
            .ok_or_else(|| JitError::UnknownFunction(name.to_string()))?;

        let func: fn(i64) -> i64 = std::mem::transmute(ptr);
        Ok(func(arg))
    }

    /// Call a compiled function that takes two i64 arguments and returns i64.
    ///
    /// # Safety
    /// The function must have been compiled with the correct signature.
    pub unsafe fn call_i64_i64_i64(&self, name: &str, arg1: i64, arg2: i64) -> JitResult<i64> {
        let ptr = self
            .get_function_ptr(name)
            .ok_or_else(|| JitError::UnknownFunction(name.to_string()))?;

        let func: fn(i64, i64) -> i64 = std::mem::transmute(ptr);
        Ok(func(arg1, arg2))
    }

    fn build_signature(func: &MirFunction) -> Signature {
        let call_conv = CallConv::SystemV;
        let mut sig = Signature::new(call_conv);

        // Add parameters
        for param in &func.params {
            let ty = type_to_cranelift(param.ty);
            sig.params.push(AbiParam::new(ty));
        }

        // Add return type
        if func.return_type != TypeId::VOID {
            let ret_ty = type_to_cranelift(func.return_type);
            sig.returns.push(AbiParam::new(ret_ty));
        }

        sig
    }

    fn compile_function(&mut self, func: &MirFunction) -> JitResult<()> {
        let func_id = *self
            .func_ids
            .get(&func.name)
            .ok_or_else(|| JitError::UnknownFunction(func.name.clone()))?;

        let sig = Self::build_signature(func);
        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        let mut func_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut func_ctx);

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

        // Initialize parameter variables
        for (i, _param) in func.params.iter().enumerate() {
            let val = builder.block_params(entry_block)[i];
            let var = variables[&i];
            builder.def_var(var, val);
        }

        // If this is an outlined body with captures, load them from ctx (last param).
        if let Some(meta) = func.outlined_bodies.get(&func.entry_block) {
            if !meta.live_ins.is_empty() {
                let ctx_param = if func.generator_states.is_some() {
                    let gen_param = builder.block_params(entry_block)[0];
                    let get_ctx_id = self.runtime_funcs["rt_generator_get_ctx"];
                    let get_ctx_ref =
                        self.module.declare_func_in_func(get_ctx_id, builder.func);
                    let call = builder.ins().call(get_ctx_ref, &[gen_param]);
                    builder.inst_results(call)[0]
                } else {
                    builder.block_params(entry_block)[func.params.len().saturating_sub(1)]
                };
                let get_id = self.runtime_funcs["rt_array_get"];
                let get_ref = self.module.declare_func_in_func(get_id, builder.func);
                for (idx, reg) in meta.live_ins.iter().enumerate() {
                    let idx_val = builder.ins().iconst(types::I64, idx as i64);
                    let call = builder.ins().call(get_ref, &[ctx_param, idx_val]);
                    let val = builder.inst_results(call)[0];
                    vreg_values.insert(*reg, val);
                }
            }
        }

        let generator_states = func.generator_states.clone();
        let generator_state_len = generator_states.as_ref().map(|s| s.len()).unwrap_or(0);
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
        let mut skip_entry_terminator = false;
        if let Some(states) = &generator_states {
            let generator_param = builder.block_params(entry_block)[0];
            let get_state_id = self.runtime_funcs["rt_generator_get_state"];
            let get_state_ref = self.module.declare_func_in_func(get_state_id, builder.func);
            let call = builder.ins().call(get_state_ref, &[generator_param]);
            let state_val = builder.inst_results(call)[0];

            if let Some(entry_target) = func
                .block(func.entry_block)
                .and_then(|b| match b.terminator {
                    Terminator::Jump(t) => Some(t),
                    _ => None,
                })
            {
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
                        builder.create_block()
                    };
                    let cmp =
                        builder
                            .ins()
                            .icmp_imm(IntCC::Equal, state_val, idx as i64);
                    builder
                        .ins()
                        .brif(cmp, *tgt, &[], next_block, &[]);
                    builder.seal_block(current_block);
                    if !is_last {
                        current_block = next_block;
                    }
                }
                builder.switch_to_block(default_block);
                skip_entry_terminator = true;
            }
        }

        // Compile each block
        let mut local_addr_map: HashMap<VReg, usize> = HashMap::new();

        for mir_block in &func.blocks {
            if generator_states.is_some() && mir_block.id == func.entry_block {
                continue;
            }
            let cl_block = *blocks.get(&mir_block.id).unwrap();

            if mir_block.id != func.entry_block {
                builder.switch_to_block(cl_block);
            }

            if let Some(resume_map) = generator_resume_map.as_ref() {
                if let Some(state) = resume_map.get(&mir_block.id) {
                    let gen_param = builder.block_params(entry_block)[0];
                    let load_id = self.runtime_funcs["rt_generator_load_slot"];
                    let load_ref = self.module.declare_func_in_func(load_id, builder.func);
                    for (idx, reg) in state.live_after_yield.iter().enumerate() {
                        let idx_val = builder.ins().iconst(types::I64, idx as i64);
                        let call = builder.ins().call(load_ref, &[gen_param, idx_val]);
                        let val = builder.inst_results(call)[0];
                        vreg_values.insert(*reg, val);
                    }
                }
            }

            // Compile instructions
            for inst in &mir_block.instructions {
                match inst {
                    MirInst::ConstInt { dest, value } => {
                        let val = builder.ins().iconst(types::I64, *value);
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::ConstFloat { dest, value } => {
                        let val = builder.ins().f64const(*value);
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::ConstBool { dest, value } => {
                        let val = builder.ins().iconst(types::I8, if *value { 1 } else { 0 });
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::Copy { dest, src } => {
                        let val = vreg_values[src];
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::BinOp {
                        dest,
                        op,
                        left,
                        right,
                    } => {
                        let lhs = vreg_values[left];
                        let rhs = vreg_values[right];

                        let val = match op {
                            BinOp::Add => builder.ins().iadd(lhs, rhs),
                            BinOp::Sub => builder.ins().isub(lhs, rhs),
                            BinOp::Mul => builder.ins().imul(lhs, rhs),
                            BinOp::Div => builder.ins().sdiv(lhs, rhs),
                            BinOp::Mod => builder.ins().srem(lhs, rhs),
                            BinOp::BitAnd => builder.ins().band(lhs, rhs),
                            BinOp::BitOr => builder.ins().bor(lhs, rhs),
                            BinOp::BitXor => builder.ins().bxor(lhs, rhs),
                            BinOp::ShiftLeft => builder.ins().ishl(lhs, rhs),
                            BinOp::ShiftRight => builder.ins().sshr(lhs, rhs),
                            BinOp::Lt => builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::SignedLessThan,
                                lhs,
                                rhs,
                            ),
                            BinOp::Gt => builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan,
                                lhs,
                                rhs,
                            ),
                            BinOp::LtEq => builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::SignedLessThanOrEqual,
                                lhs,
                                rhs,
                            ),
                            BinOp::GtEq => builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThanOrEqual,
                                lhs,
                                rhs,
                            ),
                            BinOp::Eq => builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::Equal,
                                lhs,
                                rhs,
                            ),
                            BinOp::NotEq => builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                                lhs,
                                rhs,
                            ),
                            BinOp::Is => builder.ins().icmp(
                                cranelift_codegen::ir::condcodes::IntCC::Equal,
                                lhs,
                                rhs,
                            ),
                            BinOp::In => {
                                // The 'in' operator checks if lhs is in rhs collection
                                // Call rt_contains(collection, value) -> bool
                                let contains_id = self.runtime_funcs["rt_contains"];
                                let contains_ref =
                                    self.module.declare_func_in_func(contains_id, builder.func);
                                // rhs is the collection, lhs is the value to find
                                let call = builder.ins().call(contains_ref, &[rhs, lhs]);
                                builder.inst_results(call)[0]
                            }
                            BinOp::And => {
                                let lhs_bool = builder.ins().icmp_imm(
                                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                                    lhs,
                                    0,
                                );
                                let rhs_bool = builder.ins().icmp_imm(
                                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                                    rhs,
                                    0,
                                );
                                builder.ins().band(lhs_bool, rhs_bool)
                            }
                            BinOp::Or => {
                                let lhs_bool = builder.ins().icmp_imm(
                                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                                    lhs,
                                    0,
                                );
                                let rhs_bool = builder.ins().icmp_imm(
                                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                                    rhs,
                                    0,
                                );
                                builder.ins().bor(lhs_bool, rhs_bool)
                            }
                            BinOp::Pow => {
                                // Integer power using loop
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
                                let cond = builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan,
                                    exp_param,
                                    zero,
                                );
                                builder.ins().brif(
                                    cond,
                                    loop_body,
                                    &[],
                                    loop_exit,
                                    &[result_param],
                                );

                                builder.switch_to_block(loop_body);
                                let new_result = builder.ins().imul(result_param, lhs);
                                let new_exp = builder.ins().isub(exp_param, one);
                                builder.ins().jump(loop_header, &[new_result, new_exp]);

                                builder.switch_to_block(loop_exit);
                                builder.block_params(loop_exit)[0]
                            }
                            BinOp::FloorDiv => builder.ins().sdiv(lhs, rhs),
                        };
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::LocalAddr { dest, local_index } => {
                        let addr_val = builder.ins().iconst(types::I64, *local_index as i64);
                        vreg_values.insert(*dest, addr_val);
                        local_addr_map.insert(*dest, *local_index);
                    }

                    MirInst::Load { dest, addr, .. } => {
                        if let Some(&local_index) = local_addr_map.get(addr) {
                            if let Some(&var) = variables.get(&local_index) {
                                let val = builder.use_var(var);
                                vreg_values.insert(*dest, val);
                            }
                        } else {
                            let val = vreg_values[addr];
                            vreg_values.insert(*dest, val);
                        }
                    }

                    MirInst::Store { addr, value, .. } => {
                        if let Some(&local_index) = local_addr_map.get(addr) {
                            if let Some(&var) = variables.get(&local_index) {
                                let val = vreg_values[value];
                                builder.def_var(var, val);
                            }
                        }
                    }

                    MirInst::UnaryOp { dest, op, operand } => {
                        let val = vreg_values[operand];
                        let result = match op {
                            UnaryOp::Neg => builder.ins().ineg(val),
                            UnaryOp::Not => builder.ins().icmp_imm(
                                cranelift_codegen::ir::condcodes::IntCC::Equal,
                                val,
                                0,
                            ),
                            UnaryOp::BitNot => builder.ins().bnot(val),
                        };
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::Call { dest, target, args } => {
                        let func_name = target.name();
                        if let Some(&callee_id) = self.func_ids.get(func_name) {
                            let callee_ref =
                                self.module.declare_func_in_func(callee_id, builder.func);

                            let arg_vals: Vec<_> = args.iter().map(|a| vreg_values[a]).collect();

                            let call = builder.ins().call(callee_ref, &arg_vals);
                            if let Some(d) = dest {
                                let results = builder.inst_results(call);
                                if !results.is_empty() {
                                    vreg_values.insert(*d, results[0]);
                                }
                            }
                        }
                    }

                    MirInst::GetElementPtr { dest, base, index } => {
                        let base_val = vreg_values[base];
                        let index_val = vreg_values[index];
                        let element_size = builder.ins().iconst(types::I64, 8);
                        let offset = builder.ins().imul(index_val, element_size);
                        let addr = builder.ins().iadd(base_val, offset);
                        vreg_values.insert(*dest, addr);
                    }

                    MirInst::GcAlloc { dest, ty } => {
                        // GC allocation: allocate memory for the given type
                        // Use rt_alloc with size based on type
                        let alloc_id = self.runtime_funcs["rt_alloc"];
                        let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);

                        // Calculate size based on type (default to 8 bytes for pointer-sized values)
                        let size = type_id_size(*ty) as i64;
                        let size_val = builder.ins().iconst(types::I64, size.max(8));
                        let call = builder.ins().call(alloc_ref, &[size_val]);
                        let ptr = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, ptr);
                    }

                    MirInst::Wait { dest, target } => {
                        // Blocking wait: call rt_wait to wait on target value
                        let wait_id = self.runtime_funcs["rt_wait"];
                        let wait_ref = self.module.declare_func_in_func(wait_id, builder.func);

                        let target_val = vreg_values[target];
                        let call = builder.ins().call(wait_ref, &[target_val]);
                        let result = builder.inst_results(call)[0];

                        if let Some(d) = dest {
                            vreg_values.insert(*d, result);
                        }
                    }

                    MirInst::InterpCall {
                        dest,
                        func_name,
                        args,
                    } => {
                        // Create an array to hold the arguments
                        let array_new_id = self.runtime_funcs["rt_array_new"];
                        let array_new_ref =
                            self.module.declare_func_in_func(array_new_id, builder.func);
                        let capacity = builder.ins().iconst(types::I64, args.len() as i64);
                        let call = builder.ins().call(array_new_ref, &[capacity]);
                        let args_array = builder.inst_results(call)[0];

                        // Push each argument to the array
                        let array_push_id = self.runtime_funcs["rt_array_push"];
                        let array_push_ref = self
                            .module
                            .declare_func_in_func(array_push_id, builder.func);

                        for arg in args {
                            let arg_val = vreg_values[arg];
                            builder.ins().call(array_push_ref, &[args_array, arg_val]);
                        }

                        // For JIT, create a string RuntimeValue for the function name
                        // and use rt_string_new to allocate it
                        let func_name_bytes = func_name.as_bytes();
                        let string_new_id = self.runtime_funcs["rt_string_new"];
                        let _string_new_ref = self
                            .module
                            .declare_func_in_func(string_new_id, builder.func);

                        // Store the function name in a global data section
                        let data_id = self
                            .module
                            .declare_anonymous_data(true, false)
                            .map_err(|e| JitError::ModuleError(e.to_string()))?;
                        let mut data_desc = cranelift_module::DataDescription::new();
                        data_desc.define(func_name_bytes.to_vec().into_boxed_slice());
                        self.module
                            .define_data(data_id, &data_desc)
                            .map_err(|e| JitError::ModuleError(e.to_string()))?;

                        let global_val = self.module.declare_data_in_func(data_id, builder.func);
                        let name_ptr = builder.ins().global_value(types::I64, global_val);
                        let name_len = builder
                            .ins()
                            .iconst(types::I64, func_name_bytes.len() as i64);

                        // Call rt_interp_call(name_ptr, name_len, args_array)
                        let interp_call_id = self.runtime_funcs["rt_interp_call"];
                        let interp_call_ref = self
                            .module
                            .declare_func_in_func(interp_call_id, builder.func);
                        let call = builder
                            .ins()
                            .call(interp_call_ref, &[name_ptr, name_len, args_array]);
                        let result = builder.inst_results(call)[0];

                        if let Some(d) = dest {
                            vreg_values.insert(*d, result);
                        }
                    }

                    MirInst::InterpEval { dest, expr_index } => {
                        // Call rt_interp_eval(expr_index)
                        let interp_eval_id = self.runtime_funcs["rt_interp_eval"];
                        let interp_eval_ref = self
                            .module
                            .declare_func_in_func(interp_eval_id, builder.func);
                        let idx = builder.ins().iconst(types::I64, *expr_index as i64);
                        let call = builder.ins().call(interp_eval_ref, &[idx]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    // Collection instructions - implemented with runtime FFI
                    MirInst::ArrayLit { dest, elements } => {
                        // Call rt_array_new(capacity)
                        let array_new_id = self.runtime_funcs["rt_array_new"];
                        let array_new_ref =
                            self.module.declare_func_in_func(array_new_id, builder.func);
                        let capacity = builder.ins().iconst(types::I64, elements.len() as i64);
                        let call = builder.ins().call(array_new_ref, &[capacity]);
                        let array = builder.inst_results(call)[0];

                        // Push each element: rt_array_push(array, element)
                        let array_push_id = self.runtime_funcs["rt_array_push"];
                        let array_push_ref = self
                            .module
                            .declare_func_in_func(array_push_id, builder.func);

                        // Convert raw values to RuntimeValue using rt_value_int
                        let value_int_id = self.runtime_funcs["rt_value_int"];
                        let value_int_ref =
                            self.module.declare_func_in_func(value_int_id, builder.func);

                        for elem in elements {
                            let elem_val = vreg_values[elem];
                            // Wrap the value as RuntimeValue
                            let wrap_call = builder.ins().call(value_int_ref, &[elem_val]);
                            let wrapped = builder.inst_results(wrap_call)[0];
                            builder.ins().call(array_push_ref, &[array, wrapped]);
                        }
                        vreg_values.insert(*dest, array);
                    }

                    MirInst::TupleLit { dest, elements } => {
                        // Call rt_tuple_new(len)
                        let tuple_new_id = self.runtime_funcs["rt_tuple_new"];
                        let tuple_new_ref =
                            self.module.declare_func_in_func(tuple_new_id, builder.func);
                        let len = builder.ins().iconst(types::I64, elements.len() as i64);
                        let call = builder.ins().call(tuple_new_ref, &[len]);
                        let tuple = builder.inst_results(call)[0];

                        // Set each element: rt_tuple_set(tuple, index, value)
                        let tuple_set_id = self.runtime_funcs["rt_tuple_set"];
                        let tuple_set_ref =
                            self.module.declare_func_in_func(tuple_set_id, builder.func);

                        // Convert raw values to RuntimeValue
                        let value_int_id = self.runtime_funcs["rt_value_int"];
                        let value_int_ref =
                            self.module.declare_func_in_func(value_int_id, builder.func);

                        for (i, elem) in elements.iter().enumerate() {
                            let idx = builder.ins().iconst(types::I64, i as i64);
                            let elem_val = vreg_values[elem];
                            let wrap_call = builder.ins().call(value_int_ref, &[elem_val]);
                            let wrapped = builder.inst_results(wrap_call)[0];
                            builder.ins().call(tuple_set_ref, &[tuple, idx, wrapped]);
                        }
                        vreg_values.insert(*dest, tuple);
                    }

                    MirInst::DictLit { dest, keys, values } => {
                        // Call rt_dict_new(capacity)
                        let dict_new_id = self.runtime_funcs["rt_dict_new"];
                        let dict_new_ref =
                            self.module.declare_func_in_func(dict_new_id, builder.func);
                        let capacity = builder.ins().iconst(types::I64, (keys.len() * 2) as i64);
                        let call = builder.ins().call(dict_new_ref, &[capacity]);
                        let dict = builder.inst_results(call)[0];

                        // Set each key-value pair: rt_dict_set(dict, key, value)
                        let dict_set_id = self.runtime_funcs["rt_dict_set"];
                        let dict_set_ref =
                            self.module.declare_func_in_func(dict_set_id, builder.func);

                        // Convert raw values to RuntimeValue
                        let value_int_id = self.runtime_funcs["rt_value_int"];
                        let value_int_ref =
                            self.module.declare_func_in_func(value_int_id, builder.func);

                        for (key, val) in keys.iter().zip(values.iter()) {
                            let key_val = vreg_values[key];
                            let val_val = vreg_values[val];
                            let wrap_key = builder.ins().call(value_int_ref, &[key_val]);
                            let wrapped_key = builder.inst_results(wrap_key)[0];
                            let wrap_val = builder.ins().call(value_int_ref, &[val_val]);
                            let wrapped_val = builder.inst_results(wrap_val)[0];
                            builder
                                .ins()
                                .call(dict_set_ref, &[dict, wrapped_key, wrapped_val]);
                        }
                        vreg_values.insert(*dest, dict);
                    }

                    MirInst::IndexGet {
                        dest,
                        collection,
                        index,
                    } => {
                        // Call rt_index_get(collection, index)
                        let index_get_id = self.runtime_funcs["rt_index_get"];
                        let index_get_ref =
                            self.module.declare_func_in_func(index_get_id, builder.func);
                        let coll_val = vreg_values[collection];
                        let idx_val = vreg_values[index];

                        // Wrap index as RuntimeValue
                        let value_int_id = self.runtime_funcs["rt_value_int"];
                        let value_int_ref =
                            self.module.declare_func_in_func(value_int_id, builder.func);
                        let wrap_call = builder.ins().call(value_int_ref, &[idx_val]);
                        let wrapped_idx = builder.inst_results(wrap_call)[0];

                        let call = builder.ins().call(index_get_ref, &[coll_val, wrapped_idx]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::IndexSet {
                        collection,
                        index,
                        value,
                    } => {
                        // Call rt_index_set(collection, index, value)
                        let index_set_id = self.runtime_funcs["rt_index_set"];
                        let index_set_ref =
                            self.module.declare_func_in_func(index_set_id, builder.func);
                        let coll_val = vreg_values[collection];
                        let idx_val = vreg_values[index];
                        let val = vreg_values[value];

                        // Wrap index and value as RuntimeValue
                        let value_int_id = self.runtime_funcs["rt_value_int"];
                        let value_int_ref =
                            self.module.declare_func_in_func(value_int_id, builder.func);
                        let wrap_idx = builder.ins().call(value_int_ref, &[idx_val]);
                        let wrapped_idx = builder.inst_results(wrap_idx)[0];
                        let wrap_val = builder.ins().call(value_int_ref, &[val]);
                        let wrapped_val = builder.inst_results(wrap_val)[0];

                        builder
                            .ins()
                            .call(index_set_ref, &[coll_val, wrapped_idx, wrapped_val]);
                    }

                    MirInst::SliceOp {
                        dest,
                        collection,
                        start,
                        end,
                        step,
                    } => {
                        // Call rt_slice(collection, start, end, step)
                        let slice_id = self.runtime_funcs["rt_slice"];
                        let slice_ref = self.module.declare_func_in_func(slice_id, builder.func);
                        let coll_val = vreg_values[collection];

                        // Get start, end, step values (or defaults)
                        let start_val = start
                            .map(|s| vreg_values[&s])
                            .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
                        let end_val = end
                            .map(|e| vreg_values[&e])
                            .unwrap_or_else(|| builder.ins().iconst(types::I64, i64::MAX));
                        let step_val = step
                            .map(|s| vreg_values[&s])
                            .unwrap_or_else(|| builder.ins().iconst(types::I64, 1));

                        let call = builder
                            .ins()
                            .call(slice_ref, &[coll_val, start_val, end_val, step_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::Spread { dest, source } => {
                        // Spread operator: unpacks/spreads a collection
                        // For now, just copy the collection reference (shallow spread)
                        let source_val = vreg_values[source];
                        vreg_values.insert(*dest, source_val);
                    }

                    MirInst::ConstString { dest, value } => {
                        // Create string using rt_string_new
                        let string_new_id = self.runtime_funcs["rt_string_new"];
                        let string_new_ref = self
                            .module
                            .declare_func_in_func(string_new_id, builder.func);

                        if value.is_empty() {
                            // Empty string
                            let null_ptr = builder.ins().iconst(types::I64, 0);
                            let zero_len = builder.ins().iconst(types::I64, 0);
                            let call = builder.ins().call(string_new_ref, &[null_ptr, zero_len]);
                            let result = builder.inst_results(call)[0];
                            vreg_values.insert(*dest, result);
                        } else {
                            // For non-empty strings, create a stack slot and copy bytes
                            let bytes = value.as_bytes();
                            let len = bytes.len();

                            // Create a stack slot for the string data
                            let slot = builder.create_sized_stack_slot(
                                cranelift_codegen::ir::StackSlotData::new(
                                    cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                                    len as u32,
                                    0,
                                ),
                            );

                            // Store each byte
                            for (i, &byte) in bytes.iter().enumerate() {
                                let byte_val = builder.ins().iconst(types::I8, byte as i64);
                                builder.ins().stack_store(byte_val, slot, i as i32);
                            }

                            // Get pointer to stack slot
                            let ptr = builder.ins().stack_addr(types::I64, slot, 0);
                            let len_val = builder.ins().iconst(types::I64, len as i64);

                            let call = builder.ins().call(string_new_ref, &[ptr, len_val]);
                            let result = builder.inst_results(call)[0];
                            vreg_values.insert(*dest, result);
                        }
                    }

                    MirInst::ConstSymbol { dest, value } => {
                        // Symbols are represented as hashed integer values
                        // Use a simple hash: sum of (byte * 31^position)
                        let hash = value.bytes().enumerate().fold(0i64, |acc, (i, b)| {
                            acc.wrapping_add((b as i64).wrapping_mul(31i64.wrapping_pow(i as u32)))
                        });
                        // Tag the hash with a symbol marker (high bit set)
                        let symbol_val = builder.ins().iconst(types::I64, hash | (1i64 << 62));
                        vreg_values.insert(*dest, symbol_val);
                    }

                    MirInst::FStringFormat { dest, parts } => {
                        // F-string formatting by concatenating parts
                        let string_new_id = self.runtime_funcs["rt_string_new"];
                        let string_new_ref = self
                            .module
                            .declare_func_in_func(string_new_id, builder.func);
                        let string_concat_id = self.runtime_funcs["rt_string_concat"];
                        let string_concat_ref = self
                            .module
                            .declare_func_in_func(string_concat_id, builder.func);

                        // Start with empty string
                        let null_ptr = builder.ins().iconst(types::I64, 0);
                        let zero_len = builder.ins().iconst(types::I64, 0);
                        let empty_call = builder.ins().call(string_new_ref, &[null_ptr, zero_len]);
                        let mut result = builder.inst_results(empty_call)[0];

                        for part in parts {
                            let part_str = match part {
                                crate::mir::FStringPart::Literal(s) => {
                                    if s.is_empty() {
                                        continue;
                                    }
                                    let bytes = s.as_bytes();
                                    let len = bytes.len();

                                    let slot = builder.create_sized_stack_slot(
                                        cranelift_codegen::ir::StackSlotData::new(
                                            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
                                            len as u32,
                                            0,
                                        ),
                                    );

                                    for (i, &byte) in bytes.iter().enumerate() {
                                        let byte_val = builder.ins().iconst(types::I8, byte as i64);
                                        builder.ins().stack_store(byte_val, slot, i as i32);
                                    }

                                    let ptr = builder.ins().stack_addr(types::I64, slot, 0);
                                    let len_val = builder.ins().iconst(types::I64, len as i64);
                                    let call = builder.ins().call(string_new_ref, &[ptr, len_val]);
                                    builder.inst_results(call)[0]
                                }
                                crate::mir::FStringPart::Expr(vreg) => {
                                    // Expression value - assumes it's already a string
                                    vreg_values[vreg]
                                }
                            };

                            // Concatenate with result
                            let concat_call =
                                builder.ins().call(string_concat_ref, &[result, part_str]);
                            result = builder.inst_results(concat_call)[0];
                        }

                        vreg_values.insert(*dest, result);
                    }

                    // Phase 3: Closure instructions (zero-cost)
                    MirInst::ClosureCreate {
                        dest,
                        func_name,
                        closure_size,
                        capture_offsets,
                        capture_types: _,
                        captures,
                    } => {
                        // Zero-cost closure creation:
                        // 1. Allocate memory for closure struct: { fn_ptr, captures... }
                        // 2. Store function pointer at offset 0
                        // 3. Store each capture at its byte offset

                        let alloc_id = self.runtime_funcs["rt_alloc"];
                        let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);

                        let size_val = builder.ins().iconst(types::I64, *closure_size as i64);
                        let call = builder.ins().call(alloc_ref, &[size_val]);
                        let closure_ptr = builder.inst_results(call)[0];

                        // Store function pointer at offset 0
                        if let Some(&func_id) = self.func_ids.get(func_name) {
                            let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                            let fn_addr = builder.ins().func_addr(types::I64, func_ref);
                            builder
                                .ins()
                                .store(MemFlags::new(), fn_addr, closure_ptr, 0);
                        } else {
                            // Store null if function not found
                            let null = builder.ins().iconst(types::I64, 0);
                            builder.ins().store(MemFlags::new(), null, closure_ptr, 0);
                        }

                        // Store each capture at its byte offset
                        for (i, offset) in capture_offsets.iter().enumerate() {
                            let cap_val = vreg_values[&captures[i]];
                            builder.ins().store(
                                MemFlags::new(),
                                cap_val,
                                closure_ptr,
                                *offset as i32,
                            );
                        }

                        vreg_values.insert(*dest, closure_ptr);
                    }

                    MirInst::IndirectCall {
                        dest,
                        callee,
                        param_types,
                        return_type,
                        args,
                        effect: _,
                    } => {
                        // Zero-cost indirect call:
                        // 1. Load function pointer from closure (offset 0)
                        // 2. Build signature from param_types/return_type
                        // 3. Call indirect

                        let closure_ptr = vreg_values[callee];

                        // Load function pointer from closure
                        let fn_ptr =
                            builder
                                .ins()
                                .load(types::I64, MemFlags::new(), closure_ptr, 0);

                        // Build call signature
                        let call_conv = CallConv::SystemV;
                        let mut sig = Signature::new(call_conv);

                        // First param is the closure itself (for capture access)
                        sig.params.push(AbiParam::new(types::I64));

                        for param_ty in param_types {
                            sig.params
                                .push(AbiParam::new(type_id_to_cranelift(*param_ty)));
                        }
                        if *return_type != TypeId::VOID {
                            sig.returns
                                .push(AbiParam::new(type_id_to_cranelift(*return_type)));
                        }

                        let sig_ref = builder.import_signature(sig);

                        // Build argument list: closure + args
                        let mut call_args = vec![closure_ptr];
                        for arg in args {
                            call_args.push(vreg_values[arg]);
                        }

                        // Indirect call
                        let call = builder.ins().call_indirect(sig_ref, fn_ptr, &call_args);

                        if let Some(d) = dest {
                            let results = builder.inst_results(call);
                            if !results.is_empty() {
                                vreg_values.insert(*d, results[0]);
                            } else {
                                let null = builder.ins().iconst(types::I64, 0);
                                vreg_values.insert(*d, null);
                            }
                        }
                    }

                    // Phase 4: Object/Method instructions (zero-cost)
                    MirInst::StructInit {
                        dest,
                        type_id: _,
                        struct_size,
                        field_offsets,
                        field_types,
                        field_values,
                    } => {
                        // Zero-cost struct allocation:
                        // 1. Allocate memory: rt_alloc(struct_size)
                        // 2. Store each field at its byte offset

                        let alloc_id = self.runtime_funcs["rt_alloc"];
                        let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);

                        let size_val = builder.ins().iconst(types::I64, *struct_size as i64);
                        let call = builder.ins().call(alloc_ref, &[size_val]);
                        let ptr = builder.inst_results(call)[0];

                        // Store each field at its computed byte offset
                        for (i, (offset, field_type)) in
                            field_offsets.iter().zip(field_types.iter()).enumerate()
                        {
                            let field_val = vreg_values[&field_values[i]];
                            let cranelift_ty = type_id_to_cranelift(*field_type);

                            // Direct store at offset (zero-cost pointer arithmetic)
                            builder
                                .ins()
                                .store(MemFlags::new(), field_val, ptr, *offset as i32);

                            // Suppress unused variable warning
                            let _ = cranelift_ty;
                        }

                        vreg_values.insert(*dest, ptr);
                    }

                    MirInst::FieldGet {
                        dest,
                        object,
                        byte_offset,
                        field_type,
                    } => {
                        // Zero-cost field access: pointer arithmetic + load
                        let obj_ptr = vreg_values[object];
                        let cranelift_ty = type_id_to_cranelift(*field_type);

                        // Direct load at offset (single instruction)
                        let val = builder.ins().load(
                            cranelift_ty,
                            MemFlags::new(),
                            obj_ptr,
                            *byte_offset as i32,
                        );
                        vreg_values.insert(*dest, val);
                    }

                    MirInst::FieldSet {
                        object,
                        byte_offset,
                        field_type: _,
                        value,
                    } => {
                        // Zero-cost field set: pointer arithmetic + store
                        let obj_ptr = vreg_values[object];
                        let val = vreg_values[value];

                        // Direct store at offset (single instruction)
                        builder
                            .ins()
                            .store(MemFlags::new(), val, obj_ptr, *byte_offset as i32);
                    }

                    MirInst::MethodCallStatic {
                        dest,
                        receiver,
                        func_name,
                        args,
                    } => {
                        // Zero-cost static method call: direct function call
                        // Method is just a function where receiver is the first argument

                        if let Some(&func_id) = self.func_ids.get(func_name) {
                            let func_ref = self.module.declare_func_in_func(func_id, builder.func);

                            // Build argument list: receiver + args
                            let mut call_args = vec![vreg_values[receiver]];
                            for arg in args {
                                call_args.push(vreg_values[arg]);
                            }

                            let call = builder.ins().call(func_ref, &call_args);

                            if let Some(d) = dest {
                                let results = builder.inst_results(call);
                                if !results.is_empty() {
                                    vreg_values.insert(*d, results[0]);
                                } else {
                                    let null = builder.ins().iconst(types::I64, 0);
                                    vreg_values.insert(*d, null);
                                }
                            }
                        } else {
                            // Function not found - call rt_function_not_found with function name
                            let func_name_bytes = func_name.as_bytes();
                            let data_id = self
                                .module
                                .declare_anonymous_data(true, false)
                                .map_err(|e| JitError::ModuleError(e.to_string()))?;
                            let mut data_desc = cranelift_module::DataDescription::new();
                            data_desc.define(func_name_bytes.to_vec().into_boxed_slice());
                            self.module
                                .define_data(data_id, &data_desc)
                                .map_err(|e| JitError::ModuleError(e.to_string()))?;

                            let global_val =
                                self.module.declare_data_in_func(data_id, builder.func);
                            let name_ptr = builder.ins().global_value(types::I64, global_val);
                            let name_len = builder
                                .ins()
                                .iconst(types::I64, func_name_bytes.len() as i64);

                            let not_found_id = self.runtime_funcs["rt_function_not_found"];
                            let not_found_ref =
                                self.module.declare_func_in_func(not_found_id, builder.func);
                            let call = builder.ins().call(not_found_ref, &[name_ptr, name_len]);

                            if let Some(d) = dest {
                                let result = builder.inst_results(call)[0];
                                vreg_values.insert(*d, result);
                            }
                        }
                    }

                    MirInst::MethodCallVirtual {
                        dest,
                        receiver,
                        vtable_slot,
                        param_types,
                        return_type,
                        args,
                    } => {
                        // Vtable-based virtual dispatch (only for dyn types)
                        // 1. Load vtable pointer from receiver (at offset 0)
                        // 2. Load method pointer from vtable at slot offset
                        // 3. Indirect call through method pointer

                        let recv_ptr = vreg_values[receiver];

                        // Load vtable pointer (first 8 bytes of object)
                        let vtable_ptr =
                            builder.ins().load(types::I64, MemFlags::new(), recv_ptr, 0);

                        // Load method pointer from vtable (slot * 8)
                        let slot_offset = (*vtable_slot as i32) * 8;
                        let method_ptr = builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            vtable_ptr,
                            slot_offset,
                        );

                        // Build indirect call signature
                        let call_conv = CallConv::SystemV;
                        let mut sig = Signature::new(call_conv);
                        sig.params.push(AbiParam::new(types::I64)); // receiver
                        for param_ty in param_types {
                            sig.params
                                .push(AbiParam::new(type_id_to_cranelift(*param_ty)));
                        }
                        if *return_type != TypeId::VOID {
                            sig.returns
                                .push(AbiParam::new(type_id_to_cranelift(*return_type)));
                        }

                        let sig_ref = builder.import_signature(sig);

                        // Build argument list
                        let mut call_args = vec![recv_ptr];
                        for arg in args {
                            call_args.push(vreg_values[arg]);
                        }

                        // Indirect call
                        let call = builder.ins().call_indirect(sig_ref, method_ptr, &call_args);

                        if let Some(d) = dest {
                            let results = builder.inst_results(call);
                            if !results.is_empty() {
                                vreg_values.insert(*d, results[0]);
                            } else {
                                let null = builder.ins().iconst(types::I64, 0);
                                vreg_values.insert(*d, null);
                            }
                        }
                    }

                    MirInst::BuiltinMethod {
                        dest,
                        receiver,
                        receiver_type,
                        method,
                        args,
                    } => {
                        // Built-in methods on types like Array, String, Dict, etc.
                        let receiver_val = vreg_values[receiver];
                        let result = match (receiver_type.as_str(), method.as_str()) {
                            // Array methods
                            ("Array", "push") | ("array", "push") => {
                                let push_id = self.runtime_funcs["rt_array_push"];
                                let push_ref =
                                    self.module.declare_func_in_func(push_id, builder.func);
                                let arg_val = vreg_values[&args[0]];
                                let value_int_id = self.runtime_funcs["rt_value_int"];
                                let value_int_ref =
                                    self.module.declare_func_in_func(value_int_id, builder.func);
                                let wrap_call = builder.ins().call(value_int_ref, &[arg_val]);
                                let wrapped = builder.inst_results(wrap_call)[0];
                                let call = builder.ins().call(push_ref, &[receiver_val, wrapped]);
                                let result_i8 = builder.inst_results(call)[0];
                                Some(builder.ins().uextend(types::I64, result_i8))
                            }
                            ("Array", "get") | ("array", "get") => {
                                let get_id = self.runtime_funcs["rt_index_get"];
                                let get_ref =
                                    self.module.declare_func_in_func(get_id, builder.func);
                                let idx_val = vreg_values[&args[0]];
                                let value_int_id = self.runtime_funcs["rt_value_int"];
                                let value_int_ref =
                                    self.module.declare_func_in_func(value_int_id, builder.func);
                                let wrap_call = builder.ins().call(value_int_ref, &[idx_val]);
                                let wrapped_idx = builder.inst_results(wrap_call)[0];
                                let call =
                                    builder.ins().call(get_ref, &[receiver_val, wrapped_idx]);
                                Some(builder.inst_results(call)[0])
                            }
                            ("Array", "set") | ("array", "set") => {
                                let set_id = self.runtime_funcs["rt_index_set"];
                                let set_ref =
                                    self.module.declare_func_in_func(set_id, builder.func);
                                let idx_val = vreg_values[&args[0]];
                                let arg_val = vreg_values[&args[1]];
                                let value_int_id = self.runtime_funcs["rt_value_int"];
                                let value_int_ref =
                                    self.module.declare_func_in_func(value_int_id, builder.func);
                                let wrap_idx = builder.ins().call(value_int_ref, &[idx_val]);
                                let wrapped_idx = builder.inst_results(wrap_idx)[0];
                                let wrap_val = builder.ins().call(value_int_ref, &[arg_val]);
                                let wrapped_val = builder.inst_results(wrap_val)[0];
                                let call = builder
                                    .ins()
                                    .call(set_ref, &[receiver_val, wrapped_idx, wrapped_val]);
                                let result_i8 = builder.inst_results(call)[0];
                                Some(builder.ins().uextend(types::I64, result_i8))
                            }
                            ("Array", "len") | ("array", "len") => {
                                if let Some(&len_id) = self.runtime_funcs.get("rt_array_len") {
                                    let len_ref =
                                        self.module.declare_func_in_func(len_id, builder.func);
                                    let call = builder.ins().call(len_ref, &[receiver_val]);
                                    Some(builder.inst_results(call)[0])
                                } else {
                                    Some(builder.ins().iconst(types::I64, 0))
                                }
                            }

                            // String methods
                            ("String", "len") | ("string", "len") => {
                                if let Some(&len_id) = self.runtime_funcs.get("rt_string_len") {
                                    let len_ref =
                                        self.module.declare_func_in_func(len_id, builder.func);
                                    let call = builder.ins().call(len_ref, &[receiver_val]);
                                    Some(builder.inst_results(call)[0])
                                } else {
                                    Some(builder.ins().iconst(types::I64, 0))
                                }
                            }

                            // Dict methods
                            ("Dict", "get") | ("dict", "get") => {
                                let get_id = self.runtime_funcs["rt_index_get"];
                                let get_ref =
                                    self.module.declare_func_in_func(get_id, builder.func);
                                let key_val = vreg_values[&args[0]];
                                let value_int_id = self.runtime_funcs["rt_value_int"];
                                let value_int_ref =
                                    self.module.declare_func_in_func(value_int_id, builder.func);
                                let wrap_call = builder.ins().call(value_int_ref, &[key_val]);
                                let wrapped_key = builder.inst_results(wrap_call)[0];
                                let call =
                                    builder.ins().call(get_ref, &[receiver_val, wrapped_key]);
                                Some(builder.inst_results(call)[0])
                            }
                            ("Dict", "set") | ("dict", "set") => {
                                let set_id = self.runtime_funcs["rt_dict_set"];
                                let set_ref =
                                    self.module.declare_func_in_func(set_id, builder.func);
                                let key_val = vreg_values[&args[0]];
                                let val_val = vreg_values[&args[1]];
                                let value_int_id = self.runtime_funcs["rt_value_int"];
                                let value_int_ref =
                                    self.module.declare_func_in_func(value_int_id, builder.func);
                                let wrap_key = builder.ins().call(value_int_ref, &[key_val]);
                                let wrapped_key = builder.inst_results(wrap_key)[0];
                                let wrap_val = builder.ins().call(value_int_ref, &[val_val]);
                                let wrapped_val = builder.inst_results(wrap_val)[0];
                                let call = builder
                                    .ins()
                                    .call(set_ref, &[receiver_val, wrapped_key, wrapped_val]);
                                let result_i8 = builder.inst_results(call)[0];
                                Some(builder.ins().uextend(types::I64, result_i8))
                            }
                            ("Dict", "len") | ("dict", "len") => {
                                if let Some(&len_id) = self.runtime_funcs.get("rt_dict_len") {
                                    let len_ref =
                                        self.module.declare_func_in_func(len_id, builder.func);
                                    let call = builder.ins().call(len_ref, &[receiver_val]);
                                    Some(builder.inst_results(call)[0])
                                } else {
                                    Some(builder.ins().iconst(types::I64, 0))
                                }
                            }

                            // Tuple methods
                            ("Tuple", "get") | ("tuple", "get") => {
                                let get_id = self.runtime_funcs["rt_tuple_get"];
                                let get_ref =
                                    self.module.declare_func_in_func(get_id, builder.func);
                                let idx_val = vreg_values[&args[0]];
                                let call = builder.ins().call(get_ref, &[receiver_val, idx_val]);
                                Some(builder.inst_results(call)[0])
                            }
                            ("Tuple", "len") | ("tuple", "len") => {
                                if let Some(&len_id) = self.runtime_funcs.get("rt_tuple_len") {
                                    let len_ref =
                                        self.module.declare_func_in_func(len_id, builder.func);
                                    let call = builder.ins().call(len_ref, &[receiver_val]);
                                    Some(builder.inst_results(call)[0])
                                } else {
                                    Some(builder.ins().iconst(types::I64, 0))
                                }
                            }
                            ("Tuple", "set") | ("tuple", "set") => {
                                let set_id = self.runtime_funcs["rt_tuple_set"];
                                let set_ref =
                                    self.module.declare_func_in_func(set_id, builder.func);
                                let idx_val = vreg_values[&args[0]];
                                let arg_val = vreg_values[&args[1]];
                                let value_int_id = self.runtime_funcs["rt_value_int"];
                                let value_int_ref =
                                    self.module.declare_func_in_func(value_int_id, builder.func);
                                let wrap_call = builder.ins().call(value_int_ref, &[arg_val]);
                                let wrapped = builder.inst_results(wrap_call)[0];
                                let call = builder
                                    .ins()
                                    .call(set_ref, &[receiver_val, idx_val, wrapped]);
                                let result_i8 = builder.inst_results(call)[0];
                                Some(builder.ins().uextend(types::I64, result_i8))
                            }

                            // Array - pop method
                            ("Array", "pop") | ("array", "pop") => {
                                let pop_id = self.runtime_funcs["rt_array_pop"];
                                let pop_ref =
                                    self.module.declare_func_in_func(pop_id, builder.func);
                                let call = builder.ins().call(pop_ref, &[receiver_val]);
                                Some(builder.inst_results(call)[0])
                            }

                            // String - concat method
                            ("String", "concat") | ("string", "concat") => {
                                let concat_id = self.runtime_funcs["rt_string_concat"];
                                let concat_ref =
                                    self.module.declare_func_in_func(concat_id, builder.func);
                                let arg_val = vreg_values[&args[0]];
                                let call = builder.ins().call(concat_ref, &[receiver_val, arg_val]);
                                Some(builder.inst_results(call)[0])
                            }

                            // Array - clear method
                            ("Array", "clear") | ("array", "clear") => {
                                let clear_id = self.runtime_funcs["rt_array_clear"];
                                let clear_ref =
                                    self.module.declare_func_in_func(clear_id, builder.func);
                                let call = builder.ins().call(clear_ref, &[receiver_val]);
                                let result_i8 = builder.inst_results(call)[0];
                                Some(builder.ins().uextend(types::I64, result_i8))
                            }

                            // Dict - clear method
                            ("Dict", "clear") | ("dict", "clear") => {
                                let clear_id = self.runtime_funcs["rt_dict_clear"];
                                let clear_ref =
                                    self.module.declare_func_in_func(clear_id, builder.func);
                                let call = builder.ins().call(clear_ref, &[receiver_val]);
                                let result_i8 = builder.inst_results(call)[0];
                                Some(builder.ins().uextend(types::I64, result_i8))
                            }

                            // Dict - keys method
                            ("Dict", "keys") | ("dict", "keys") => {
                                let keys_id = self.runtime_funcs["rt_dict_keys"];
                                let keys_ref =
                                    self.module.declare_func_in_func(keys_id, builder.func);
                                let call = builder.ins().call(keys_ref, &[receiver_val]);
                                Some(builder.inst_results(call)[0])
                            }

                            // Dict - values method
                            ("Dict", "values") | ("dict", "values") => {
                                let values_id = self.runtime_funcs["rt_dict_values"];
                                let values_ref =
                                    self.module.declare_func_in_func(values_id, builder.func);
                                let call = builder.ins().call(values_ref, &[receiver_val]);
                                Some(builder.inst_results(call)[0])
                            }

                            // Array/Dict/String - contains method
                            ("Array", "contains")
                            | ("array", "contains")
                            | ("Dict", "contains")
                            | ("dict", "contains")
                            | ("String", "contains")
                            | ("string", "contains") => {
                                let contains_id = self.runtime_funcs["rt_contains"];
                                let contains_ref =
                                    self.module.declare_func_in_func(contains_id, builder.func);
                                let arg_val = vreg_values[&args[0]];
                                let call =
                                    builder.ins().call(contains_ref, &[receiver_val, arg_val]);
                                let result_i8 = builder.inst_results(call)[0];
                                Some(builder.ins().uextend(types::I64, result_i8))
                            }

                            // Array/String - slice method
                            ("Array", "slice")
                            | ("array", "slice")
                            | ("String", "slice")
                            | ("string", "slice") => {
                                let slice_id = self.runtime_funcs["rt_slice"];
                                let slice_ref =
                                    self.module.declare_func_in_func(slice_id, builder.func);
                                // slice(start, end, step) - step defaults to 1
                                let start = vreg_values[&args[0]];
                                let end = if args.len() > 1 {
                                    vreg_values[&args[1]]
                                } else {
                                    builder.ins().iconst(types::I64, i64::MAX)
                                };
                                let step = if args.len() > 2 {
                                    vreg_values[&args[2]]
                                } else {
                                    builder.ins().iconst(types::I64, 1)
                                };
                                let call = builder
                                    .ins()
                                    .call(slice_ref, &[receiver_val, start, end, step]);
                                Some(builder.inst_results(call)[0])
                            }

                            // Unknown method - call rt_method_not_found with type and method names
                            _ => {
                                // Create data for type name
                                let type_bytes = receiver_type.as_bytes();
                                let type_data_id = self
                                    .module
                                    .declare_anonymous_data(true, false)
                                    .map_err(|e| JitError::ModuleError(e.to_string()))?;
                                let mut type_data_desc = cranelift_module::DataDescription::new();
                                type_data_desc.define(type_bytes.to_vec().into_boxed_slice());
                                self.module
                                    .define_data(type_data_id, &type_data_desc)
                                    .map_err(|e| JitError::ModuleError(e.to_string()))?;

                                let type_global =
                                    self.module.declare_data_in_func(type_data_id, builder.func);
                                let type_ptr = builder.ins().global_value(types::I64, type_global);
                                let type_len =
                                    builder.ins().iconst(types::I64, type_bytes.len() as i64);

                                // Create data for method name
                                let method_bytes = method.as_bytes();
                                let method_data_id = self
                                    .module
                                    .declare_anonymous_data(true, false)
                                    .map_err(|e| JitError::ModuleError(e.to_string()))?;
                                let mut method_data_desc = cranelift_module::DataDescription::new();
                                method_data_desc.define(method_bytes.to_vec().into_boxed_slice());
                                self.module
                                    .define_data(method_data_id, &method_data_desc)
                                    .map_err(|e| JitError::ModuleError(e.to_string()))?;

                                let method_global = self
                                    .module
                                    .declare_data_in_func(method_data_id, builder.func);
                                let method_ptr =
                                    builder.ins().global_value(types::I64, method_global);
                                let method_len =
                                    builder.ins().iconst(types::I64, method_bytes.len() as i64);

                                let not_found_id = self.runtime_funcs["rt_method_not_found"];
                                let not_found_ref =
                                    self.module.declare_func_in_func(not_found_id, builder.func);
                                let call = builder.ins().call(
                                    not_found_ref,
                                    &[type_ptr, type_len, method_ptr, method_len],
                                );
                                Some(builder.inst_results(call)[0])
                            }
                        };

                        if let Some(d) = dest {
                            let val = result.unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
                            vreg_values.insert(*d, val);
                        }
                    }

                    // Phase 5: Pattern matching instructions
                    MirInst::PatternTest {
                        dest,
                        subject,
                        pattern,
                    } => {
                        // Pattern testing - compare subject against pattern
                        let subject_val = vreg_values[subject];

                        let result = match pattern {
                            crate::mir::MirPattern::Wildcard => {
                                // Wildcard always matches
                                builder.ins().iconst(types::I8, 1)
                            }
                            crate::mir::MirPattern::Literal(lit) => {
                                // Compare against literal value
                                match lit {
                                    crate::mir::MirLiteral::Int(n) => {
                                        let lit_val = builder.ins().iconst(types::I64, *n);
                                        builder.ins().icmp(
                                            cranelift_codegen::ir::condcodes::IntCC::Equal,
                                            subject_val,
                                            lit_val,
                                        )
                                    }
                                    crate::mir::MirLiteral::Bool(b) => {
                                        let lit_val =
                                            builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
                                        // Truncate subject to I8 for comparison
                                        let subject_i8 =
                                            builder.ins().ireduce(types::I8, subject_val);
                                        builder.ins().icmp(
                                            cranelift_codegen::ir::condcodes::IntCC::Equal,
                                            subject_i8,
                                            lit_val,
                                        )
                                    }
                                    crate::mir::MirLiteral::Nil => {
                                        // Check if subject is null/nil (zero)
                                        let zero = builder.ins().iconst(types::I64, 0);
                                        builder.ins().icmp(
                                            cranelift_codegen::ir::condcodes::IntCC::Equal,
                                            subject_val,
                                            zero,
                                        )
                                    }
                                    _ => {
                                        // Float/String comparisons need runtime support
                                        builder.ins().iconst(types::I8, 0)
                                    }
                                }
                            }
                            crate::mir::MirPattern::Binding(_) => {
                                // Binding patterns always match (value is bound elsewhere)
                                builder.ins().iconst(types::I8, 1)
                            }
                            crate::mir::MirPattern::Variant {
                                enum_name: _,
                                variant_name: _,
                                payload: _,
                            } => {
                                // Variant matching requires discriminant check
                                let disc_id = self.runtime_funcs["rt_enum_discriminant"];
                                let disc_ref =
                                    self.module.declare_func_in_func(disc_id, builder.func);
                                let call = builder.ins().call(disc_ref, &[subject_val]);
                                let disc = builder.inst_results(call)[0];
                                // Return discriminant != -1 (valid variant)
                                let neg_one = builder.ins().iconst(types::I64, -1);
                                builder.ins().icmp(
                                    cranelift_codegen::ir::condcodes::IntCC::NotEqual,
                                    disc,
                                    neg_one,
                                )
                            }
                            _ => {
                                // Complex patterns (Tuple, Struct, Or, Guard) need more work
                                builder.ins().iconst(types::I8, 0)
                            }
                        };
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::PatternBind {
                        dest,
                        subject,
                        binding,
                    } => {
                        // Extract value from subject according to binding path
                        // For now, just return the subject value (simplified)
                        let current = vreg_values[subject];

                        // If there's an enum payload step, extract it
                        let result = if binding
                            .path
                            .iter()
                            .any(|s| matches!(s, crate::mir::BindingStep::EnumPayload))
                        {
                            let payload_id = self.runtime_funcs["rt_enum_payload"];
                            let payload_ref =
                                self.module.declare_func_in_func(payload_id, builder.func);
                            let call = builder.ins().call(payload_ref, &[current]);
                            builder.inst_results(call)[0]
                        } else {
                            current
                        };
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::EnumDiscriminant { dest, value } => {
                        // Get enum discriminant using runtime function
                        let disc_id = self.runtime_funcs["rt_enum_discriminant"];
                        let disc_ref = self.module.declare_func_in_func(disc_id, builder.func);
                        let val = vreg_values[value];
                        let call = builder.ins().call(disc_ref, &[val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::EnumPayload { dest, value } => {
                        // Get enum payload using runtime function
                        let payload_id = self.runtime_funcs["rt_enum_payload"];
                        let payload_ref =
                            self.module.declare_func_in_func(payload_id, builder.func);
                        let val = vreg_values[value];
                        let call = builder.ins().call(payload_ref, &[val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::EnumUnit {
                        dest,
                        enum_name: _,
                        variant_name,
                    } => {
                        // Create unit enum variant using rt_enum_new
                        let enum_new_id = self.runtime_funcs["rt_enum_new"];
                        let enum_new_ref =
                            self.module.declare_func_in_func(enum_new_id, builder.func);

                        // Use hash of variant name as discriminant
                        let disc = variant_name
                            .bytes()
                            .fold(0u32, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u32));
                        let disc_val = builder.ins().iconst(types::I32, disc as i64);
                        let enum_id = builder.ins().iconst(types::I32, 0);
                        let nil_val = builder.ins().iconst(types::I64, 0);

                        let call = builder
                            .ins()
                            .call(enum_new_ref, &[enum_id, disc_val, nil_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::EnumWith {
                        dest,
                        enum_name: _,
                        variant_name,
                        payload,
                    } => {
                        // Create enum variant with payload using rt_enum_new
                        let enum_new_id = self.runtime_funcs["rt_enum_new"];
                        let enum_new_ref =
                            self.module.declare_func_in_func(enum_new_id, builder.func);

                        // Use hash of variant name as discriminant
                        let disc = variant_name
                            .bytes()
                            .fold(0u32, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u32));
                        let disc_val = builder.ins().iconst(types::I32, disc as i64);
                        let enum_id = builder.ins().iconst(types::I32, 0);
                        let payload_val = vreg_values[payload];

                        let call = builder
                            .ins()
                            .call(enum_new_ref, &[enum_id, disc_val, payload_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    // Phase 6: Async/Generator instructions
                    MirInst::FutureCreate { dest, body_block } => {
                        // Create a new future with body function pointer and captured ctx.
                        let future_new_id = self.runtime_funcs["rt_future_new"];
                        let future_new_ref = self
                            .module
                            .declare_func_in_func(future_new_id, builder.func);

                        let body_ptr = Self::func_block_addr(
                            &self.func_ids,
                            &mut self.module,
                            &func.name,
                            *body_block,
                            &mut builder,
                        );
                        let ctx_val = if let Some(meta) = func.outlined_bodies.get(body_block) {
                            if meta.live_ins.is_empty() {
                                builder.ins().iconst(types::I64, 0)
                            } else {
                                let cap = builder.ins().iconst(types::I64, meta.live_ins.len() as i64);
                                let new_id = self.runtime_funcs["rt_array_new"];
                                let new_ref =
                                    self.module.declare_func_in_func(new_id, builder.func);
                                let new_call = builder.ins().call(new_ref, &[cap]);
                                let arr = builder.inst_results(new_call)[0];
                                let push_id = self.runtime_funcs["rt_array_push"];
                                let push_ref =
                                    self.module.declare_func_in_func(push_id, builder.func);
                                for reg in &meta.live_ins {
                                    let val = vreg_values[reg];
                                    let _ = builder.ins().call(push_ref, &[arr, val]);
                                }
                                arr
                            }
                        } else {
                            builder.ins().iconst(types::I64, 0)
                        };
                        let call = builder.ins().call(future_new_ref, &[body_ptr, ctx_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::Await { dest, future } => {
                        // Await a future
                        let await_id = self.runtime_funcs["rt_future_await"];
                        let await_ref = self.module.declare_func_in_func(await_id, builder.func);

                        let future_val = vreg_values[future];
                        let call = builder.ins().call(await_ref, &[future_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::ActorSpawn { dest, body_block } => {
                        // Spawn actor using runtime hook with captured ctx.
                        let spawn_id = self.runtime_funcs["rt_actor_spawn"];
                        let spawn_ref = self.module.declare_func_in_func(spawn_id, builder.func);

                        let body_ptr = Self::func_block_addr(
                            &self.func_ids,
                            &mut self.module,
                            &func.name,
                            *body_block,
                            &mut builder,
                        );
                        let ctx_val = if let Some(meta) = func.outlined_bodies.get(body_block) {
                            if meta.live_ins.is_empty() {
                                builder.ins().iconst(types::I64, 0)
                            } else {
                                let cap = builder.ins().iconst(types::I64, meta.live_ins.len() as i64);
                                let new_id = self.runtime_funcs["rt_array_new"];
                                let new_ref =
                                    self.module.declare_func_in_func(new_id, builder.func);
                                let new_call = builder.ins().call(new_ref, &[cap]);
                                let arr = builder.inst_results(new_call)[0];
                                let push_id = self.runtime_funcs["rt_array_push"];
                                let push_ref =
                                    self.module.declare_func_in_func(push_id, builder.func);
                                for reg in &meta.live_ins {
                                    let val = vreg_values[reg];
                                    let _ = builder.ins().call(push_ref, &[arr, val]);
                                }
                                arr
                            }
                        } else {
                            builder.ins().iconst(types::I64, 0)
                        };
                        let call = builder.ins().call(spawn_ref, &[body_ptr, ctx_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::ActorSend { actor, message } => {
                        let send_id = self.runtime_funcs["rt_actor_send"];
                        let send_ref = self.module.declare_func_in_func(send_id, builder.func);

                        let actor_val = vreg_values[actor];
                        let msg_val = vreg_values[message];
                        builder.ins().call(send_ref, &[actor_val, msg_val]);
                    }

                    MirInst::ActorRecv { dest } => {
                        let recv_id = self.runtime_funcs["rt_actor_recv"];
                        let recv_ref = self.module.declare_func_in_func(recv_id, builder.func);

                        let call = builder.ins().call(recv_ref, &[]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::GeneratorCreate { dest, body_block } => {
                        // Create a new generator with body function pointer and captured ctx.
                        let gen_new_id = self.runtime_funcs["rt_generator_new"];
                        let gen_new_ref =
                            self.module.declare_func_in_func(gen_new_id, builder.func);

                        // Lower generator body to state machine if outlined
                        let body_ptr = Self::func_block_addr(
                            &self.func_ids,
                            &mut self.module,
                            &func.name,
                            *body_block,
                            &mut builder,
                        );
                        let (ctx_val, slot_count) = if let Some(meta) = func.outlined_bodies.get(body_block) {
                            let ctx = if meta.live_ins.is_empty() {
                                builder.ins().iconst(types::I64, 0)
                            } else {
                                let cap = builder.ins().iconst(types::I64, meta.live_ins.len() as i64);
                                let new_id = self.runtime_funcs["rt_array_new"];
                                let new_ref =
                                    self.module.declare_func_in_func(new_id, builder.func);
                                let new_call = builder.ins().call(new_ref, &[cap]);
                                let arr = builder.inst_results(new_call)[0];
                                let push_id = self.runtime_funcs["rt_array_push"];
                                let push_ref =
                                    self.module.declare_func_in_func(push_id, builder.func);
                                for reg in &meta.live_ins {
                                    let val = vreg_values[reg];
                                    let _ = builder.ins().call(push_ref, &[arr, val]);
                                }
                                arr
                            };
                            (ctx, meta.frame_slots.unwrap_or(0) as i64)
                        } else {
                            (builder.ins().iconst(types::I64, 0), 0)
                        };
                        let slots_val = builder.ins().iconst(types::I64, slot_count);
                        let call = builder.ins().call(gen_new_ref, &[body_ptr, slots_val, ctx_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::Yield { value } => {
                        if let Some(state_map) = generator_state_map.as_ref() {
                            if let Some(state) = state_map.get(&mir_block.id) {
                                let gen_param = builder.block_params(entry_block)[0];
                                let store_id = self.runtime_funcs["rt_generator_store_slot"];
                                let store_ref =
                                    self.module.declare_func_in_func(store_id, builder.func);
                                for (idx, reg) in state.live_after_yield.iter().enumerate() {
                                    let val = vreg_values[reg];
                                    let idx_val = builder.ins().iconst(types::I64, idx as i64);
                                    let _ = builder.ins().call(store_ref, &[gen_param, idx_val, val]);
                                }

                                let set_state_id = self.runtime_funcs["rt_generator_set_state"];
                                let set_state_ref =
                                    self.module.declare_func_in_func(set_state_id, builder.func);
                                let next_state =
                                    builder.ins().iconst(types::I64, (state.state_id + 1) as i64);
                                let _ = builder.ins().call(set_state_ref, &[gen_param, next_state]);

                                let val = vreg_values[value];
                                builder.ins().return_(&[val]);
                                continue;
                            }
                        }
                        builder
                            .ins()
                            .trap(cranelift_codegen::ir::TrapCode::unwrap_user(2));
                    }

                    MirInst::GeneratorNext { dest, generator } => {
                        // Get next value from generator
                        let next_id = self.runtime_funcs["rt_generator_next"];
                        let next_ref = self.module.declare_func_in_func(next_id, builder.func);

                        let gen_val = vreg_values[generator];
                        let call = builder.ins().call(next_ref, &[gen_val]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    // Phase 7: Error handling instructions
                    // Option/Result representation: { discriminant: i64, payload: i64 }
                    // Option: Some=1, None=0
                    // Result: Ok=1, Err=0
                    MirInst::TryUnwrap {
                        dest,
                        value,
                        error_block,
                        error_dest,
                    } => {
                        // Check discriminant and branch to error block if None/Err
                        let val = vreg_values[value];

                        // Load discriminant (first 8 bytes)
                        let disc = builder.ins().load(types::I64, MemFlags::new(), val, 0);

                        // Check if discriminant is 0 (None/Err)
                        let zero = builder.ins().iconst(types::I64, 0);
                        let is_error = builder.ins().icmp(
                            cranelift_codegen::ir::condcodes::IntCC::Equal,
                            disc,
                            zero,
                        );

                        // Create success and error continuation blocks
                        let success_block = builder.create_block();
                        let err_block = *blocks.get(error_block).unwrap();

                        builder
                            .ins()
                            .brif(is_error, err_block, &[], success_block, &[]);

                        // Success block: extract payload
                        builder.switch_to_block(success_block);
                        let payload = builder.ins().load(types::I64, MemFlags::new(), val, 8);
                        vreg_values.insert(*dest, payload);

                        // Also set up error_dest for the error case
                        vreg_values.insert(*error_dest, val);
                    }

                    MirInst::OptionSome { dest, value } => {
                        // Allocate Option: { discriminant=1, payload=value }
                        let alloc_id = self.runtime_funcs["rt_alloc"];
                        let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);

                        let size = builder.ins().iconst(types::I64, 16);
                        let call = builder.ins().call(alloc_ref, &[size]);
                        let ptr = builder.inst_results(call)[0];

                        // Store discriminant = 1 (Some)
                        let one = builder.ins().iconst(types::I64, 1);
                        builder.ins().store(MemFlags::new(), one, ptr, 0);

                        // Store payload
                        let val = vreg_values[value];
                        builder.ins().store(MemFlags::new(), val, ptr, 8);

                        vreg_values.insert(*dest, ptr);
                    }

                    MirInst::OptionNone { dest } => {
                        // Allocate Option: { discriminant=0, payload=0 }
                        let alloc_id = self.runtime_funcs["rt_alloc"];
                        let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);

                        let size = builder.ins().iconst(types::I64, 16);
                        let call = builder.ins().call(alloc_ref, &[size]);
                        let ptr = builder.inst_results(call)[0];

                        // Store discriminant = 0 (None)
                        let zero = builder.ins().iconst(types::I64, 0);
                        builder.ins().store(MemFlags::new(), zero, ptr, 0);
                        builder.ins().store(MemFlags::new(), zero, ptr, 8);

                        vreg_values.insert(*dest, ptr);
                    }

                    MirInst::ResultOk { dest, value } => {
                        // Allocate Result: { discriminant=1, payload=value }
                        let alloc_id = self.runtime_funcs["rt_alloc"];
                        let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);

                        let size = builder.ins().iconst(types::I64, 16);
                        let call = builder.ins().call(alloc_ref, &[size]);
                        let ptr = builder.inst_results(call)[0];

                        // Store discriminant = 1 (Ok)
                        let one = builder.ins().iconst(types::I64, 1);
                        builder.ins().store(MemFlags::new(), one, ptr, 0);

                        // Store payload
                        let val = vreg_values[value];
                        builder.ins().store(MemFlags::new(), val, ptr, 8);

                        vreg_values.insert(*dest, ptr);
                    }

                    MirInst::ResultErr { dest, value } => {
                        // Allocate Result: { discriminant=0, payload=error }
                        let alloc_id = self.runtime_funcs["rt_alloc"];
                        let alloc_ref = self.module.declare_func_in_func(alloc_id, builder.func);

                        let size = builder.ins().iconst(types::I64, 16);
                        let call = builder.ins().call(alloc_ref, &[size]);
                        let ptr = builder.inst_results(call)[0];

                        // Store discriminant = 0 (Err)
                        let zero = builder.ins().iconst(types::I64, 0);
                        builder.ins().store(MemFlags::new(), zero, ptr, 0);

                        // Store error value
                        let val = vreg_values[value];
                        builder.ins().store(MemFlags::new(), val, ptr, 8);

                        vreg_values.insert(*dest, ptr);
                    }
                }
            }

            // Compile terminator
            if skip_entry_terminator && mir_block.id == func.entry_block {
                continue;
            }
            match &mir_block.terminator {
                Terminator::Return(val) => {
                    if generator_states.is_some() {
                        let gen_param = builder.block_params(entry_block)[0];
                        let set_state_id = self.runtime_funcs["rt_generator_set_state"];
                        let set_state_ref =
                            self.module.declare_func_in_func(set_state_id, builder.func);
                        let done_state =
                            builder.ins().iconst(types::I64, generator_state_len as i64);
                        let _ = builder.ins().call(set_state_ref, &[gen_param, done_state]);
                        let mark_id = self.runtime_funcs["rt_generator_mark_done"];
                        let mark_ref =
                            self.module.declare_func_in_func(mark_id, builder.func);
                        let _ = builder.ins().call(mark_ref, &[gen_param]);
                    }
                    if let Some(v) = val {
                        let ret_val = vreg_values[v];
                        builder.ins().return_(&[ret_val]);
                    } else if func.return_type == TypeId::VOID {
                        builder.ins().return_(&[]);
                    } else {
                        builder
                            .ins()
                            .trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
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
                    let cond_val = vreg_values[cond];
                    let then_bl = *blocks.get(then_block).unwrap();
                    let else_bl = *blocks.get(else_block).unwrap();
                    builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
                }

                Terminator::Unreachable => {
                    builder
                        .ins()
                        .trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
                }
            }
        }

        // Seal all blocks
        for mir_block in &func.blocks {
            let cl_block = *blocks.get(&mir_block.id).unwrap();
            builder.seal_block(cl_block);
        }

        builder.finalize();

        // Verify the function
        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            return Err(JitError::Compilation(format!(
                "Verifier errors:\n{}",
                errors
            )));
        }

        // Define the function
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| JitError::ModuleError(format!("Compilation error: {}", e)))?;

        self.module.clear_context(&mut self.ctx);

        Ok(())
    }
}

impl Default for JitCompiler {
    fn default() -> Self {
        Self::new().expect("Failed to create JIT compiler")
    }
}

#[cfg(test)]
#[path = "jit_tests.rs"]
mod tests;
