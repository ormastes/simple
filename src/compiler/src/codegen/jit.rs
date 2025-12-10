//! JIT (Just-In-Time) compilation module using Cranelift.
//!
//! This module provides JIT compilation for Simple functions, allowing
//! the interpreter to compile hot paths to native code at runtime.

use std::collections::HashMap;

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use target_lexicon::Triple;
use thiserror::Error;

use crate::hir::{BinOp, TypeId, UnaryOp};
use crate::mir::{MirFunction, MirInst, MirModule, Terminator, VReg};

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
        &mut self,
        parent_name: &str,
        block: crate::mir::BlockId,
        builder: &mut FunctionBuilder,
    ) -> cranelift_codegen::ir::Value {
        let name = format!("{}_outlined_{}", parent_name, block.0);
        let func_id = *self
            .func_ids
            .get(&name)
            .unwrap_or_else(|| panic!("outlined function {name} not declared"));
        let func_ref = self.module.declare_func_in_func(func_id, builder.func);
        builder.ins().func_addr(types::I64, func_ref)
    }

    /// Declare external runtime functions for FFI
    fn declare_runtime_functions(
        module: &mut JITModule,
    ) -> JitResult<HashMap<&'static str, cranelift_module::FuncId>> {
        let mut funcs = HashMap::new();
        let call_conv = CallConv::SystemV;

        // rt_array_new(capacity: u64) -> RuntimeValue (i64)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_array_new", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_array_new", id);

        // rt_array_push(array: RuntimeValue, value: RuntimeValue) -> bool (i8)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I8));
        let id = module
            .declare_function("rt_array_push", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_array_push", id);

        // rt_array_pop(array: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_array_pop", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_array_pop", id);

        // rt_array_len(array: RuntimeValue) -> i64
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_array_len", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_array_len", id);

        // rt_string_len(string: RuntimeValue) -> i64
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_string_len", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_string_len", id);

        // rt_tuple_new(len: u64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_tuple_new", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_tuple_new", id);

        // rt_tuple_set(tuple: RuntimeValue, index: u64, value: RuntimeValue) -> bool
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I8));
        let id = module
            .declare_function("rt_tuple_set", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_tuple_set", id);

        // rt_tuple_get(tuple: RuntimeValue, index: u64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_tuple_get", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_tuple_get", id);

        // rt_tuple_len(tuple: RuntimeValue) -> i64
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_tuple_len", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_tuple_len", id);

        // rt_dict_new(capacity: u64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_dict_new", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_dict_new", id);

        // rt_dict_set(dict: RuntimeValue, key: RuntimeValue, value: RuntimeValue) -> bool
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I8));
        let id = module
            .declare_function("rt_dict_set", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_dict_set", id);

        // rt_dict_len(dict: RuntimeValue) -> i64
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_dict_len", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_dict_len", id);

        // rt_index_get(collection: RuntimeValue, index: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_index_get", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_index_get", id);

        // rt_index_set(collection: RuntimeValue, index: RuntimeValue, value: RuntimeValue) -> bool
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I8));
        let id = module
            .declare_function("rt_index_set", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_index_set", id);

        // rt_slice(collection: RuntimeValue, start: i64, end: i64, step: i64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_slice", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_slice", id);

        // rt_value_int(value: i64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_value_int", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_value_int", id);

        // rt_string_new(bytes: *const u8, len: u64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64)); // pointer
        sig.params.push(AbiParam::new(types::I64)); // len
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_string_new", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_string_new", id);

        // rt_string_concat(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_string_concat", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_string_concat", id);

        // rt_contains(collection: RuntimeValue, value: RuntimeValue) -> bool (i8)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I8));
        let id = module
            .declare_function("rt_contains", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_contains", id);

        // rt_alloc(size: u64) -> *mut u8
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_alloc", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_alloc", id);

        // rt_enum_new(enum_id: u32, discriminant: u32, payload: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I32));
        sig.params.push(AbiParam::new(types::I32));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_enum_new", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_enum_new", id);

        // rt_enum_discriminant(value: RuntimeValue) -> i64
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_enum_discriminant", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_enum_discriminant", id);

        // rt_enum_payload(value: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_enum_payload", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_enum_payload", id);

        // rt_wait(target: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_wait", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_wait", id);

        // rt_future_new(body_func: u64, ctx: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_future_new", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_future_new", id);

        // rt_future_await(future: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_future_await", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_future_await", id);

        // rt_actor_spawn(body_func: u64, ctx: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_actor_spawn", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_actor_spawn", id);

        // rt_actor_send(actor: RuntimeValue, message: RuntimeValue)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_actor_send", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_actor_send", id);

        // rt_actor_recv() -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_actor_recv", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_actor_recv", id);

        // rt_generator_new(body_func: u64, ctx: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_generator_new", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_generator_new", id);

        // rt_generator_yield(value: RuntimeValue)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_generator_yield", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_generator_yield", id);

        // rt_generator_next(generator: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_generator_next", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_generator_next", id);

        // =====================================================================
        // Dict/Array helper methods
        // =====================================================================

        // rt_dict_clear(dict: RuntimeValue) -> bool
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I8));
        let id = module
            .declare_function("rt_dict_clear", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_dict_clear", id);

        // rt_dict_keys(dict: RuntimeValue) -> RuntimeValue (array)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_dict_keys", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_dict_keys", id);

        // rt_dict_values(dict: RuntimeValue) -> RuntimeValue (array)
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_dict_values", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_dict_values", id);

        // rt_array_clear(array: RuntimeValue) -> bool
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I8));
        let id = module
            .declare_function("rt_array_clear", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_array_clear", id);

        // =====================================================================
        // Interpreter bridge FFI
        // =====================================================================

        // rt_interp_call(name_ptr: *const u8, name_len: u64, args: RuntimeValue) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64)); // name_ptr
        sig.params.push(AbiParam::new(types::I64)); // name_len
        sig.params.push(AbiParam::new(types::I64)); // args (RuntimeValue array)
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_interp_call", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_interp_call", id);

        // rt_interp_eval(expr_index: u64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_interp_eval", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_interp_eval", id);

        // =====================================================================
        // Error handling
        // =====================================================================

        // rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64)); // name_ptr
        sig.params.push(AbiParam::new(types::I64)); // name_len
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_function_not_found", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_function_not_found", id);

        // rt_method_not_found(type_ptr, type_len, method_ptr, method_len) -> RuntimeValue
        let mut sig = Signature::new(call_conv);
        sig.params.push(AbiParam::new(types::I64)); // type_ptr
        sig.params.push(AbiParam::new(types::I64)); // type_len
        sig.params.push(AbiParam::new(types::I64)); // method_ptr
        sig.params.push(AbiParam::new(types::I64)); // method_len
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("rt_method_not_found", Linkage::Import, &sig)
            .map_err(|e| JitError::ModuleError(e.to_string()))?;
        funcs.insert("rt_method_not_found", id);

        Ok(funcs)
    }

    /// Convert TypeId to Cranelift type for zero-cost codegen
    fn type_id_to_cranelift(type_id: TypeId) -> cranelift_codegen::ir::Type {
        match type_id {
            TypeId::VOID => types::I64, // Use I64 for void (no actual value)
            TypeId::BOOL => types::I8,
            TypeId::I8 => types::I8,
            TypeId::I16 => types::I16,
            TypeId::I32 => types::I32,
            TypeId::I64 => types::I64,
            TypeId::U8 => types::I8,
            TypeId::U16 => types::I16,
            TypeId::U32 => types::I32,
            TypeId::U64 => types::I64,
            TypeId::F32 => types::F32,
            TypeId::F64 => types::F64,
            TypeId::STRING => types::I64, // Pointer
            TypeId::NIL => types::I64,    // Tagged value
            _ => types::I64,              // All other types are pointers
        }
    }

    /// Get the size in bytes for a TypeId
    fn type_id_size(type_id: TypeId) -> u32 {
        match type_id {
            TypeId::VOID => 0,
            TypeId::BOOL => 1,
            TypeId::I8 | TypeId::U8 => 1,
            TypeId::I16 | TypeId::U16 => 2,
            TypeId::I32 | TypeId::U32 | TypeId::F32 => 4,
            TypeId::I64 | TypeId::U64 | TypeId::F64 => 8,
            TypeId::STRING | TypeId::NIL => 8,
            _ => 8, // All other types are pointers
        }
    }

    /// Compile a MIR module and return function pointers.
    pub fn compile_module(&mut self, mir: &MirModule) -> JitResult<()> {
        self.declare_outlined_functions(mir)?;

        // First pass: declare all functions
        for func in &mir.functions {
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
        for func in &mir.functions {
            self.compile_function(func)?;
        }

        // Finalize all functions (make them executable)
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::ModuleError(e.to_string()))?;

        // Store function pointers
        for func in &mir.functions {
            if let Some(&func_id) = self.func_ids.get(&func.name) {
                let ptr = self.module.get_finalized_function(func_id);
                self.compiled_funcs.insert(func.name.clone(), ptr);
            }
        }

        Ok(())
    }

    /// Declare trivial outlined functions for each body_block encountered.
    fn declare_outlined_functions(&mut self, mir: &MirModule) -> JitResult<()> {
        for func in &mir.functions {
            for block in &func.blocks {
                for inst in &block.instructions {
                    let body_block_opt = match inst {
                        MirInst::ActorSpawn { body_block, .. }
                        | MirInst::GeneratorCreate { body_block, .. }
                        | MirInst::FutureCreate { body_block, .. } => Some(*body_block),
                        _ => None,
                    };
                    if let Some(body_block) = body_block_opt {
                        let name = format!("{}_outlined_{}", func.name, body_block.0);
                        if self.func_ids.contains_key(&name) {
                            continue;
                        }
                        let mut sig = Signature::new(CallConv::SystemV);
                        sig.params.push(AbiParam::new(types::I64)); // ctx
                        let id = self
                            .module
                            .declare_function(&name, Linkage::Local, &sig)
                            .map_err(|e| JitError::ModuleError(e.to_string()))?;
                        self.func_ids.insert(name.clone(), id);

                        // Define trivial body: fn(ctx) { return; }
                        let mut ctx = self.module.make_context();
                        ctx.func.signature = sig;
                        ctx.func.name = UserFuncName::user(0, id.as_u32());
                        {
                            let mut fb_ctx = FunctionBuilderContext::new();
                            let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
                            let block = fb.create_block();
                            fb.append_block_params_for_function_params(block);
                            fb.switch_to_block(block);
                            fb.seal_block(block);
                            fb.ins().return_(&[]);
                            fb.finalize();
                        }
                        self.module
                            .define_function(id, &mut ctx)
                            .map_err(|e| JitError::ModuleError(e.to_string()))?;
                        self.module.clear_context(&mut ctx);
                    }
                }
            }
        }
        Ok(())
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
            let ty = Self::type_to_cranelift(param.ty);
            sig.params.push(AbiParam::new(ty));
        }

        // Add return type
        if func.return_type != TypeId::VOID {
            let ret_ty = Self::type_to_cranelift(func.return_type);
            sig.returns.push(AbiParam::new(ret_ty));
        }

        sig
    }

    fn type_to_cranelift(ty: TypeId) -> types::Type {
        match ty {
            TypeId::VOID => types::I64, // Void returns use I64 for ABI compatibility
            TypeId::BOOL => types::I8,
            TypeId::I8 | TypeId::U8 => types::I8,
            TypeId::I16 | TypeId::U16 => types::I16,
            TypeId::I32 | TypeId::U32 => types::I32,
            TypeId::I64 | TypeId::U64 => types::I64,
            TypeId::F32 => types::F32,
            TypeId::F64 => types::F64,
            TypeId::STRING => types::I64, // String pointer
            TypeId::NIL => types::I64,    // Nil is pointer-sized
            _ => types::I64,              // Custom types default to pointer-sized
        }
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
            let ty = Self::type_to_cranelift(param.ty);
            builder.declare_var(var, ty);
            variables.insert(i, var);
            var_idx += 1;
        }

        for (i, local) in func.locals.iter().enumerate() {
            let var = Variable::from_u32(var_idx);
            let ty = Self::type_to_cranelift(local.ty);
            builder.declare_var(var, ty);
            variables.insert(func.params.len() + i, var);
            var_idx += 1;
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

        // Initialize parameter variables
        for (i, _param) in func.params.iter().enumerate() {
            let val = builder.block_params(entry_block)[i];
            let var = variables[&i];
            builder.def_var(var, val);
        }

        // Compile each block
        let mut vreg_values: HashMap<VReg, cranelift_codegen::ir::Value> = HashMap::new();
        let mut local_addr_map: HashMap<VReg, usize> = HashMap::new();

        for mir_block in &func.blocks {
            let cl_block = *blocks.get(&mir_block.id).unwrap();

            if mir_block.id != func.entry_block {
                builder.switch_to_block(cl_block);
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
                        let size = Self::type_id_size(*ty) as i64;
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
                        let string_new_ref = self
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
                                .push(AbiParam::new(Self::type_id_to_cranelift(*param_ty)));
                        }
                        if *return_type != TypeId::VOID {
                            sig.returns
                                .push(AbiParam::new(Self::type_id_to_cranelift(*return_type)));
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
                            let cranelift_ty = Self::type_id_to_cranelift(*field_type);

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
                        let cranelift_ty = Self::type_id_to_cranelift(*field_type);

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
                                .push(AbiParam::new(Self::type_id_to_cranelift(*param_ty)));
                        }
                        if *return_type != TypeId::VOID {
                            sig.returns
                                .push(AbiParam::new(Self::type_id_to_cranelift(*return_type)));
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
                        // Create a new future with body function pointer
                        let future_new_id = self.runtime_funcs["rt_future_new"];
                        let future_new_ref = self
                            .module
                            .declare_func_in_func(future_new_id, builder.func);

                        let body_ptr = self.func_block_addr(&func.name, *body_block, builder);
                        let nil_ctx = builder.ins().iconst(types::I64, 0);
                        let call = builder.ins().call(future_new_ref, &[body_ptr, nil_ctx]);
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
                        // Spawn actor using runtime hook; body pointer should be outlined (stubbed)
                        let spawn_id = self.runtime_funcs["rt_actor_spawn"];
                        let spawn_ref = self.module.declare_func_in_func(spawn_id, builder.func);

                        let body_ptr = self.func_block_addr(&func.name, *body_block, builder);
                        let nil_ctx = builder.ins().iconst(types::I64, 0);
                        let call = builder.ins().call(spawn_ref, &[body_ptr, nil_ctx]);
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
                        // Create a new generator with body function pointer
                        let gen_new_id = self.runtime_funcs["rt_generator_new"];
                        let gen_new_ref =
                            self.module.declare_func_in_func(gen_new_id, builder.func);

                        let body_ptr = self.func_block_addr(&func.name, *body_block, builder);
                        let nil_ctx = builder.ins().iconst(types::I64, 0);
                        let call = builder.ins().call(gen_new_ref, &[body_ptr, nil_ctx]);
                        let result = builder.inst_results(call)[0];
                        vreg_values.insert(*dest, result);
                    }

                    MirInst::Yield { value } => {
                        let yield_id = self.runtime_funcs["rt_generator_yield"];
                        let yield_ref = self.module.declare_func_in_func(yield_id, builder.func);

                        let val = vreg_values[value];
                        builder.ins().call(yield_ref, &[val]);
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
            match &mir_block.terminator {
                Terminator::Return(val) => {
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
mod tests {
    use super::*;
    use crate::hir;
    use crate::mir::lower_to_mir;
    use simple_parser::Parser;

    fn jit_compile(source: &str) -> JitResult<JitCompiler> {
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast).expect("hir lower failed");
        let mir_module = lower_to_mir(&hir_module).expect("mir lower failed");

        let mut jit = JitCompiler::new()?;
        jit.compile_module(&mir_module)?;
        Ok(jit)
    }

    #[test]
    fn test_jit_simple_return() {
        let jit = jit_compile("fn answer() -> i64:\n    return 42\n").unwrap();
        let result = unsafe { jit.call_i64_void("answer").unwrap() };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_jit_add() {
        let jit = jit_compile("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();
        let result = unsafe { jit.call_i64_i64_i64("add", 10, 32).unwrap() };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_jit_subtract() {
        let jit = jit_compile("fn sub(a: i64, b: i64) -> i64:\n    return a - b\n").unwrap();
        let result = unsafe { jit.call_i64_i64_i64("sub", 50, 8).unwrap() };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_jit_multiply() {
        let jit = jit_compile("fn mul(a: i64, b: i64) -> i64:\n    return a * b\n").unwrap();
        let result = unsafe { jit.call_i64_i64_i64("mul", 6, 7).unwrap() };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_jit_negate() {
        let jit = jit_compile("fn neg(x: i64) -> i64:\n    return -x\n").unwrap();
        let result = unsafe { jit.call_i64_i64("neg", -42).unwrap() };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_jit_conditional() {
        let jit = jit_compile(
            "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
        ).unwrap();

        let result1 = unsafe { jit.call_i64_i64_i64("max", 42, 10).unwrap() };
        assert_eq!(result1, 42);

        let result2 = unsafe { jit.call_i64_i64_i64("max", 10, 42).unwrap() };
        assert_eq!(result2, 42);
    }

    #[test]
    fn test_jit_recursive_factorial() {
        let jit = jit_compile(
            r#"fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)
"#,
        )
        .unwrap();

        let result = unsafe { jit.call_i64_i64("factorial", 5).unwrap() };
        assert_eq!(result, 120);
    }
}
