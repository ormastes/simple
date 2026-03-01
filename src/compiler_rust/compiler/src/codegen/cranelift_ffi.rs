//! Cranelift FFI Bindings for Self-Hosting Simple Compiler
//!
//! This module provides FFI functions that expose Cranelift code generation
//! capabilities to Simple code. This enables the self-hosting compiler
//! (simple/compiler/*.spl) to generate native code via Cranelift.
//!
//! # Architecture
//!
//! Uses a two-registry pattern to handle FunctionBuilder's self-referential lifetime:
//! - BUILDER_BACKINGS: Owns Context + FunctionBuilderContext (Box'd for stable heap addresses)
//! - ACTIVE_BUILDERS: Owns FunctionBuilder (with transmuted 'static lifetime) + value maps
//!
//! The builder is created in begin_function and finalized/dropped in end_function,
//! always BEFORE the backing data is freed (maintaining lifetime safety).
//!
//! # Usage from Simple
//!
//! ```simple
//! extern fn rt_cranelift_new_module(name_ptr: i64, name_len: i64, target: i64) -> i64
//! extern fn rt_cranelift_begin_function(module: i64, name_ptr: i64, name_len: i64, sig: i64) -> i64
//! # ... etc
//! ```

use std::collections::HashMap;
use std::sync::Mutex;

use cranelift_codegen::ir::{
    types, AbiParam, Block, FuncRef, Function, InstBuilder, MemFlags, Signature,
    StackSlotData, StackSlotKind, StackSlot, TrapCode, Value,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use target_lexicon::Triple;

use lazy_static::lazy_static;
use simple_runtime::RuntimeValue;
use simple_runtime::value::{rt_string_len, rt_string_data};

// ============================================================================
// Handle Management
// ============================================================================

static HANDLE_COUNTER: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

fn next_handle() -> i64 {
    HANDLE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

// ============================================================================
// Registry Types
// ============================================================================

/// Context for JIT compilation
struct JITModuleContext {
    module: JITModule,
    func_ids: HashMap<String, FuncId>,
}

/// Context for AOT compilation
struct ObjectModuleContext {
    module: ObjectModule,
    func_ids: HashMap<String, FuncId>,
}

/// Backing storage for a function being built.
/// Box'd for stable heap address since FunctionBuilder holds references into these.
struct BuilderBacking {
    ctx: Context,
    func_builder_ctx: FunctionBuilderContext,
}

/// Active function builder state.
/// The FunctionBuilder has a transmuted 'static lifetime that actually borrows
/// from the corresponding BuilderBacking (which has a stable heap address via Box).
struct ActiveBuilder {
    builder: Option<FunctionBuilder<'static>>,
    blocks: HashMap<i64, Block>,
    values: HashMap<i64, Value>,
    stack_slots: HashMap<i64, StackSlot>,
    func_refs: HashMap<i64, FuncRef>,
    next_block_id: i64,
    next_value_id: i64,
    module_handle: i64,
    is_jit: bool,
    func_name: String,
}

/// Finished function context, ready for define_function.
struct FinishedFunc {
    ctx: Context,
    name: String,
    module_handle: i64,
    is_jit: bool,
}

// ============================================================================
// Global Registries
// ============================================================================

lazy_static! {
    static ref JIT_MODULES: Mutex<HashMap<i64, JITModuleContext>> = Mutex::new(HashMap::new());
    static ref AOT_MODULES: Mutex<HashMap<i64, ObjectModuleContext>> = Mutex::new(HashMap::new());
    static ref SIGNATURES: Mutex<HashMap<i64, Signature>> = Mutex::new(HashMap::new());
    static ref BUILDER_BACKINGS: Mutex<HashMap<i64, Box<BuilderBacking>>> = Mutex::new(HashMap::new());
    static ref ACTIVE_BUILDERS: Mutex<HashMap<i64, ActiveBuilder>> = Mutex::new(HashMap::new());
    static ref FINISHED_FUNCS: Mutex<HashMap<i64, FinishedFunc>> = Mutex::new(HashMap::new());
    static ref DECLARED_FUNCS: Mutex<HashMap<i64, FuncId>> = Mutex::new(HashMap::new());
}

/// Clear all Cranelift FFI global registries.
/// Called between test runs to prevent OOM from accumulated state.
pub fn clear_cranelift_registries() {
    // Drop builders BEFORE backings to maintain safety invariant
    {
        let mut active = ACTIVE_BUILDERS.lock().unwrap();
        for (_, mut ab) in active.drain() {
            if let Some(builder) = ab.builder.take() {
                builder.finalize();
            }
        }
    }
    BUILDER_BACKINGS.lock().unwrap().clear();
    FINISHED_FUNCS.lock().unwrap().clear();
    DECLARED_FUNCS.lock().unwrap().clear();
    SIGNATURES.lock().unwrap().clear();
    JIT_MODULES.lock().unwrap().clear();
    AOT_MODULES.lock().unwrap().clear();
}

// ============================================================================
// Type Constants
// ============================================================================

const CL_TYPE_I8: i64 = 1;
const CL_TYPE_I16: i64 = 2;
const CL_TYPE_I32: i64 = 3;
const CL_TYPE_I64: i64 = 4;
const CL_TYPE_F32: i64 = 5;
const CL_TYPE_F64: i64 = 6;
const CL_TYPE_B1: i64 = 7;
const CL_TYPE_PTR: i64 = 8;

const CL_TARGET_X86_64: i64 = 0;
const CL_TARGET_AARCH64: i64 = 1;
const CL_TARGET_RISCV64: i64 = 2;

const CL_CMP_EQ: i64 = 0;
const CL_CMP_NE: i64 = 1;
const CL_CMP_SLT: i64 = 2;
const CL_CMP_SLE: i64 = 3;
const CL_CMP_SGT: i64 = 4;
const CL_CMP_SGE: i64 = 5;
const CL_CMP_ULT: i64 = 6;
const CL_CMP_ULE: i64 = 7;
const CL_CMP_UGT: i64 = 8;
const CL_CMP_UGE: i64 = 9;

fn type_from_code(code: i64) -> types::Type {
    match code {
        CL_TYPE_I8 => types::I8,
        CL_TYPE_I16 => types::I16,
        CL_TYPE_I32 => types::I32,
        CL_TYPE_I64 => types::I64,
        CL_TYPE_F32 => types::F32,
        CL_TYPE_F64 => types::F64,
        CL_TYPE_B1 => types::I8,   // Booleans as i8
        CL_TYPE_PTR => types::I64, // Pointers as i64
        _ => types::I64,
    }
}

fn int_cc_from_code(code: i64) -> cranelift_codegen::ir::condcodes::IntCC {
    use cranelift_codegen::ir::condcodes::IntCC;
    match code {
        CL_CMP_EQ => IntCC::Equal,
        CL_CMP_NE => IntCC::NotEqual,
        CL_CMP_SLT => IntCC::SignedLessThan,
        CL_CMP_SLE => IntCC::SignedLessThanOrEqual,
        CL_CMP_SGT => IntCC::SignedGreaterThan,
        CL_CMP_SGE => IntCC::SignedGreaterThanOrEqual,
        CL_CMP_ULT => IntCC::UnsignedLessThan,
        CL_CMP_ULE => IntCC::UnsignedLessThanOrEqual,
        CL_CMP_UGT => IntCC::UnsignedGreaterThan,
        CL_CMP_UGE => IntCC::UnsignedGreaterThanOrEqual,
        _ => IntCC::Equal,
    }
}

fn float_cc_from_code(code: i64) -> cranelift_codegen::ir::condcodes::FloatCC {
    use cranelift_codegen::ir::condcodes::FloatCC;
    match code {
        0 => FloatCC::Equal,
        1 => FloatCC::NotEqual,
        2 => FloatCC::LessThan,
        3 => FloatCC::LessThanOrEqual,
        4 => FloatCC::GreaterThan,
        5 => FloatCC::GreaterThanOrEqual,
        _ => FloatCC::Equal,
    }
}

fn linkage_from_code(code: i64) -> Linkage {
    match code {
        0 => Linkage::Export,
        1 => Linkage::Import,
        2 => Linkage::Local,
        _ => Linkage::Import,
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

unsafe fn string_from_ptr(ptr: i64, len: i64) -> String {
    if ptr == 0 || len <= 0 {
        return String::new();
    }
    let slice = std::slice::from_raw_parts(ptr as *const u8, len as usize);
    String::from_utf8_lossy(slice).to_string()
}

/// Extract string from RuntimeValue
fn extract_string(val: RuntimeValue) -> Option<String> {
    let len = rt_string_len(val);
    if len <= 0 {
        return None;
    }
    let data = rt_string_data(val);
    if data.is_null() {
        return None;
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

fn build_isa_and_triple(target: i64) -> Option<(Triple, std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa>)> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").ok()?;
    flag_builder.set("is_pic", "true").ok()?;

    let triple = match target {
        CL_TARGET_X86_64 => "x86_64-unknown-linux-gnu"
            .parse::<Triple>()
            .unwrap_or_else(|_| Triple::host()),
        CL_TARGET_AARCH64 => "aarch64-unknown-linux-gnu"
            .parse::<Triple>()
            .unwrap_or_else(|_| Triple::host()),
        CL_TARGET_RISCV64 => "riscv64gc-unknown-linux-gnu"
            .parse::<Triple>()
            .unwrap_or_else(|_| Triple::host()),
        _ => Triple::host(),
    };

    let flags = settings::Flags::new(flag_builder);
    let isa_builder = cranelift_codegen::isa::lookup(triple.clone()).ok()?;
    let isa = isa_builder.finish(flags).ok()?;
    Some((triple, isa))
}

// ============================================================================
// Module Management FFI
// ============================================================================

/// Create a new JIT or AOT module (takes RuntimeValue for name).
#[no_mangle]
pub extern "C" fn rt_cranelift_module_new(name: RuntimeValue, target: i64) -> i64 {
    let name_str = match extract_string(name) {
        Some(s) => s,
        None => return 0,
    };
    unsafe { rt_cranelift_new_module_impl(&name_str, target) }
}

/// Create a new JIT module (low-level with raw pointers).
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_new_module(name_ptr: i64, name_len: i64, target: i64) -> i64 {
    let name = string_from_ptr(name_ptr, name_len);
    rt_cranelift_new_module_impl(&name, target)
}

unsafe fn rt_cranelift_new_module_impl(name: &str, target: i64) -> i64 {
    if name.is_empty() {
        return 0;
    }

    let (_, isa) = match build_isa_and_triple(target) {
        Some(v) => v,
        None => return 0,
    };

    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    let module = JITModule::new(builder);
    let handle = next_handle();

    JIT_MODULES.lock().unwrap().insert(handle, JITModuleContext {
        module,
        func_ids: HashMap::new(),
    });
    handle
}

/// Finalize the module after all functions are defined.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_finalize_module(module: i64) -> i64 {
    {
        let mut modules = JIT_MODULES.lock().unwrap();
        if let Some(ctx) = modules.get_mut(&module) {
            ctx.module.finalize_definitions().unwrap();
            return module;
        }
    }
    {
        let modules = AOT_MODULES.lock().unwrap();
        if modules.contains_key(&module) {
            return module;
        }
    }
    0
}

/// Free module resources.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_free_module(module: i64) {
    if JIT_MODULES.lock().unwrap().remove(&module).is_some() {
        return;
    }
    AOT_MODULES.lock().unwrap().remove(&module);
}

// ============================================================================
// Signature Building FFI
// ============================================================================

/// Create a new function signature.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_new_signature(call_conv: i64) -> i64 {
    let cc = match call_conv {
        0 => CallConv::SystemV,
        1 => CallConv::WindowsFastcall,
        2 => CallConv::Fast,
        _ => CallConv::SystemV,
    };
    let sig = Signature::new(cc);
    let handle = next_handle();
    SIGNATURES.lock().unwrap().insert(handle, sig);
    handle
}

/// Add a parameter to a signature.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_sig_add_param(sig: i64, type_: i64) {
    let mut sigs = SIGNATURES.lock().unwrap();
    if let Some(signature) = sigs.get_mut(&sig) {
        signature.params.push(AbiParam::new(type_from_code(type_)));
    }
}

/// Set the return type of a signature.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_sig_set_return(sig: i64, type_: i64) {
    let mut sigs = SIGNATURES.lock().unwrap();
    if let Some(signature) = sigs.get_mut(&sig) {
        signature.returns.clear();
        signature.returns.push(AbiParam::new(type_from_code(type_)));
    }
}

// ============================================================================
// Function Declaration FFI
// ============================================================================

/// Declare a function in a module (for forward references and imports).
/// linkage: 0=Export, 1=Import, 2=Local
/// Returns a function handle, or 0 on failure.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_declare_function(
    module: i64, name_ptr: i64, name_len: i64, sig: i64, linkage: i64,
) -> i64 {
    let name = string_from_ptr(name_ptr, name_len);
    if name.is_empty() {
        return 0;
    }

    let signature = {
        let sigs = SIGNATURES.lock().unwrap();
        match sigs.get(&sig) {
            Some(s) => s.clone(),
            None => return 0,
        }
    };

    let link = linkage_from_code(linkage);

    // Try JIT module first, then AOT
    let func_id = {
        let mut jit = JIT_MODULES.lock().unwrap();
        if let Some(mod_ctx) = jit.get_mut(&module) {
            mod_ctx.module.declare_function(&name, link, &signature).ok()
        } else {
            drop(jit);
            let mut aot = AOT_MODULES.lock().unwrap();
            if let Some(mod_ctx) = aot.get_mut(&module) {
                mod_ctx.module.declare_function(&name, link, &signature).ok()
            } else {
                None
            }
        }
    };

    match func_id {
        Some(id) => {
            let handle = next_handle();
            DECLARED_FUNCS.lock().unwrap().insert(handle, id);
            handle
        }
        None => 0,
    }
}

/// Import a declared function into the current function being built.
/// Returns a func_ref handle for use with call instructions, or 0 on failure.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_import_function(ctx: i64, func_handle: i64) -> i64 {
    let func_id = {
        let declared = DECLARED_FUNCS.lock().unwrap();
        match declared.get(&func_handle) {
            Some(&id) => id,
            None => return 0,
        }
    };

    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };

    let func_ref = if ab.is_jit {
        let mut modules = JIT_MODULES.lock().unwrap();
        let Some(mod_ctx) = modules.get_mut(&ab.module_handle) else { return 0 };
        mod_ctx.module.declare_func_in_func(func_id, &mut builder.func)
    } else {
        let mut modules = AOT_MODULES.lock().unwrap();
        let Some(mod_ctx) = modules.get_mut(&ab.module_handle) else { return 0 };
        mod_ctx.module.declare_func_in_func(func_id, &mut builder.func)
    };

    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.func_refs.insert(id, func_ref);
    id
}

// ============================================================================
// Function Building FFI
// ============================================================================

/// Begin building a function. Creates a FunctionBuilder for emitting instructions.
/// Returns function context handle, or 0 on failure.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_begin_function(
    module: i64, name_ptr: i64, name_len: i64, sig: i64,
) -> i64 {
    let name = string_from_ptr(name_ptr, name_len);
    if name.is_empty() {
        return 0;
    }

    let signature = {
        let sigs = SIGNATURES.lock().unwrap();
        match sigs.get(&sig) {
            Some(s) => s.clone(),
            None => return 0,
        }
    };

    // Determine if JIT or AOT module
    let is_jit = JIT_MODULES.lock().unwrap().contains_key(&module);
    let is_aot = AOT_MODULES.lock().unwrap().contains_key(&module);
    if !is_jit && !is_aot {
        return 0;
    }

    let handle = next_handle();

    // Create backing storage (Box'd for stable heap address)
    let mut backing = Box::new(BuilderBacking {
        ctx: Context::new(),
        func_builder_ctx: FunctionBuilderContext::new(),
    });

    // Set up function signature and name
    backing.ctx.func.signature = signature.clone();
    backing.ctx.func.name = cranelift_codegen::ir::UserFuncName::user(0, handle as u32);

    // Create FunctionBuilder with transmuted 'static lifetime.
    // SAFETY: backing is Box'd (stable heap address). The builder is always
    // finalized and dropped in end_function BEFORE the backing is freed.
    let builder = {
        let func_ptr: *mut Function = &mut backing.ctx.func;
        let fbc_ptr: *mut FunctionBuilderContext = &mut backing.func_builder_ctx;
        let builder = FunctionBuilder::new(&mut *func_ptr, &mut *fbc_ptr);
        std::mem::transmute::<FunctionBuilder<'_>, FunctionBuilder<'static>>(builder)
    };

    // Store backing and builder in separate registries
    BUILDER_BACKINGS.lock().unwrap().insert(handle, backing);
    ACTIVE_BUILDERS.lock().unwrap().insert(handle, ActiveBuilder {
        builder: Some(builder),
        blocks: HashMap::new(),
        values: HashMap::new(),
        stack_slots: HashMap::new(),
        func_refs: HashMap::new(),
        next_block_id: 1,
        next_value_id: 1,
        module_handle: module,
        is_jit,
        func_name: name,
    });

    handle
}

/// End building a function. Finalizes the builder and prepares for define_function.
/// Returns the context handle for use with define_function.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_end_function(ctx: i64) -> i64 {
    // Step 1: Finalize builder and extract metadata
    let (name, module_handle, is_jit) = {
        let mut active = ACTIVE_BUILDERS.lock().unwrap();
        let Some(ab) = active.get_mut(&ctx) else { return 0 };
        // Finalize the builder (consumes it, drops borrows into backing)
        if let Some(builder) = ab.builder.take() {
            builder.finalize();
        }
        (ab.func_name.clone(), ab.module_handle, ab.is_jit)
    };

    // Step 2: Move finished Context from backing to FINISHED_FUNCS
    {
        let mut backings = BUILDER_BACKINGS.lock().unwrap();
        if let Some(backing) = backings.remove(&ctx) {
            let backing = *backing; // Unbox
            FINISHED_FUNCS.lock().unwrap().insert(ctx, FinishedFunc {
                ctx: backing.ctx,
                name,
                module_handle,
                is_jit,
            });
        }
    }

    // Step 3: Remove active builder entry
    ACTIVE_BUILDERS.lock().unwrap().remove(&ctx);

    ctx
}

/// Define a function in a JIT module.
/// Returns true on success.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_define_function(
    module: i64, _func_id: i64, ctx: i64,
) -> bool {
    let finished = FINISHED_FUNCS.lock().unwrap().remove(&ctx);
    let Some(finished) = finished else { return false };

    let mut modules = JIT_MODULES.lock().unwrap();
    let Some(mod_ctx) = modules.get_mut(&module) else { return false };

    let func_id_result = mod_ctx.module.declare_function(
        &finished.name,
        Linkage::Export,
        &finished.ctx.func.signature,
    );

    match func_id_result {
        Ok(id) => {
            let mut ctx = finished.ctx;
            match mod_ctx.module.define_function(id, &mut ctx) {
                Ok(_) => {
                    mod_ctx.func_ids.insert(finished.name, id);
                    true
                }
                Err(e) => {
                    eprintln!("cranelift: define_function error: {}", e);
                    false
                }
            }
        }
        Err(e) => {
            eprintln!("cranelift: declare_function error: {}", e);
            false
        }
    }
}

// ============================================================================
// Block Management FFI
// ============================================================================

/// Create a new basic block.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_create_block(ctx: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };

    let block = builder.create_block();
    let block_id = ab.next_block_id;
    ab.next_block_id += 1;
    ab.blocks.insert(block_id, block);
    block_id
}

/// Switch to a basic block for instruction insertion.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_switch_to_block(ctx: i64, block: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let Some(&blk) = ab.blocks.get(&block) else { return };
    builder.switch_to_block(blk);
}

/// Seal a basic block (no more predecessors will be added).
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_seal_block(ctx: i64, block: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let Some(&blk) = ab.blocks.get(&block) else { return };
    builder.seal_block(blk);
}

/// Seal all blocks.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_seal_all_blocks(ctx: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    builder.seal_all_blocks();
}

// ============================================================================
// Value Creation FFI
// ============================================================================

/// Create an integer constant.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_iconst(ctx: i64, type_: i64, value: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };

    let ty = type_from_code(type_);
    let result = builder.ins().iconst(ty, value);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

/// Create a float constant.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_fconst(ctx: i64, type_: i64, value: f64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };

    let result = match type_ {
        CL_TYPE_F32 => builder.ins().f32const(value as f32),
        _ => builder.ins().f64const(value),
    };
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

/// Create a boolean constant.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_bconst(ctx: i64, value: bool) -> i64 {
    rt_cranelift_iconst(ctx, CL_TYPE_I8, if value { 1 } else { 0 })
}

/// Create a null pointer constant.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_null(ctx: i64, type_: i64) -> i64 {
    rt_cranelift_iconst(ctx, type_, 0)
}

// ============================================================================
// Arithmetic FFI
// ============================================================================

macro_rules! impl_binop {
    ($name:ident, $method:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(ctx: i64, a: i64, b: i64) -> i64 {
            let mut active = ACTIVE_BUILDERS.lock().unwrap();
            let Some(ab) = active.get_mut(&ctx) else { return 0 };
            let Some(builder) = ab.builder.as_mut() else { return 0 };
            let Some(&a_val) = ab.values.get(&a) else { return 0 };
            let Some(&b_val) = ab.values.get(&b) else { return 0 };
            let result = builder.ins().$method(a_val, b_val);
            let id = ab.next_value_id;
            ab.next_value_id += 1;
            ab.values.insert(id, result);
            id
        }
    };
}

impl_binop!(rt_cranelift_iadd, iadd);
impl_binop!(rt_cranelift_isub, isub);
impl_binop!(rt_cranelift_imul, imul);
impl_binop!(rt_cranelift_sdiv, sdiv);
impl_binop!(rt_cranelift_udiv, udiv);
impl_binop!(rt_cranelift_srem, srem);
impl_binop!(rt_cranelift_urem, urem);
impl_binop!(rt_cranelift_fadd, fadd);
impl_binop!(rt_cranelift_fsub, fsub);
impl_binop!(rt_cranelift_fmul, fmul);
impl_binop!(rt_cranelift_fdiv, fdiv);
impl_binop!(rt_cranelift_band, band);
impl_binop!(rt_cranelift_bor, bor);
impl_binop!(rt_cranelift_bxor, bxor);
impl_binop!(rt_cranelift_ishl, ishl);
impl_binop!(rt_cranelift_sshr, sshr);
impl_binop!(rt_cranelift_ushr, ushr);

/// Bitwise NOT (unary).
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_bnot(ctx: i64, a: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&a_val) = ab.values.get(&a) else { return 0 };
    let result = builder.ins().bnot(a_val);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

// ============================================================================
// Comparison FFI
// ============================================================================

/// Integer comparison.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_icmp(ctx: i64, cond: i64, a: i64, b: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&a_val) = ab.values.get(&a) else { return 0 };
    let Some(&b_val) = ab.values.get(&b) else { return 0 };

    let cc = int_cc_from_code(cond);
    let result = builder.ins().icmp(cc, a_val, b_val);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

/// Float comparison.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_fcmp(ctx: i64, cond: i64, a: i64, b: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&a_val) = ab.values.get(&a) else { return 0 };
    let Some(&b_val) = ab.values.get(&b) else { return 0 };

    let cc = float_cc_from_code(cond);
    let result = builder.ins().fcmp(cc, a_val, b_val);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

// ============================================================================
// Memory FFI
// ============================================================================

/// Load from memory.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_load(ctx: i64, type_: i64, addr: i64, offset: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&addr_val) = ab.values.get(&addr) else { return 0 };

    let ty = type_from_code(type_);
    let result = builder.ins().load(ty, MemFlags::new(), addr_val, offset as i32);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

/// Store to memory.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_store(ctx: i64, value: i64, addr: i64, offset: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let Some(&val) = ab.values.get(&value) else { return };
    let Some(&addr_val) = ab.values.get(&addr) else { return };

    builder.ins().store(MemFlags::new(), val, addr_val, offset as i32);
}

/// Allocate a stack slot.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_stack_slot(ctx: i64, size: i64, align: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };

    let slot_data = StackSlotData::new(StackSlotKind::ExplicitSlot, size as u32, align as u8);
    let slot = builder.func.create_sized_stack_slot(slot_data);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.stack_slots.insert(id, slot);
    id
}

/// Get address of a stack slot.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_stack_addr(ctx: i64, slot_handle: i64, offset: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&slot) = ab.stack_slots.get(&slot_handle) else { return 0 };

    let result = builder.ins().stack_addr(types::I64, slot, offset as i32);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

// ============================================================================
// Control Flow FFI
// ============================================================================

/// Unconditional jump.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_jump(ctx: i64, block: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let Some(&blk) = ab.blocks.get(&block) else { return };
    builder.ins().jump(blk, &[]);
}

/// Conditional branch.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_brif(
    ctx: i64, cond: i64, then_block: i64, else_block: i64,
) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let Some(&cond_val) = ab.values.get(&cond) else { return };
    let Some(&then_blk) = ab.blocks.get(&then_block) else { return };
    let Some(&else_blk) = ab.blocks.get(&else_block) else { return };
    builder.ins().brif(cond_val, then_blk, &[], else_blk, &[]);
}

/// Return with value.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_return(ctx: i64, value: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let Some(&val) = ab.values.get(&value) else { return };
    builder.ins().return_(&[val]);
}

/// Return void.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_return_void(ctx: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    builder.ins().return_(&[]);
}

/// Trap (unreachable).
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_trap(ctx: i64, code: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let trap_code = TrapCode::user(code as u8).unwrap_or(TrapCode::STACK_OVERFLOW);
    builder.ins().trap(trap_code);
}

// ============================================================================
// Function Call FFI
// ============================================================================

/// Direct function call via FuncRef handle (from import_function).
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_call(
    ctx: i64, func_ref_handle: i64, args_ptr: i64, args_len: i64,
) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&func_ref) = ab.func_refs.get(&func_ref_handle) else { return 0 };

    // Convert arg handles to Values
    let mut args = Vec::new();
    if args_ptr != 0 && args_len > 0 {
        let arg_handles = std::slice::from_raw_parts(args_ptr as *const i64, args_len as usize);
        for &h in arg_handles {
            let Some(&val) = ab.values.get(&h) else { return 0 };
            args.push(val);
        }
    }

    let inst = builder.ins().call(func_ref, &args);
    let results = builder.inst_results(inst);
    if results.is_empty() {
        0
    } else {
        let result = results[0];
        let id = ab.next_value_id;
        ab.next_value_id += 1;
        ab.values.insert(id, result);
        id
    }
}

/// Indirect function call through a pointer.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_call_indirect(
    ctx: i64, sig: i64, addr: i64, args_ptr: i64, args_len: i64,
) -> i64 {
    // Get signature first (separate lock)
    let signature = {
        let sigs = SIGNATURES.lock().unwrap();
        match sigs.get(&sig) {
            Some(s) => s.clone(),
            None => return 0,
        }
    };

    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&addr_val) = ab.values.get(&addr) else { return 0 };

    let sig_ref = builder.import_signature(signature);

    let mut args = Vec::new();
    if args_ptr != 0 && args_len > 0 {
        let arg_handles = std::slice::from_raw_parts(args_ptr as *const i64, args_len as usize);
        for &h in arg_handles {
            let Some(&val) = ab.values.get(&h) else { return 0 };
            args.push(val);
        }
    }

    let inst = builder.ins().call_indirect(sig_ref, addr_val, &args);
    let results = builder.inst_results(inst);
    if results.is_empty() {
        0
    } else {
        let result = results[0];
        let id = ab.next_value_id;
        ab.next_value_id += 1;
        ab.values.insert(id, result);
        id
    }
}

// ============================================================================
// Type Conversion FFI
// ============================================================================

macro_rules! impl_conv {
    ($name:ident, $method:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(ctx: i64, to_type: i64, value: i64) -> i64 {
            let mut active = ACTIVE_BUILDERS.lock().unwrap();
            let Some(ab) = active.get_mut(&ctx) else { return 0 };
            let Some(builder) = ab.builder.as_mut() else { return 0 };
            let Some(&val) = ab.values.get(&value) else { return 0 };
            let ty = type_from_code(to_type);
            let result = builder.ins().$method(ty, val);
            let id = ab.next_value_id;
            ab.next_value_id += 1;
            ab.values.insert(id, result);
            id
        }
    };
}

impl_conv!(rt_cranelift_sextend, sextend);
impl_conv!(rt_cranelift_uextend, uextend);
impl_conv!(rt_cranelift_ireduce, ireduce);
impl_conv!(rt_cranelift_fcvt_to_sint, fcvt_to_sint);
impl_conv!(rt_cranelift_fcvt_to_uint, fcvt_to_uint);
impl_conv!(rt_cranelift_fcvt_from_sint, fcvt_from_sint);
impl_conv!(rt_cranelift_fcvt_from_uint, fcvt_from_uint);

/// Bitcast (reinterpret bits).
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_bitcast(ctx: i64, to_type: i64, value: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&val) = ab.values.get(&value) else { return 0 };
    let ty = type_from_code(to_type);
    let result = builder.ins().bitcast(ty, MemFlags::new(), val);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, result);
    id
}

// ============================================================================
// Block Parameters FFI
// ============================================================================

/// Append a block parameter.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_append_block_param(
    ctx: i64, block: i64, type_: i64,
) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&blk) = ab.blocks.get(&block) else { return 0 };

    let ty = type_from_code(type_);
    let value = builder.func.dfg.append_block_param(blk, ty);
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, value);
    id
}

/// Get a block parameter value.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_block_param(ctx: i64, block: i64, index: i64) -> i64 {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return 0 };
    let Some(builder) = ab.builder.as_mut() else { return 0 };
    let Some(&blk) = ab.blocks.get(&block) else { return 0 };

    let params = builder.block_params(blk);
    if (index as usize) >= params.len() {
        return 0;
    }
    let value = params[index as usize];
    let id = ab.next_value_id;
    ab.next_value_id += 1;
    ab.values.insert(id, value);
    id
}

/// Append function parameters as block parameters to the entry block.
/// Convenience wrapper for append_block_params_for_function_params.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_append_func_params(ctx: i64, block: i64) {
    let mut active = ACTIVE_BUILDERS.lock().unwrap();
    let Some(ab) = active.get_mut(&ctx) else { return };
    let Some(builder) = ab.builder.as_mut() else { return };
    let Some(&blk) = ab.blocks.get(&block) else { return };
    builder.append_block_params_for_function_params(blk);
}

// ============================================================================
// JIT Execution FFI
// ============================================================================

/// Get a function pointer from a JIT module.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_get_function_ptr(
    module: i64, name_ptr: i64, name_len: i64,
) -> i64 {
    let name = string_from_ptr(name_ptr, name_len);
    if name.is_empty() {
        return 0;
    }

    let modules = JIT_MODULES.lock().unwrap();
    if let Some(ctx) = modules.get(&module) {
        if let Some(&func_id) = ctx.func_ids.get(&name) {
            ctx.module.get_finalized_function(func_id) as i64
        } else {
            0
        }
    } else {
        0
    }
}

/// Call a JIT function pointer.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_call_function_ptr(
    ptr: i64, _args_ptr: i64, _args_len: i64,
) -> i64 {
    if ptr == 0 {
        return 0;
    }
    // Simplified: assumes no-arg, i64-returning function
    let func: extern "C" fn() -> i64 = std::mem::transmute(ptr as *const ());
    func()
}

// ============================================================================
// Object File Generation FFI
// ============================================================================

/// Create a new AOT (Object) module for ahead-of-time compilation.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_new_aot_module(
    name_ptr: i64, name_len: i64, target: i64,
) -> i64 {
    let name = string_from_ptr(name_ptr, name_len);
    if name.is_empty() {
        return 0;
    }

    let (triple, isa) = match build_isa_and_triple(target) {
        Some(v) => v,
        None => return 0,
    };

    let builder = match ObjectBuilder::new(isa, name, cranelift_module::default_libcall_names()) {
        Ok(b) => b,
        Err(_) => return 0,
    };

    let module = ObjectModule::new(builder);
    let handle = next_handle();

    AOT_MODULES.lock().unwrap().insert(handle, ObjectModuleContext {
        module,
        func_ids: HashMap::new(),
    });
    handle
}

/// Emit an object file from an AOT module.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_emit_object(module: i64, path: RuntimeValue) -> bool {
    let path_str = match extract_string(path) {
        Some(s) => s,
        None => return false,
    };

    let mut aot_modules = AOT_MODULES.lock().unwrap();
    if let Some(ctx) = aot_modules.remove(&module) {
        let product = ctx.module.finish();
        let bytes = product.emit().unwrap_or_default();
        if bytes.is_empty() {
            return false;
        }
        match std::fs::write(&path_str, bytes) {
            Ok(_) => true,
            Err(_) => false,
        }
    } else {
        false
    }
}

/// Define a function in an AOT module.
#[no_mangle]
pub unsafe extern "C" fn rt_cranelift_aot_define_function(
    module: i64, name_ptr: i64, name_len: i64, ctx: i64,
) -> bool {
    let name = string_from_ptr(name_ptr, name_len);
    if name.is_empty() {
        return false;
    }

    let finished = FINISHED_FUNCS.lock().unwrap().remove(&ctx);
    let Some(finished) = finished else { return false };

    let mut modules = AOT_MODULES.lock().unwrap();
    let Some(mod_ctx) = modules.get_mut(&module) else { return false };

    let func_id_result = mod_ctx
        .module
        .declare_function(&name, Linkage::Export, &finished.ctx.func.signature);

    match func_id_result {
        Ok(id) => {
            let mut ctx = finished.ctx;
            match mod_ctx.module.define_function(id, &mut ctx) {
                Ok(_) => {
                    mod_ctx.func_ids.insert(name, id);
                    true
                }
                Err(e) => {
                    eprintln!("cranelift: AOT define_function error: {}", e);
                    false
                }
            }
        }
        Err(e) => {
            eprintln!("cranelift: AOT declare_function error: {}", e);
            false
        }
    }
}

// ============================================================================
// Module Registration
// ============================================================================

/// Register all Cranelift FFI functions with the JIT module.
/// Symbol names match the Simple `extern fn` declarations in src/lib/nogc_sync_mut/ffi/codegen.spl.
/// Some use `rt_` prefix (with Simple wrappers), some use bare `cranelift_` names (direct extern).
pub fn register_cranelift_ffi_functions(builder: &mut JITBuilder) {
    // Module management (rt_ prefix — have Simple wrappers)
    builder.symbol("rt_cranelift_new_module", rt_cranelift_new_module as *const u8);
    builder.symbol("rt_cranelift_new_aot_module", rt_cranelift_new_aot_module as *const u8);
    builder.symbol("rt_cranelift_finalize_module", rt_cranelift_finalize_module as *const u8);
    builder.symbol("cranelift_free_module", rt_cranelift_free_module as *const u8);

    // Signature building (bare names — direct extern in Simple)
    builder.symbol("cranelift_new_signature", rt_cranelift_new_signature as *const u8);
    builder.symbol("cranelift_sig_add_param", rt_cranelift_sig_add_param as *const u8);
    builder.symbol("cranelift_sig_set_return", rt_cranelift_sig_set_return as *const u8);

    // Function declaration (rt_ prefix — new functions with Simple wrappers)
    builder.symbol("rt_cranelift_declare_function", rt_cranelift_declare_function as *const u8);
    builder.symbol("rt_cranelift_import_function", rt_cranelift_import_function as *const u8);

    // Function building (rt_ prefix — Simple has wrapper for text→ptr/len)
    builder.symbol("rt_cranelift_begin_function", rt_cranelift_begin_function as *const u8);
    builder.symbol("cranelift_end_function", rt_cranelift_end_function as *const u8);
    builder.symbol("cranelift_define_function", rt_cranelift_define_function as *const u8);

    // Block management (bare names — direct extern in Simple)
    builder.symbol("cranelift_create_block", rt_cranelift_create_block as *const u8);
    builder.symbol("cranelift_switch_to_block", rt_cranelift_switch_to_block as *const u8);
    builder.symbol("cranelift_seal_block", rt_cranelift_seal_block as *const u8);
    builder.symbol("cranelift_seal_all_blocks", rt_cranelift_seal_all_blocks as *const u8);

    // Values (bare names except rt_cranelift_null)
    builder.symbol("cranelift_iconst", rt_cranelift_iconst as *const u8);
    builder.symbol("cranelift_fconst", rt_cranelift_fconst as *const u8);
    builder.symbol("cranelift_bconst", rt_cranelift_bconst as *const u8);
    builder.symbol("rt_cranelift_null", rt_cranelift_null as *const u8);

    // Integer arithmetic (bare names except rt_ prefixed ones)
    builder.symbol("cranelift_iadd", rt_cranelift_iadd as *const u8);
    builder.symbol("cranelift_isub", rt_cranelift_isub as *const u8);
    builder.symbol("cranelift_imul", rt_cranelift_imul as *const u8);
    builder.symbol("cranelift_sdiv", rt_cranelift_sdiv as *const u8);
    builder.symbol("rt_cranelift_udiv", rt_cranelift_udiv as *const u8);
    builder.symbol("cranelift_srem", rt_cranelift_srem as *const u8);
    builder.symbol("rt_cranelift_urem", rt_cranelift_urem as *const u8);

    // Float arithmetic (rt_ prefix — have Simple wrappers)
    builder.symbol("rt_cranelift_fadd", rt_cranelift_fadd as *const u8);
    builder.symbol("rt_cranelift_fsub", rt_cranelift_fsub as *const u8);
    builder.symbol("rt_cranelift_fmul", rt_cranelift_fmul as *const u8);
    builder.symbol("rt_cranelift_fdiv", rt_cranelift_fdiv as *const u8);

    // Bitwise (bare names except rt_cranelift_ushr)
    builder.symbol("cranelift_band", rt_cranelift_band as *const u8);
    builder.symbol("cranelift_bor", rt_cranelift_bor as *const u8);
    builder.symbol("cranelift_bxor", rt_cranelift_bxor as *const u8);
    builder.symbol("cranelift_bnot", rt_cranelift_bnot as *const u8);
    builder.symbol("cranelift_ishl", rt_cranelift_ishl as *const u8);
    builder.symbol("cranelift_sshr", rt_cranelift_sshr as *const u8);
    builder.symbol("rt_cranelift_ushr", rt_cranelift_ushr as *const u8);

    // Comparison (bare cranelift_icmp, rt_ for fcmp)
    builder.symbol("cranelift_icmp", rt_cranelift_icmp as *const u8);
    builder.symbol("rt_cranelift_fcmp", rt_cranelift_fcmp as *const u8);

    // Memory (bare names)
    builder.symbol("cranelift_load", rt_cranelift_load as *const u8);
    builder.symbol("cranelift_store", rt_cranelift_store as *const u8);
    builder.symbol("cranelift_stack_slot", rt_cranelift_stack_slot as *const u8);
    builder.symbol("cranelift_stack_addr", rt_cranelift_stack_addr as *const u8);

    // Control flow (bare jump/return/return_void, rt_ for brif/trap)
    builder.symbol("cranelift_jump", rt_cranelift_jump as *const u8);
    builder.symbol("rt_cranelift_brif", rt_cranelift_brif as *const u8);
    builder.symbol("cranelift_return", rt_cranelift_return as *const u8);
    builder.symbol("cranelift_return_void", rt_cranelift_return_void as *const u8);
    builder.symbol("rt_cranelift_trap", rt_cranelift_trap as *const u8);

    // Function calls (bare names)
    builder.symbol("cranelift_call", rt_cranelift_call as *const u8);
    builder.symbol("cranelift_call_indirect", rt_cranelift_call_indirect as *const u8);

    // Type conversion (rt_ prefix — have Simple wrappers)
    builder.symbol("rt_cranelift_sextend", rt_cranelift_sextend as *const u8);
    builder.symbol("rt_cranelift_uextend", rt_cranelift_uextend as *const u8);
    builder.symbol("rt_cranelift_ireduce", rt_cranelift_ireduce as *const u8);
    builder.symbol("rt_cranelift_fcvt_to_sint", rt_cranelift_fcvt_to_sint as *const u8);
    builder.symbol("rt_cranelift_fcvt_to_uint", rt_cranelift_fcvt_to_uint as *const u8);
    builder.symbol("rt_cranelift_fcvt_from_sint", rt_cranelift_fcvt_from_sint as *const u8);
    builder.symbol("rt_cranelift_fcvt_from_uint", rt_cranelift_fcvt_from_uint as *const u8);
    builder.symbol("cranelift_bitcast", rt_cranelift_bitcast as *const u8);

    // Block parameters (rt_ for append_block_param, bare for block_param)
    builder.symbol("rt_cranelift_append_block_param", rt_cranelift_append_block_param as *const u8);
    builder.symbol("cranelift_block_param", rt_cranelift_block_param as *const u8);
    builder.symbol("rt_cranelift_append_func_params", rt_cranelift_append_func_params as *const u8);

    // JIT execution (rt_ for get_function_ptr, bare for call_function_ptr)
    builder.symbol("rt_cranelift_get_function_ptr", rt_cranelift_get_function_ptr as *const u8);
    builder.symbol("cranelift_call_function_ptr", rt_cranelift_call_function_ptr as *const u8);

    // Object file generation / AOT compilation
    builder.symbol("rt_cranelift_emit_object", rt_cranelift_emit_object as *const u8);
    builder.symbol("rt_cranelift_aot_define_function", rt_cranelift_aot_define_function as *const u8);
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;

    #[test]
    fn test_create_and_free_module() {
        unsafe {
            let name = "test_module";
            let handle = rt_cranelift_new_module(
                name.as_ptr() as i64, name.len() as i64, CL_TARGET_X86_64,
            );
            assert!(handle > 0);
            rt_cranelift_free_module(handle);
        }
    }

    #[test]
    fn test_create_signature() {
        unsafe {
            let handle = rt_cranelift_new_signature(0);
            assert!(handle > 0);
            rt_cranelift_sig_add_param(handle, CL_TYPE_I64);
            rt_cranelift_sig_set_return(handle, CL_TYPE_I64);
        }
    }

    #[test]
    fn test_build_simple_function() {
        unsafe {
            // Create module
            let mod_name = "test_build";
            let module = rt_cranelift_new_module(
                mod_name.as_ptr() as i64, mod_name.len() as i64, CL_TARGET_X86_64,
            );
            assert!(module > 0);

            // Create signature: () -> i64
            let sig = rt_cranelift_new_signature(0); // SystemV
            rt_cranelift_sig_set_return(sig, CL_TYPE_I64);

            // Begin function
            let fname = "test_fn";
            let ctx = rt_cranelift_begin_function(
                module, fname.as_ptr() as i64, fname.len() as i64, sig,
            );
            assert!(ctx > 0);

            // Create entry block
            let entry = rt_cranelift_create_block(ctx);
            assert!(entry > 0);
            rt_cranelift_switch_to_block(ctx, entry);
            rt_cranelift_seal_block(ctx, entry);

            // Return constant 42
            let val = rt_cranelift_iconst(ctx, CL_TYPE_I64, 42);
            assert!(val > 0);
            rt_cranelift_return(ctx, val);

            // End and define
            let func_id = rt_cranelift_end_function(ctx);
            assert!(func_id > 0);
            let ok = rt_cranelift_define_function(module, func_id, ctx);
            assert!(ok);

            // Finalize module
            rt_cranelift_finalize_module(module);

            // Get function pointer and call it
            let fptr = rt_cranelift_get_function_ptr(
                module, fname.as_ptr() as i64, fname.len() as i64,
            );
            assert!(fptr != 0);
            let func: extern "C" fn() -> i64 = std::mem::transmute(fptr as *const ());
            assert_eq!(func(), 42);

            rt_cranelift_free_module(module);
        }
    }

    #[test]
    fn test_aot_module() {
        unsafe {
            let name = "test_aot";
            let handle = rt_cranelift_new_aot_module(
                name.as_ptr() as i64, name.len() as i64, CL_TARGET_X86_64,
            );
            assert!(handle > 0);
            rt_cranelift_free_module(handle);
        }
    }
}
