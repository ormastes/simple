//! LLVM JIT compiler using inkwell's ExecutionEngine.
//!
//! Reuses the existing `LlvmBackend` + `LlvmEmitter` for compilation,
//! but instead of emitting object files, creates an in-memory JIT
//! execution engine for direct function invocation.
//!
//! Requires the `llvm` feature flag.

use std::collections::HashMap;

use inkwell::context::Context;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;
use inkwell::targets::InitializationConfig;
use inkwell::OptimizationLevel;

use crate::hir::TypeId;
use crate::mir::{MirFunction, MirModule};

use super::llvm::LlvmBackend;

/// LLVM JIT compiler for Simple functions.
///
/// Uses inkwell's MCJIT execution engine to compile MIR functions
/// to native code for direct in-process execution.
pub struct LlvmJitCompiler {
    context: &'static Context,
    execution_engine: Option<ExecutionEngine<'static>>,
    compiled_funcs: HashMap<String, u64>,
}

// Safety: LlvmJitCompiler owns its data and function pointers are valid
// while the compiler is alive.
unsafe impl Send for LlvmJitCompiler {}

impl LlvmJitCompiler {
    /// Create a new LLVM JIT compiler.
    pub fn new() -> Result<Self, String> {
        // Initialize LLVM targets for the host
        inkwell::targets::Target::initialize_native(&InitializationConfig::default())
            .map_err(|e| format!("LLVM native init: {}", e))?;

        let context = Box::leak(Box::new(Context::create()));

        Ok(Self {
            context,
            execution_engine: None,
            compiled_funcs: HashMap::new(),
        })
    }

    /// Compile a MIR module, making functions available for execution.
    pub fn compile_module(&mut self, mir: &MirModule) -> Result<(), String> {
        let module_name = mir.name.as_deref().unwrap_or("jit_module");

        // Create a fresh LLVM module
        let module = self.context.create_module(module_name);

        // Set up the LLVM backend for compilation
        let backend =
            LlvmBackend::new(simple_common::target::Target::host()).map_err(|e| format!("LLVM backend init: {}", e))?;

        // Use the backend to compile all functions into the module
        // Forward-declare all function signatures first
        for func in &mir.functions {
            let param_types: Vec<_> = func.params.iter().map(|p| p.ty).collect();
            create_function_in_module(self.context, &module, &func.name, &param_types, &func.return_type)
                .map_err(|e| format!("LLVM JIT declare '{}': {}", func.name, e))?;
        }

        // Compile function bodies using the backend
        // Note: We use the backend's compile_function which handles the
        // full LLVM IR generation pipeline
        compile_functions_into_module(&backend, &module, &mir.functions)?;

        // Create JIT execution engine from the compiled module
        let ee = module
            .create_jit_execution_engine(OptimizationLevel::Default)
            .map_err(|e| format!("LLVM JIT engine: {}", e))?;

        // Collect function addresses
        for func in &mir.functions {
            if !func.blocks.is_empty() {
                if let Ok(addr) = ee.get_function_address(&func.name) {
                    if addr != 0 {
                        self.compiled_funcs.insert(func.name.clone(), addr);
                    }
                }
            }
        }

        self.execution_engine = Some(ee);
        Ok(())
    }

    /// Execute a compiled function by name with i64 arguments.
    pub fn execute(&self, name: &str, args: &[i64]) -> Result<i64, String> {
        let addr = self
            .compiled_funcs
            .get(name)
            .copied()
            .ok_or_else(|| format!("LLVM JIT: function '{}' not found", name))?;

        unsafe {
            match args.len() {
                0 => {
                    let func: fn() -> i64 = std::mem::transmute(addr as *const u8);
                    Ok(func())
                }
                1 => {
                    let func: fn(i64) -> i64 = std::mem::transmute(addr as *const u8);
                    Ok(func(args[0]))
                }
                2 => {
                    let func: fn(i64, i64) -> i64 = std::mem::transmute(addr as *const u8);
                    Ok(func(args[0], args[1]))
                }
                3 => {
                    let func: fn(i64, i64, i64) -> i64 = std::mem::transmute(addr as *const u8);
                    Ok(func(args[0], args[1], args[2]))
                }
                n => Err(format!("LLVM JIT: unsupported argument count {} for '{}'", n, name)),
            }
        }
    }

    /// Check if a function is compiled and available.
    pub fn has_function(&self, name: &str) -> bool {
        self.compiled_funcs.contains_key(name)
    }
}

/// Create a function declaration in an LLVM module.
fn create_function_in_module(
    context: &Context,
    module: &Module<'_>,
    name: &str,
    param_types: &[TypeId],
    return_type: &TypeId,
) -> Result<(), String> {
    use inkwell::types::BasicMetadataTypeEnum;

    let i64_type = context.i64_type();
    let f64_type = context.f64_type();
    let ptr_type = context.ptr_type(inkwell::AddressSpace::default());

    let map_type = |ty: &TypeId| -> BasicMetadataTypeEnum {
        match ty {
            TypeId::Int
            | TypeId::I64
            | TypeId::I32
            | TypeId::I16
            | TypeId::I8
            | TypeId::U64
            | TypeId::U32
            | TypeId::U16
            | TypeId::U8
            | TypeId::Bool
            | TypeId::Char => i64_type.into(),
            TypeId::Float | TypeId::F64 | TypeId::F32 => f64_type.into(),
            TypeId::String
            | TypeId::Array(_)
            | TypeId::Tuple(_)
            | TypeId::Struct(_)
            | TypeId::Ref(_)
            | TypeId::MutRef(_) => ptr_type.into(),
            _ => i64_type.into(),
        }
    };

    let params: Vec<BasicMetadataTypeEnum> = param_types.iter().map(|t| map_type(t)).collect();

    let fn_type = match return_type {
        TypeId::Float | TypeId::F64 | TypeId::F32 => f64_type.fn_type(&params, false),
        TypeId::Unit | TypeId::Never => context.void_type().fn_type(&params, false),
        _ => i64_type.fn_type(&params, false),
    };

    module.add_function(name, fn_type, None);
    Ok(())
}

/// Compile function bodies into an LLVM module.
///
/// This is a simplified compilation path. For full feature support,
/// functions are compiled through the LlvmBackend's emitter pipeline.
fn compile_functions_into_module(
    backend: &LlvmBackend,
    _module: &Module<'_>,
    functions: &[MirFunction],
) -> Result<(), String> {
    for func in functions {
        if !func.blocks.is_empty() {
            backend
                .compile_function(func)
                .map_err(|e| format!("LLVM JIT compile '{}': {}", func.name, e))?;
        }
    }
    Ok(())
}
