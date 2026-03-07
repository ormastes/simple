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
use inkwell::targets::InitializationConfig;
use inkwell::OptimizationLevel;

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

        // Set up the LLVM backend for compilation
        let backend =
            LlvmBackend::new(simple_common::target::Target::host()).map_err(|e| format!("LLVM backend init: {}", e))?;

        // Initialize the backend's internal module and builder
        backend
            .create_module(module_name)
            .map_err(|e| format!("LLVM JIT create module: {}", e))?;

        // Forward-declare all function signatures via the backend
        for func in &mir.functions {
            let param_types: Vec<_> = func.params.iter().map(|p| p.ty).collect();
            backend
                .create_function_signature(&func.name, &param_types, &func.return_type)
                .map_err(|e| format!("LLVM JIT declare '{}': {}", func.name, e))?;
        }

        // Compile function bodies using the backend
        compile_functions_into_module(&backend, &mir.functions)?;

        // Take the module from the backend to create the JIT execution engine
        let module = backend.take_module()
            .ok_or_else(|| "LLVM JIT: failed to take module from backend".to_string())?;

        // Create JIT execution engine from the compiled module
        let ee = module
            .create_jit_execution_engine(OptimizationLevel::Default)
            .map_err(|e| format!("LLVM JIT engine: {}", e))?;

        // Collect function addresses
        for func in &mir.functions {
            if !func.blocks.is_empty() {
                if let Ok(addr) = ee.get_function_address(&func.name) {
                    if addr != 0 {
                        self.compiled_funcs.insert(func.name.clone(), addr as u64);
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

/// Compile function bodies using the backend's internal module.
///
/// This is a simplified compilation path. For full feature support,
/// functions are compiled through the LlvmBackend's emitter pipeline.
fn compile_functions_into_module(
    backend: &LlvmBackend,
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
