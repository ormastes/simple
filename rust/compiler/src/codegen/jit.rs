//! JIT (Just-In-Time) compilation using Cranelift with JITModule.
//!
//! This module provides JIT compilation for Simple functions, allowing
//! the interpreter to compile hot paths to native code at runtime.

use std::collections::HashMap;
use std::sync::Arc;

use cranelift_jit::{JITBuilder, JITModule};

use crate::mir::MirModule;

use super::common_backend::{create_isa_and_flags, BackendError, BackendResult, BackendSettings, CodegenBackend};

// Re-export error types for backwards compatibility
pub use super::common_backend::BackendError as JitError;
pub type JitResult<T> = BackendResult<T>;

// Re-export provider types for convenience
pub use simple_native_loader::{default_runtime_provider, static_provider, RuntimeLoadMode, RuntimeSymbolProvider};

/// JIT compiler for Simple functions.
///
/// Compiles MIR functions to native code that can be executed directly.
pub struct JitCompiler {
    backend: CodegenBackend<JITModule>,
    /// Map of function names to their native function pointers
    compiled_funcs: HashMap<String, *const u8>,
    /// Runtime symbol provider (kept alive for the lifetime of the compiler)
    #[allow(dead_code)]
    provider: Arc<dyn RuntimeSymbolProvider>,
}

// Safety: The compiled function pointers are only valid while JitCompiler is alive
// and we don't share them across threads without synchronization.
unsafe impl Send for JitCompiler {}

impl JitCompiler {
    /// Create a new JIT compiler with the default runtime provider.
    ///
    /// Uses `default_runtime_provider()` which:
    /// - In debug builds: tries dynamic loading first, falls back to static
    /// - In release builds: uses static linking
    pub fn new() -> JitResult<Self> {
        Self::with_provider(default_runtime_provider())
    }

    /// Create a new JIT compiler with a specific runtime symbol provider.
    ///
    /// This allows customizing how runtime FFI symbols are resolved:
    /// - `StaticSymbolProvider`: Zero-cost, compiled-in symbols
    /// - `DynamicSymbolProvider`: Load from shared library
    /// - `ChainedProvider`: Multiple libraries, first match wins
    pub fn with_provider(provider: Arc<dyn RuntimeSymbolProvider>) -> JitResult<Self> {
        let settings = BackendSettings::jit();
        let (_flags, isa) = create_isa_and_flags(&settings)?;

        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        // Register runtime FFI symbols from the provider
        register_runtime_symbols_from_provider(&mut builder, provider.as_ref());

        let module = JITModule::new(builder);
        let backend = CodegenBackend::with_module(module)?;

        Ok(Self {
            backend,
            compiled_funcs: HashMap::new(),
            provider,
        })
    }

    /// Create a new JIT compiler with static symbol resolution only.
    ///
    /// This is the most efficient option with zero runtime lookup cost.
    pub fn new_static() -> JitResult<Self> {
        Self::with_provider(static_provider())
    }

    /// Compile a MIR module and return function pointers.
    pub fn compile_module(&mut self, mir: &MirModule) -> JitResult<()> {
        // Compile all functions
        let functions = self.backend.compile_all_functions(mir)?;

        // Finalize all functions (make them executable)
        self.backend
            .module
            .finalize_definitions()
            .map_err(|e| BackendError::ModuleError(e.to_string()))?;

        // Store function pointers
        for func in &functions {
            if let Some(&func_id) = self.backend.func_ids.get(&func.name) {
                let ptr = self.backend.module.get_finalized_function(func_id);
                self.compiled_funcs.insert(func.name.clone(), ptr);
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
            .ok_or_else(|| BackendError::UnknownFunction(name.to_string()))?;

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
            .ok_or_else(|| BackendError::UnknownFunction(name.to_string()))?;

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
            .ok_or_else(|| BackendError::UnknownFunction(name.to_string()))?;

        let func: fn(i64, i64) -> i64 = std::mem::transmute(ptr);
        Ok(func(arg1, arg2))
    }
}

impl Default for JitCompiler {
    fn default() -> Self {
        Self::new().expect("Failed to create JIT compiler")
    }
}

/// Register runtime FFI function symbols with the JIT builder from a provider.
///
/// This allows the JIT to resolve external function calls to runtime FFI functions
/// like print, array operations, etc. The symbols are obtained from the provider,
/// which can be static (compiled-in) or dynamic (loaded from shared library).
fn register_runtime_symbols_from_provider(builder: &mut JITBuilder, provider: &dyn RuntimeSymbolProvider) {
    use simple_native_loader::RUNTIME_SYMBOL_NAMES;

    for &name in RUNTIME_SYMBOL_NAMES {
        if let Some(ptr) = provider.get_symbol(name) {
            builder.symbol(name, ptr);
        }
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
#[path = "jit_tests.rs"]
mod tests;
