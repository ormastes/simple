//! JIT (Just-In-Time) compilation using Cranelift with JITModule.
//!
//! This module provides JIT compilation for Simple functions, allowing
//! the interpreter to compile hot paths to native code at runtime.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
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
    /// Runtime symbol provider (kept alive for the lifetime of the compiler;
    /// also queried by `first_unresolved_import` to detect NULL-jump imports).
    provider: Arc<dyn RuntimeSymbolProvider>,
    /// Heap-backed global initialization runs once before the first JIT entry call.
    module_init_ran: AtomicBool,
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
    /// This allows customizing how runtime SFFI symbols are resolved:
    /// - `StaticSymbolProvider`: Zero-cost, compiled-in symbols
    /// - `DynamicSymbolProvider`: Load from shared library
    /// - `ChainedProvider`: Multiple libraries, first match wins
    pub fn with_provider(provider: Arc<dyn RuntimeSymbolProvider>) -> JitResult<Self> {
        let settings = BackendSettings::jit();
        let (_flags, isa) = create_isa_and_flags(&settings)?;

        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        // Register runtime SFFI symbols from the provider
        register_runtime_symbols_from_provider(&mut builder, provider.as_ref());

        let module = JITModule::new(builder);
        let backend = CodegenBackend::with_module(module)?;

        Ok(Self {
            backend,
            compiled_funcs: HashMap::new(),
            provider,
            module_init_ran: AtomicBool::new(false),
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

        // Pre-finalize guard against NULL-jump crashes.
        //
        // cranelift-jit fills the GOT slot of an undefined `Linkage::Import`
        // with `lookup_symbol(name).unwrap_or(std::ptr::null())`
        // (vendor/cranelift-jit/src/backend.rs `declare_function`). An import
        // that resolves to neither a registered runtime symbol nor a dlsym
        // entry therefore finalizes to a NULL slot and SIGSEGVs when called.
        // This happens for cross-module Simple method symbols (e.g.
        // `Type_dot_new`) pulled in by a non-flattening `use` import: AOT
        // reports these as a clean "undefined symbol" relocation error, but
        // JIT would crash. Detect them here and fail the JIT compile so the
        // driver's interpreter fallback runs instead (matching AOT behaviour).
        if let Some(name) = self.first_unresolved_import() {
            return Err(BackendError::ModuleError(format!(
                "unresolved external symbol '{name}' would NULL-jump in JIT; deferring to interpreter"
            )));
        }

        // Finalize all functions (make them executable)
        self.backend
            .module
            .finalize_definitions()
            .map_err(|e| BackendError::ModuleError(e.to_string()))?;

        // Store function pointers
        for func in &functions {
            if let Some(&func_id) = self.backend.func_ids.get(&func.name) {
                let ptr = self.backend.module.get_finalized_function(func_id);
                if std::env::var("SIMPLE_JIT_TRACE_ADDR").is_ok() {
                    eprintln!("[jit-addr] {} {:p}", func.name, ptr);
                }
                self.compiled_funcs.insert(func.name.clone(), ptr);
            }
        }
        if let Some(&func_id) = self.backend.func_ids.get("__module_init") {
            let ptr = self.backend.module.get_finalized_function(func_id);
            if std::env::var("SIMPLE_JIT_TRACE_ADDR").is_ok() {
                eprintln!("[jit-addr] __module_init {:p}", ptr);
            }
            self.compiled_funcs.insert("__module_init".to_string(), ptr);
            self.module_init_ran.store(false, Ordering::SeqCst);
        }

        Ok(())
    }

    /// Return the name of a declared `Linkage::Import` function that will not
    /// resolve to a real address at finalize time, if any.
    ///
    /// Mirrors cranelift-jit's own `lookup_symbol` (registered runtime symbols
    /// plus a `dlsym(RTLD_DEFAULT)` fallback). Any import for which both miss
    /// would be bound to a NULL GOT slot; see `compile_module`.
    fn first_unresolved_import(&self) -> Option<String> {
        use cranelift_module::{Linkage, Module};
        for (_id, decl) in self.backend.module.declarations().get_functions() {
            if decl.linkage != Linkage::Import {
                continue;
            }
            if let Some(name) = decl.name.as_deref() {
                if !jit_import_resolves(self.provider.as_ref(), name) {
                    return Some(name.to_string());
                }
            }
        }
        None
    }

    /// Get the native function pointer for a compiled function.
    ///
    /// # Safety
    /// The caller must ensure the function signature matches the expected type.
    pub fn get_function_ptr(&self, name: &str) -> Option<*const u8> {
        self.compiled_funcs.get(name).copied()
    }

    unsafe fn run_module_init_once(&self) -> JitResult<()> {
        if self.module_init_ran.load(Ordering::SeqCst) {
            return Ok(());
        }
        let Some(ptr) = self.get_function_ptr("__module_init") else {
            self.module_init_ran.store(true, Ordering::SeqCst);
            return Ok(());
        };
        if self
            .module_init_ran
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            let init: fn() = std::mem::transmute(ptr);
            init();
        }
        Ok(())
    }

    /// Call a compiled function that takes no arguments and returns i64.
    ///
    /// # Safety
    /// The function must have been compiled with the correct signature.
    pub unsafe fn call_i64_void(&self, name: &str) -> JitResult<i64> {
        if name != "__module_init" {
            self.run_module_init_once()?;
        }
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
        self.run_module_init_once()?;
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
        self.run_module_init_once()?;
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

/// Register runtime SFFI function symbols with the JIT builder from a provider.
///
/// This allows the JIT to resolve external function calls to runtime SFFI functions
/// like print, array operations, etc. The symbols are obtained from the provider,
/// which can be static (compiled-in) or dynamic (loaded from shared library).
fn register_runtime_symbols_from_provider(builder: &mut JITBuilder, provider: &dyn RuntimeSymbolProvider) {
    use simple_native_loader::RUNTIME_SYMBOL_NAMES;

    for &name in RUNTIME_SYMBOL_NAMES {
        if let Some(ptr) = provider.get_symbol(name) {
            builder.symbol(name, ptr);
        } else if let Some(addr) = crate::elf_utils::resolve_runtime_symbol(name) {
            builder.symbol(name, addr as *const u8);
        }
    }
}

/// True if a `Linkage::Import` symbol named `name` will resolve to a real
/// address at JIT finalize time — i.e. it is a registered runtime symbol or is
/// `dlsym`-resolvable in the current process. This is exactly the resolution
/// cranelift-jit performs in `lookup_symbol` (registered symbols, then
/// `lookup_with_dlsym`); an import resolving to neither is bound to a NULL GOT
/// slot and would SIGSEGV when called.
fn jit_import_resolves(provider: &dyn RuntimeSymbolProvider, name: &str) -> bool {
    if provider.get_symbol(name).is_some() {
        return true;
    }
    if crate::elf_utils::resolve_runtime_symbol(name).is_some() {
        return true;
    }
    dlsym_resolves(name)
}

#[cfg(not(windows))]
fn dlsym_resolves(name: &str) -> bool {
    let Ok(c_name) = std::ffi::CString::new(name) else {
        return false;
    };
    // SAFETY: `dlsym(RTLD_DEFAULT, ..)` with a valid C string; this is the same
    // call cranelift-jit's `lookup_with_dlsym` makes to resolve the symbol.
    let sym = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_name.as_ptr()) };
    !sym.is_null()
}

#[cfg(windows)]
fn dlsym_resolves(_name: &str) -> bool {
    // Conservative on Windows: assume resolvable so the guard never forces an
    // unnecessary interpreter fallback. The cross-module NULL-jump this guards
    // is observed on the System V/ELF JIT path; Windows uses a different
    // (GetProcAddress-based) resolver and is out of scope for this guard.
    true
}

#[cfg(all(test, target_arch = "x86_64"))]
#[path = "jit_tests.rs"]
mod tests;
