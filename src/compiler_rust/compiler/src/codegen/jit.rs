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
        register_compiler_owned_symbols(&mut builder);

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
        // Pre-compile guard against the broken JIT lambda/closure ABI.
        //
        // `compile_closure_create` builds a closure as a bare `rt_alloc` block
        // with the raw code address at offset 0, and `compile_indirect_call`
        // calls it as `fn(closure_ptr, raw_args...) -> raw_result`. Neither the
        // arguments nor the result are tag-boxed, and the block carries no
        // `HeapHeader`. Two consequences, both observed:
        //
        //  1. The result of a lambda call is consumed as a tagged
        //     `RuntimeValue`. A raw `i64` body result is therefore misread
        //     (`fn(x: i64) -> i64: x * 10` applied to 4 yields 40, printed as
        //     40 >> 3 == 5), and a raw `bool` result of 1 aliases `TAG_HEAP`
        //     with a NULL payload, so the first deref SIGSEGVs
        //     (`fn(x: i64) -> bool: x > 1` crashes with exit 139).
        //  2. Every runtime helper that accepts a closure
        //     (`rt_array_filter`, `rt_array_find`, `rt_option_map`, ...) calls
        //     `rt_closure_func_ptr`, which validates a `HeapObjectType::Closure`
        //     header. A JIT closure has none, so the helper either silently
        //     returns an empty/NIL result or walks unmapped memory.
        //
        // Repairing this needs a coordinated change to the JIT closure
        // representation (a real `rt_closure_new` object) plus boxing of lambda
        // parameters and results. Until then, fail the JIT compile so the
        // driver's interpreter fallback runs and produces correct answers,
        // matching the `first_unresolved_import` guard below.
        if let Some((name, why)) = Self::first_unsupported_lambda(mir) {
            return Err(BackendError::ModuleError(format!(
                "function '{name}' creates a lambda/closure the JIT closure ABI cannot \
                 compile ({why}); JIT would return wrong values or crash; \
                 deferring to interpreter"
            )));
        }

        // Guard for Defect 2 (named-fn-as-value silent miscompile), see
        // doc/08_tracking/bug/jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md.
        //
        // `emit_global_load`'s "static method reference" fallback
        // (cranelift_emitter.rs) treats any `GlobalLoad` whose name is not a
        // declared global variable as a function reference, and emits a bare
        // `func_addr` with no closure object, no `HeapHeader`, and no
        // tag-boxing. `compile_indirect_call` then unconditionally treats
        // that raw code address as a pointer to a closure struct and derefs
        // it, calling garbage. There is no fix at `compile_indirect_call`
        // alone (no provenance is carried through the vreg), so refuse the
        // whole module here, matching Defect 1's fallback shape, whenever a
        // `GlobalLoad` name resolves to a function rather than a global.
        if let Some(name) = Self::first_named_fn_value_load(mir) {
            return Err(BackendError::ModuleError(format!(
                "function '{name}' loads a named function as a callable value; the JIT \
                 closure ABI has no tag-boxed representation for a bare function pointer \
                 (compile_indirect_call would deref the raw code address as a closure struct \
                 and call garbage); deferring to interpreter"
            )));
        }

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
            // Make the de-JIT LOUD. A silent whole-module drop to the
            // interpreter is a proven catastrophic-cost defect class here: one
            // unresolvable name cost ~1000x (parse_html 3.56s -> 19.4ms,
            // compute_styles >10min -> 369ms once fixed, 365a643236b). Worse,
            // de-JITted code is *correct but slow*, so it silently hides real
            // miscompiles until someone makes it fast. Always emit a greppable
            // marker naming the symbol.
            eprintln!(
                "[jit-fallback] unresolved external symbol '{name}': \
                 whole module dropped to the interpreter (expect ~100-1000x slowdown). \
                 Set SIMPLE_JIT_STRICT=1 to turn this into a hard error."
            );
            // Opt-in hard failure for lanes that must never silently de-JIT.
            // Off by default so legitimate fallbacks (cross-module Simple
            // method symbols) keep working.
            if std::env::var_os("SIMPLE_JIT_STRICT").is_some_and(|v| v != "0") {
                return Err(BackendError::ModuleError(format!(
                    "SIMPLE_JIT_STRICT: unresolved external symbol '{name}' would NULL-jump in JIT; \
                     refusing to fall back to the interpreter"
                )));
            }
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

    /// Return the name of the first MIR function that builds a closure, if any.
    ///
    /// `MirInst::ClosureCreate` is emitted only for `HirExprKind::Lambda`
    /// (see `MirLowerer::lower_lambda_expr`); generators, futures and actors
    /// have their own instructions. See `compile_module` for why its presence
    /// disqualifies a module from JIT execution.
    fn first_lambda_function_impl(mir: &MirModule) -> Option<String> {
        Self::first_unsupported_lambda(mir).map(|(name, _)| name)
    }

    /// Return the first function whose lambda usage the closure ABI cannot
    /// compile, with the reason.
    ///
    /// # The two closure conventions
    ///
    /// A `ClosureCreate` result can be consumed in two incompatible ways:
    ///
    /// 1. **JIT-internal.** The closure is called back by an `IndirectCall` in
    ///    the same function. Both halves of that boundary are emitted by this
    ///    backend, so they only have to AGREE: `compile_indirect_call` builds
    ///    its signature from `param_types`/`return_type`, and the outlined
    ///    lambda declares the same types (`create_outlined_function` now takes
    ///    the lambda's real return type rather than hardcoding I64). Since
    ///    `mir::closure_call_types` fills those in from the `ClosureCreate`
    ///    itself, they agree by construction, and no tag-boxing is needed at
    ///    all — the values never leave JIT-compiled code.
    ///
    /// 2. **Runtime-facing.** The closure value is handed to something else —
    ///    passed as an argument (e.g. to `rt_array_map`), stored into a heap
    ///    object, or returned. Whoever calls it then goes through the runtime's
    ///    `RuntimeClosure` layout and its all-`RuntimeValue` convention, which
    ///    is NOT what `compile_closure_create` builds (a bare `rt_alloc` block
    ///    with a raw code address at offset 0) and NOT how the outlined body
    ///    reads its arguments. That mismatch returns wrong values or crashes.
    ///
    /// Only case 1 is admitted. Case 2 needs `rt_closure_new` allocation plus
    /// tag-boxed arguments/results/captures on both sides; it is recorded as
    /// the remaining blocker in
    /// `doc/08_tracking/bug/seed_jit_coverage_self_hosted_compiler_2026-08-21.md`.
    ///
    /// An `IndirectCall` still carrying `TypeId::ANY` is also refused: no value
    /// encoding at an untyped boundary can be right for both an i64 and an f64,
    /// which is the exact defect that reverted the previous attempt.
    fn first_unsupported_lambda(mir: &MirModule) -> Option<(String, String)> {
        use crate::mir::MirInst;

        for func in &mir.functions {
            // Registers holding a closure built in THIS function.
            let closure_regs = crate::mir::closure_call_types::closure_value_regs(func);
            if closure_regs.is_empty() {
                continue;
            }

            // A closure register may only be consumed as an `IndirectCall`
            // callee (case 1) or stored/loaded through a local — the shape a
            // `val f = \x: ...` binding lowers to, which
            // `mir::closure_call_types` already tracks. Every other use is
            // runtime-facing (case 2).
            // NOT filtered to the closure's own registers, and NOT filtered to
            // the non-body blocks. Once a module contains a lambda, ANY
            // indirect call in it may reach a closure — through a capture, a
            // struct field, a parameter, another module — and every such call
            // now boxes its arguments and unboxes its result. An `ANY`
            // boundary leaves that transport undefined in BOTH directions: the
            // nested `\y: inner(y) * 2` case answered 64 instead of 8 because
            // the callee's tagged result (4 << 3 == 32) was multiplied raw.
            for block in &func.blocks {
                for inst in &block.instructions {
                    // The only remaining refusal is a JIT-INTERNAL call whose
                    // boundary types are not carryable. Every runtime-FACING
                    // shape — passed as an argument, stored into a heap object,
                    // returned, captured by another closure — is now compiled:
                    // `compile_closure_create` builds a real
                    // `HeapObjectType::Closure` whose `func_ptr` is the lambda's
                    // boxed entry (codegen/closure_boxed_entry.rs), so any
                    // caller reaching it through `rt_closure_func_ptr` gets the
                    // all-`RuntimeValue` convention it expects.
                    // A closure HANDLE that reaches a scalar boxing
                    // instruction is being widened as if it were a number.
                    // `BoxInt` shifts it left by 3 whenever it cannot see a
                    // heap-shaped vreg type, which destroys the pointer; the
                    // later `rt_closure_func_ptr` then answers NULL and the
                    // indirect call jumps to 0. Measured: SIGSEGV on
                    // `fn mk() -> any: return \\x: x + 100`, where the `any`
                    // return slot inserts exactly this boxing. Refused and
                    // named rather than silently crashing.
                    if let MirInst::BoxInt { value, .. } | MirInst::BoxFloat { value, .. } = inst {
                        if closure_regs.contains(value) {
                            return Some((
                                func.name.clone(),
                                "the closure handle is scalar-boxed (an `any`-typed slot), which \
                                 shifts the pointer and corrupts it"
                                    .to_string(),
                            ));
                        }
                    }
                    if let MirInst::IndirectCall {
                        callee,
                        param_types,
                        return_type,
                        ..
                    } = inst
                    {
                        let _ = callee;
                        if !(crate::codegen::jit_closure_abi_supports(*return_type)
                                && param_types
                                    .iter()
                                    .all(|ty| crate::codegen::jit_closure_abi_supports(*ty)))
                        {
                            return Some((
                                func.name.clone(),
                                format!(
                                    "the call boundary types {param_types:?} -> {return_type:?} \
                                     are not carryable across the closure ABI (ANY means no \
                                     encoding is correct for both an integer and a float)"
                                ),
                            ));
                        }
                    }
                }
                // A closure handed back to the CALLER still has to survive the
                // return slot, and when that slot is typed `any` the MIR
                // lowering boxes it — `BoxInt` shifts a handle whose vreg type
                // it cannot see, corrupting the pointer, after which
                // `rt_closure_func_ptr` answers NULL and the indirect call
                // jumps to 0 (measured: SIGSEGV on `fn mk() -> any: return
                // \\x: x + 100`). The object convention is right; the boxing of
                // the HANDLE on the way out is not, so this one shape stays
                // refused and named.
                if let crate::mir::Terminator::Return(Some(reg)) = &block.terminator {
                    if closure_regs.contains(reg) {
                        return Some((
                            func.name.clone(),
                            "the closure is returned from the function, whose return slot boxes \
                             the handle and corrupts it"
                                .to_string(),
                        ));
                    }
                }
            }
        }
        None
    }

    /// Return the name of the first MIR function that loads a *named function*
    /// as a callable value (a `GlobalLoad` whose name is not a declared
    /// global variable — see `emit_global_load`'s "static method reference"
    /// fallback), if any. This is Defect 2 from
    /// doc/08_tracking/bug/jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md:
    /// unlike `ClosureCreate` (Defect 1, guarded above), this lowering path
    /// emits no closure object at all, just a bare function-pointer value,
    /// and currently sails through undetected into a miscompile.
    fn first_named_fn_value_load(mir: &MirModule) -> Option<String> {
        // `Node::Extern` handling (hir/lower/stmt_lowering.rs) inserts every
        // extern fn's name into `hir.globals` (with the function's RETURN
        // type, not a function-pointer type) specifically so the name is
        // loadable via `GlobalLoad` when referenced as a value — that insert
        // is what makes an extern fn nameable as a first-class value at all,
        // and it flows straight through into `mir.globals` unfiltered. That
        // means an extern fn's name is ALSO a `global_names` entry, so the
        // original `!global_names.contains(name) && func_names.contains(name)`
        // guard below always short-circuited false on `!global_names.contains`
        // for extern fn names, regardless of whether `func_names` also listed
        // them — the same closure-ABI miscompile this guard exists to catch
        // (see the defined-fn case docs) reached compile_indirect_call
        // silently for an extern fn name. Excluding extern fn names from the
        // "safe global" set routes them into the `func_names` check instead.
        let global_names: std::collections::HashSet<&str> = mir
            .globals
            .iter()
            .map(|(name, _, _)| name.as_str())
            .filter(|name| !mir.extern_fn_names.contains(*name))
            .collect();
        // A DEFINED function (non-extern, with a body) loaded as a value is
        // now JIT-able: `emit_boxed_fn_value_entries` gives it a `name$boxed`
        // thunk and `emit_global_load` wraps that in a zero-capture
        // `rt_closure_new`, so it is a real closure object. Only extern /
        // bodiless names still have no representation and keep the refusal.
        let func_names: std::collections::HashSet<&str> = mir
            .functions
            .iter()
            .filter(|f| f.blocks.is_empty())
            .map(|f| f.name.as_str())
            .chain(mir.extern_fn_names.iter().map(String::as_str))
            .collect();
        for func in &mir.functions {
            for block in &func.blocks {
                for inst in &block.instructions {
                    if let crate::mir::MirInst::GlobalLoad { global_name, .. } = inst {
                        let name = global_name.as_str();
                        if !global_names.contains(name) && func_names.contains(name) {
                            return Some(func.name.clone());
                        }
                    }
                }
            }
        }
        None
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

/// Runtime-ABI symbols whose bodies live in THIS crate rather than in
/// `simple-runtime`, and which therefore never appear in `RUNTIME_SYMBOL_NAMES`
/// (that list is generated from the runtime crate plus the C runtime sources).
///
/// Without this table the JIT has no way to reach them: the static provider does
/// not know them, and `dlsym(RTLD_DEFAULT)` misses because a Rust `bin` does not
/// put its `#[no_mangle]` symbols in the dynamic symbol table. The import would
/// be bound to a NULL GOT slot, so `first_unresolved_import` correctly refuses
/// and de-JITs the whole module — which is exactly what happened to stage1 on
/// `rt_native_build`.
///
/// Every entry here is a REAL function address. This is a registration of an
/// existing definition, never a stub: a stub that returned nil would be the
/// unbacked-extern defect class (see
/// `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`).
fn compiler_owned_symbol(name: &str) -> Option<*const u8> {
    match name {
        "rt_native_build" => Some(crate::native_build_sffi::rt_native_build as *const u8),
        _ => None,
    }
}

/// The names `compiler_owned_symbol` answers for. Kept beside it so a test can
/// assert the two agree and neither can silently empty out.
pub const COMPILER_OWNED_RUNTIME_SYMBOLS: &[&str] = &["rt_native_build"];

/// Publish [`COMPILER_OWNED_RUNTIME_SYMBOLS`] to a `JITBuilder`, mirroring what
/// `register_runtime_symbols_from_provider` does for the runtime-owned set.
fn register_compiler_owned_symbols(builder: &mut JITBuilder) {
    for &name in COMPILER_OWNED_RUNTIME_SYMBOLS {
        if let Some(ptr) = compiler_owned_symbol(name) {
            builder.symbol(name, ptr);
        }
    }
}

/// True if `name` is resolvable purely through the compiler-owned table.
/// Exposed so the regression gate can check the same predicate the JIT uses.
pub fn compiler_owned_symbol_resolves(name: &str) -> bool {
    compiler_owned_symbol(name).is_some()
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
    if compiler_owned_symbol(name).is_some() {
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
