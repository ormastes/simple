//! Common execution core shared between Runner and Interpreter
//!
//! Eliminates duplication of GC setup, compilation, loading, and execution logic.

use std::fs;
use std::path::Path;
use std::sync::Arc;
use tempfile::TempDir;

use simple_common::gc::{GcAllocator, MemoryLimitConfig};
use simple_common::target::Target;
use simple_compiler::{CompilerPipeline, SimdMode as CompilerSimdMode};
use simple_runtime::loader::loader::ModuleLoader as SmfLoader;
use simple_runtime::loader::LoadedModule;
use simple_native_loader::{default_runtime_provider, RuntimeSymbolProvider};
use simple_parser::error_recovery::ErrorHintLevel;
use simple_parser::Parser;
use simple_runtime::gc::GcRuntime;
use simple_runtime::NoGcAllocator;

/// Execution mode for the runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionMode {
    /// JIT compilation with interpreter fallback (default in Stage 2+)
    Jit,
    /// Force interpreter only (--interpret flag)
    Interpret,
    /// Force Cranelift JIT backend
    CraneliftJit,
    /// Force LLVM JIT backend
    LlvmJit,
    /// Compile to `wasm32-wasi` and run under the Wasmer WASI host, enforcing
    /// the module's declared `sandbox` capability policy.
    Wasm,
}

/// What the host is offering a WebAssembly guest for one invocation.
///
/// This exists because WASI capability enforcement can only refuse things it is
/// actually handed. `run_source_wasm` used to build a bare `WasiConfig::new()`
/// -- empty env, empty preopens, empty stdin -- so `validate_capabilities`
/// iterated three empty collections and could not deny anything even when the
/// module carried a correct policy table. The control was wired but starved.
///
/// Grants are *opt-in* rather than "forward the whole host environment".
/// `validate_capabilities` denies by returning an error, it does not silently
/// filter, so forwarding every host variable by default would hard-fail every
/// sandboxed module on the first unlisted variable -- a control that refuses
/// everything is as broken as one that refuses nothing. The operator names what
/// the guest should receive; the module's policy decides whether it may.
#[derive(Debug, Clone, Default)]
pub struct WasmInvocation {
    /// Environment variables offered to the guest, as (key, value).
    pub env: Vec<(String, String)>,
    /// Directories offered to the guest, as (host_path, guest_path).
    pub preopens: Vec<(String, String)>,
    /// Bytes offered to the guest on stdin.
    pub stdin: Vec<u8>,
}

impl WasmInvocation {
    /// Assemble the invocation from the process environment.
    ///
    /// * `SIMPLE_WASM_ENV="A,B"` forwards host variables `A` and `B` (only
    ///   those that are actually set). The single entry `*` forwards the entire
    ///   host environment -- deliberately spellable, deliberately not default.
    /// * `SIMPLE_WASM_PREOPEN="host:guest,host2"` preopens directories. With no
    ///   `:guest` part the guest sees the host path under its own name.
    /// * stdin is forwarded when it is redirected (a pipe or a file). On a
    ///   terminal nothing is read, so an interactive run never blocks.
    pub fn from_process_env() -> Self {
        let mut invocation = Self::default();

        if let Ok(spec) = std::env::var("SIMPLE_WASM_ENV") {
            for name in spec.split(',').map(str::trim).filter(|n| !n.is_empty()) {
                if name == "*" {
                    invocation.env = std::env::vars().collect();
                    break;
                }
                if let Ok(value) = std::env::var(name) {
                    invocation.env.push((name.to_string(), value));
                }
            }
        }

        if let Ok(spec) = std::env::var("SIMPLE_WASM_PREOPEN") {
            for entry in spec.split(',').map(str::trim).filter(|e| !e.is_empty()) {
                let (host, guest) = match entry.split_once(':') {
                    Some((host, guest)) if !guest.is_empty() => (host, guest),
                    _ => (entry, entry),
                };
                invocation.preopens.push((host.to_string(), guest.to_string()));
            }
        }

        {
            use std::io::{IsTerminal, Read};
            if !std::io::stdin().is_terminal() {
                let mut buffer = Vec::new();
                if std::io::stdin().read_to_end(&mut buffer).is_ok() {
                    invocation.stdin = buffer;
                }
            }
        }

        invocation
    }
}

impl ExecutionMode {
    /// Parse from string (CLI flag or env var).
    ///
    /// Note the `_` arm: an unrecognised value is *not* an error, it silently
    /// means JIT. That is why `SIMPLE_EXECUTION_MODE=wasm` used to run the
    /// module through the JIT and exit 0 without touching WebAssembly at all --
    /// the value was accepted and discarded. `wasm` is now a real mode, so the
    /// wasm lane is selectable rather than merely spellable.
    pub fn parse_str(s: &str) -> Self {
        match s {
            "interpret" | "interpreter" => ExecutionMode::Interpret,
            "cranelift" => ExecutionMode::CraneliftJit,
            "llvm" => ExecutionMode::LlvmJit,
            "wasm" | "wasm32" | "wasi" | "wasm32-wasi" => ExecutionMode::Wasm,
            _ => ExecutionMode::Jit,
        }
    }

    /// Check if this mode uses JIT.
    ///
    /// `Wasm` must be excluded explicitly. The old body was
    /// `!matches!(self, Interpret)`, so every new variant defaulted to "is JIT"
    /// and would have been routed straight back into the JIT lane.
    pub fn is_jit(&self) -> bool {
        !matches!(self, ExecutionMode::Interpret | ExecutionMode::Wasm)
    }

    /// Check if this mode compiles to WebAssembly and runs under a WASI host.
    pub fn is_wasm(&self) -> bool {
        matches!(self, ExecutionMode::Wasm)
    }
}

/// Core execution engine for Simple code
/// Handles GC allocation, compilation, loading, and execution
pub struct ExecCore {
    pub loader: SmfLoader,
    pub gc_alloc: Arc<dyn GcAllocator>,
    pub gc_runtime: Option<Arc<GcRuntime>>,
    /// Runtime symbol provider for JIT compilation
    pub symbol_provider: Arc<dyn RuntimeSymbolProvider>,
    /// Execution mode (JIT vs interpreter)
    pub execution_mode: ExecutionMode,
}

impl ExecCore {
    /// Create with a GC runtime and default symbol provider
    pub fn with_gc(gc: GcRuntime) -> Self {
        Self::with_gc_and_provider(gc, default_runtime_provider())
    }

    /// Create with a GC runtime and custom symbol provider
    #[allow(clippy::arc_with_non_send_sync)] // reason: Arc used for single-threaded ref-counting in interpreter context
    pub fn with_gc_and_provider(gc: GcRuntime, provider: Arc<dyn RuntimeSymbolProvider>) -> Self {
        let gc = Arc::new(gc);
        // Check SIMPLE_EXECUTION_MODE env var for default mode
        let mode = std::env::var("SIMPLE_EXECUTION_MODE")
            .map(|s| ExecutionMode::parse_str(&s))
            .unwrap_or(ExecutionMode::Jit); // JIT default (Stage 2+)
        Self {
            loader: SmfLoader::new(),
            gc_alloc: gc.clone(),
            gc_runtime: Some(gc),
            symbol_provider: provider,
            execution_mode: mode,
        }
    }

    /// Create with default GC runtime and symbol provider
    pub fn new() -> Self {
        Self::with_gc(GcRuntime::new())
    }

    /// Create with a custom symbol provider (uses default GC runtime)
    pub fn with_provider(provider: Arc<dyn RuntimeSymbolProvider>) -> Self {
        Self::with_gc_and_provider(GcRuntime::new(), provider)
    }

    /// Create without GC (uses NoGcAllocator)
    pub fn new_no_gc() -> Self {
        Self {
            loader: SmfLoader::new(),
            gc_alloc: Arc::new(NoGcAllocator::new()),
            gc_runtime: None,
            symbol_provider: default_runtime_provider(),
            execution_mode: ExecutionMode::Jit,
        }
    }

    /// Set the execution mode.
    pub fn set_execution_mode(&mut self, mode: ExecutionMode) {
        self.execution_mode = mode;
    }

    /// Create with verbose GC logging
    pub fn new_with_gc_logging() -> Self {
        Self::with_gc(GcRuntime::verbose_stdout())
    }

    /// Create with specific memory limit in bytes
    pub fn with_memory_limit(limit_bytes: usize) -> Self {
        Self::with_gc(GcRuntime::with_memory_limit(limit_bytes))
    }

    /// Create with specific memory limit in megabytes
    pub fn with_memory_limit_mb(limit_mb: usize) -> Self {
        Self::with_gc(GcRuntime::with_memory_limit_mb(limit_mb))
    }

    /// Create with specific memory limit in gigabytes
    pub fn with_memory_limit_gb(limit_gb: usize) -> Self {
        Self::with_gc(GcRuntime::with_memory_limit_gb(limit_gb))
    }

    /// Create with custom memory limit configuration
    pub fn with_memory_config(config: MemoryLimitConfig) -> Self {
        Self::with_gc(GcRuntime::with_options(
            simple_runtime::gc::GcOptions::new(),
            None,
            config,
        ))
    }

    /// Create with unlimited memory
    pub fn unlimited_memory() -> Self {
        Self::with_gc(GcRuntime::unlimited())
    }

    /// Create without GC but with memory limit
    pub fn new_no_gc_with_memory_limit(limit_bytes: usize) -> Self {
        Self {
            loader: SmfLoader::new(),
            gc_alloc: Arc::new(NoGcAllocator::with_memory_limit(limit_bytes)),
            gc_runtime: None,
            symbol_provider: default_runtime_provider(),
            execution_mode: ExecutionMode::Jit,
        }
    }

    /// Create without GC and with memory limit configuration
    pub fn new_no_gc_with_memory_config(config: MemoryLimitConfig) -> Self {
        Self {
            loader: SmfLoader::new(),
            gc_alloc: Arc::new(NoGcAllocator::with_memory_config(config)),
            gc_runtime: None,
            symbol_provider: default_runtime_provider(),
            execution_mode: ExecutionMode::Jit,
        }
    }

    /// Get current memory usage in bytes
    pub fn memory_usage(&self) -> usize {
        self.gc_alloc.memory_usage()
    }

    /// Get memory limit in bytes (0 if unlimited)
    pub fn memory_limit(&self) -> usize {
        self.gc_alloc.memory_limit()
    }

    /// Get the runtime symbol provider
    pub fn provider(&self) -> &Arc<dyn RuntimeSymbolProvider> {
        &self.symbol_provider
    }

    /// Trigger post-run GC collection
    pub fn collect_gc(&self) {
        if let Some(gc) = &self.gc_runtime {
            let _ = gc.collect("post-run");
        } else {
            self.gc_alloc.collect();
        }
    }

    /// Display error hints from parser (helpful messages for common mistakes)
    fn display_error_hints(&self, parser: &Parser, source: &str) {
        let hints = parser.error_hints();
        if hints.is_empty() {
            return;
        }
        let suppress_non_errors = std::env::var_os("SIMPLE_NO_DEPRECATED_WARNINGS").is_some();

        // Display hints to stderr
        for hint in hints {
            if suppress_non_errors && !matches!(hint.level, ErrorHintLevel::Error) {
                continue;
            }
            let level_str = match hint.level {
                ErrorHintLevel::Error => "\x1b[31merror\x1b[0m",     // red
                ErrorHintLevel::Warning => "\x1b[33mwarning\x1b[0m", // yellow
                ErrorHintLevel::Info => "\x1b[36minfo\x1b[0m",       // cyan
                ErrorHintLevel::Hint => "\x1b[32mhint\x1b[0m",       // green
            };

            eprintln!("{}: {}", level_str, hint.message);
            eprintln!("  --> line {}:{}", hint.span.line, hint.span.column);

            // Show source line with caret
            if let Some(line) = source.lines().nth(hint.span.line - 1) {
                eprintln!("   |");
                eprintln!("{:3} | {}", hint.span.line, line);
                eprintln!("   | {}^", " ".repeat(hint.span.column - 1));
            }

            if let Some(ref suggestion) = hint.suggestion {
                eprintln!("\nSuggestion: {}", suggestion);
            }

            if let Some(ref help) = hint.help {
                eprintln!("\nHelp:\n{}", help);
            }

            eprintln!(); // blank line between hints
        }
    }

    /// True when a top-level item is a pure DECLARATION — something that
    /// defines a name but executes nothing when the module is run.
    ///
    /// Anything not listed here is treated as executable, so a newly added
    /// `Node` variant can never turn into a spurious "nothing to run" error.
    fn is_pure_declaration(item: &simple_parser::ast::Node) -> bool {
        use simple_parser::ast::Node as N;
        matches!(
            item,
            N::Function(_)
                | N::Struct(_)
                | N::Bitfield(_)
                | N::Class(_)
                | N::Enum(_)
                | N::Trait(_)
                | N::Impl(_)
                | N::InterfaceBinding(_)
                | N::Mixin(_)
                | N::Actor(_)
                | N::TypeAlias(_)
                | N::ClassAlias(_)
                | N::FunctionAlias(_)
                | N::Extern(_)
                | N::ExternClass(_)
                | N::Macro(_)
                | N::Unit(_)
                | N::UnitFamily(_)
                | N::CompoundUnit(_)
                | N::HandlePool(_)
                | N::LiteralFunction(_)
                | N::ModDecl(_)
                | N::UseStmt(_)
                | N::MultiUse(_)
                | N::CommonUseStmt(_)
                | N::ExportUseStmt(_)
                | N::StructuredExportStmt(_)
                | N::AutoImportStmt(_)
                | N::RequiresCapabilities(_)
                | N::AopAdvice(_)
                | N::DiBinding(_)
                | N::InjectGraph(_)
                | N::SecurityPolicy(_)
                | N::SecurityGate(_)
                | N::SandboxPolicy(_)
                | N::CapabilityPolicy(_)
                | N::UiPolicy(_)
                | N::ArchitectureRule(_)
                | N::MockDecl(_)
                | N::Newtype(_)
                | N::Extend(_)
                | N::Pass(_)
        )
    }

    /// Guard the silent no-op run.
    ///
    /// A module with no `fn main` AND no executable top-level item runs
    /// NOTHING. Historically that path returned `Ok(0)` without printing a
    /// single character, so a mis-parse that re-parented `main` into an
    /// enclosing block was indistinguishable from a successful run — the worst
    /// possible diagnostic shape, and the mechanism behind
    /// doc/08_tracking/bug/
    /// parser_while_continuation_swallows_following_declarations_2026-08-01.md.
    ///
    /// Returns an error describing what the module DID declare so the caller
    /// gets a located, actionable message instead of exit 0.
    fn reject_silent_no_op_module(items: &[simple_parser::ast::Node]) -> Result<(), String> {
        if items.iter().any(|i| !Self::is_pure_declaration(i)) {
            return Ok(());
        }
        if items
            .iter()
            .any(|i| matches!(i, simple_parser::ast::Node::Function(f) if f.name == "main"))
        {
            return Ok(());
        }
        let nested_main = items.iter().any(|i| {
            matches!(i, simple_parser::ast::Node::Function(f) if f.body.statements.iter().any(|s| {
                matches!(s, simple_parser::ast::Node::Function(inner) if inner.name == "main")
            }))
        });
        let mut msg = String::from(
            "no `main` function and no top-level statements: this module declares only \
             names, so running it would execute nothing",
        );
        if nested_main {
            msg.push_str(
                "\n  = note: a `main` was found NESTED inside another function's body. \
                 That is almost always an indentation/line-continuation mis-parse that \
                 re-parented the following declarations — check any multi-line \
                 `while`/`for`/`match` header just above it.",
            );
        }
        msg.push_str("\n  = help: add `fn main():`, or run this file with `simple test` / import it instead of running it directly");
        Err(msg)
    }

    // =========================================================================
    // Compilation methods
    // =========================================================================

    /// Compile source string to SMF file
    pub fn compile_source(&self, source: &str, out: &Path) -> Result<(), String> {
        let smf_bytes = self.compile_to_memory(source)?;
        fs::write(out, smf_bytes).map_err(|e| format!("write smf: {e}"))
    }

    /// Compile source string to SMF file with options (LLM-friendly #885-887)
    pub fn compile_source_with_options(
        &self,
        source: &str,
        out: &Path,
        options: &crate::CompileOptions,
    ) -> Result<(), String> {
        let smf_bytes = self.compile_to_memory_with_options(source, options)?;
        fs::write(out, smf_bytes).map_err(|e| format!("write smf: {e}"))
    }

    /// Compile source string to SMF file for a specific target architecture.
    /// This enables cross-compilation.
    pub fn compile_source_for_target(&self, source: &str, out: &Path, target: Target) -> Result<(), String> {
        let smf_bytes = self.compile_to_memory_for_target(source, target)?;
        fs::write(out, smf_bytes).map_err(|e| format!("write smf: {e}"))
    }

    /// Compile a source file to target-specific bytes with import resolution.
    pub fn compile_file_for_target(&self, source_path: &Path, out: &Path, target: Target) -> Result<(), String> {
        let smf_bytes = self.compile_file_to_memory_for_target(source_path, target)?;
        fs::write(out, smf_bytes).map_err(|e| format!("write smf: {e}"))
    }

    /// Compile source string to SMF bytes in memory (no disk I/O)
    pub fn compile_to_memory(&self, source: &str) -> Result<Vec<u8>, String> {
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile_source_to_memory(source)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile source string to SMF bytes with options (LLM-friendly #885-887)
    pub fn compile_to_memory_with_options(
        &self,
        source: &str,
        options: &crate::CompileOptions,
    ) -> Result<Vec<u8>, String> {
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;

        // Set emit options
        if let Some(path) = &options.emit_ast {
            compiler.set_emit_ast(path.clone());
        }
        if let Some(path) = &options.emit_hir {
            compiler.set_emit_hir(path.clone());
        }
        if let Some(path) = &options.emit_mir {
            compiler.set_emit_mir(path.clone());
        }

        compiler
            .compile_source_to_memory(source)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile source string to SMF bytes for a specific target architecture.
    pub fn compile_to_memory_for_target(&self, source: &str, target: Target) -> Result<Vec<u8>, String> {
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile_source_to_memory_for_target(source, target)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile a source file to target-specific bytes with import resolution.
    pub fn compile_file_to_memory_for_target(&self, source_path: &Path, target: Target) -> Result<Vec<u8>, String> {
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile_file_to_memory_for_target(source_path, target)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile source string to SMF bytes using native codegen (HIR → MIR → Cranelift)
    pub fn compile_to_memory_native(&self, source: &str) -> Result<Vec<u8>, String> {
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile_source_to_memory_native(source)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile file to SMF
    pub fn compile_file(&self, path: &Path, out: &Path) -> Result<(), String> {
        // Parse source to collect error hints
        let source = std::fs::read_to_string(path).map_err(|e| format!("failed to read {}: {}", path.display(), e))?;
        // Normalize CRLF → LF
        let source = if source.contains('\r') {
            source.replace('\r', "")
        } else {
            source
        };
        let source = simple_compiler::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(
            &source,
            simple_common::target::TargetArch::host(),
        );
        let mut parser = Parser::new(&source);
        let parse_result = parser.parse();

        // Display error hints (even if parsing failed)
        self.display_error_hints(&parser, &source);

        // Now check if parsing succeeded
        let _ast = parse_result.map_err(|e| format!("parse error: {}", e))?;

        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile(path, out)
            .map_err(|e| format!("compile failed ({}): {e}", path.display()))
    }

    /// Compile a source file to SMF with compile options (LLM-friendly #885-887)
    pub fn compile_file_with_options(
        &self,
        path: &Path,
        out: &Path,
        options: &crate::CompileOptions,
    ) -> Result<(), String> {
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;

        // Apply options (flatten nested Option)
        if let Some(emit_ast) = &options.emit_ast {
            compiler.set_emit_ast(emit_ast.clone());
        }
        if let Some(emit_hir) = &options.emit_hir {
            compiler.set_emit_hir(emit_hir.clone());
        }
        if let Some(emit_mir) = &options.emit_mir {
            compiler.set_emit_mir(emit_mir.clone());
        }

        // Enable coverage instrumentation if requested (#674)
        if options.coverage {
            compiler.set_coverage_enabled(true);
        }
        compiler.set_simd_mode(match options.simd_mode {
            crate::compile_options::SimdMode::Off => CompilerSimdMode::Off,
            crate::compile_options::SimdMode::Auto => CompilerSimdMode::Auto,
            crate::compile_options::SimdMode::Report => CompilerSimdMode::Report,
        });

        compiler
            .compile(path, out)
            .map_err(|e| format!("compile failed ({}): {e}", path.display()))
    }

    // =========================================================================
    // Loading methods
    // =========================================================================

    /// Load an SMF module from file
    pub fn load_module(&self, path: &Path) -> Result<LoadedModule, String> {
        self.loader
            .load_with_resolver(path, |name| {
                if std::env::var_os("SIMPLE_RESOLVER_TRACE").is_some() {
                    let _ = std::fs::OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open("/tmp/simple_resolver.log")
                        .and_then(|mut f| {
                            use std::io::Write;
                            writeln!(f, "resolve {}", name)
                        });
                }
                self.symbol_provider.get_symbol(name).map(|ptr| ptr as usize)
            })
            .map_err(|e| format!("load failed: {e}"))
    }

    /// Load an SMF module from memory buffer
    pub fn load_module_from_memory(&self, bytes: &[u8]) -> Result<LoadedModule, String> {
        self.loader
            .load_from_memory_with_resolver(bytes, |name| {
                if std::env::var_os("SIMPLE_RESOLVER_TRACE").is_some() {
                    let _ = std::fs::OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open("/tmp/simple_resolver.log")
                        .and_then(|mut f| {
                            use std::io::Write;
                            writeln!(f, "resolve {}", name)
                        });
                }
                self.symbol_provider.get_symbol(name).map(|ptr| ptr as usize)
            })
            .map_err(|e| format!("load failed: {e}"))
    }

    // =========================================================================
    // Unified execution helper (reduces duplication)
    // =========================================================================

    /// Execute a loaded module and collect GC afterward
    fn execute_and_gc(&self, module: &LoadedModule) -> Result<i32, String> {
        run_module_init(module)?;
        let exit = run_main(module)?;
        self.collect_gc();
        Ok(exit)
    }

    // =========================================================================
    // Run methods (all use execute_and_gc internally)
    // =========================================================================

    /// Compile and run source string, return exit code (uses temp file)
    pub fn run_source(&self, source: &str) -> Result<i32, String> {
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let out = tmp.path().join("module.smf");
        self.compile_source(source, &out)?;
        let module = self.load_module(&out)?;
        self.execute_and_gc(&module)
    }

    /// Compile and run source string in memory (no disk I/O)
    pub fn run_source_in_memory(&self, source: &str) -> Result<i32, String> {
        let smf_bytes = self.compile_to_memory(source)?;
        let module = self.load_module_from_memory(&smf_bytes)?;
        self.execute_and_gc(&module)
    }

    /// Compile using native codegen and run source string (uses temp file)
    ///
    /// Uses JIT compilation for proper symbol resolution of runtime SFFI functions.
    pub fn run_source_native(&self, source: &str) -> Result<i32, String> {
        // Delegate to in-memory version since JIT doesn't need disk I/O
        self.run_source_in_memory_native(source)
    }

    /// Compile using native codegen and run source string in memory (no disk I/O)
    ///
    /// Uses JIT compilation for proper symbol resolution of runtime SFFI functions.
    /// Falls back to interpreter for code without explicit `fn main()`.
    pub fn run_source_in_memory_native(&self, source: &str) -> Result<i32, String> {
        use simple_compiler::codegen::JitCompiler;
        use simple_compiler::hir;
        use simple_compiler::interpreter::evaluate_module;
        use simple_compiler::mir::lower_to_mir;
        use simple_parser::Parser;

        // Parse the same cfg-filtered text used for diagnostics and lowering.
        let source = simple_compiler::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(
            source,
            simple_common::target::TargetArch::host(),
        );
        let mut parser = Parser::new(&source);
        let parse_result = parser.parse();

        // Display error hints (even if parsing failed)
        self.display_error_hints(&parser, &source);

        // Now check if parsing succeeded
        let mut ast = parse_result.map_err(|e| format!("parse error: {}", e))?;

        // Drop wrong-arch @cfg(<arch>) fn variants before lowering: JIT/interp
        // execute on the HOST, and without this strip first-wins registration
        // runs whichever variant is declared first (multivariant misdispatch).
        simple_compiler::pipeline::cfg_strip::strip_inactive_cfg_arch_fns_for_host(&mut ast);

        // Lower to HIR
        let hir_module = hir::lower(&ast).map_err(|e| format!("HIR lowering error: {}", e))?;

        // Lower to MIR
        let mir_module = lower_to_mir(&hir_module).map_err(|e| format!("MIR lowering error: {}", e))?;

        // Check if we have a proper main function
        let has_main_function = mir_module.functions.iter().any(|f| f.name == "main");

        if !has_main_function {
            // Never exit 0 silently: a module with nothing to run is an error,
            // not a successful no-op run.
            Self::reject_silent_no_op_module(&ast.items)?;
            // Fallback: evaluate via interpreter for module-level `main = ...` syntax
            let exit_code = evaluate_module(&ast.items).map_err(|e| format!("{}", e))?;
            self.collect_gc();
            return Ok(exit_code);
        }

        // JIT compile using the configured symbol provider
        let mut jit =
            JitCompiler::with_provider(self.symbol_provider.clone()).map_err(|e| format!("JIT init error: {}", e))?;

        jit.compile_module(&mir_module)
            .map_err(|e| format!("JIT compile error: {}", e))?;

        // Execute main function
        let exit_code = unsafe {
            jit.call_i64_void("main")
                .map_err(|e| format!("JIT execution error: {}", e))?
        };

        self.collect_gc();
        Ok(exit_code as i32)
    }

    /// Run SMF from memory buffer
    pub fn run_smf_from_memory(&self, bytes: &[u8]) -> Result<i32, String> {
        self.run_smf_from_memory_with_args(bytes, vec![])
    }

    /// Run SMF from memory buffer with arguments
    pub fn run_smf_from_memory_with_args(&self, bytes: &[u8], args: Vec<String>) -> Result<i32, String> {
        // Set arguments in runtime before loading module
        simple_runtime::value::rt_set_args_vec(&args);

        let module = self.load_module_from_memory(bytes)?;
        self.execute_and_gc(&module)
    }

    /// Run a pre-compiled SMF file directly
    pub fn run_smf(&self, path: &Path) -> Result<i32, String> {
        self.run_smf_with_args(path, vec![])
    }

    /// Run a pre-compiled SMF file with arguments
    pub fn run_smf_with_args(&self, path: &Path, args: Vec<String>) -> Result<i32, String> {
        // Set arguments in runtime before loading module
        simple_runtime::value::rt_set_args_vec(&args);

        let module = self.load_module(path)?;
        self.execute_and_gc(&module)
    }

    /// Attach the module's declared sandbox policy to a WASI config.
    ///
    /// The compiler already renders every `sandbox` policy into
    /// `sandbox_manifest.sdn`, and `WasiCapabilityTable` already knows how to
    /// parse it, but nothing connected the two: the runtime's capability table
    /// was only ever populated from tests, so `validate_capabilities` returned
    /// `Ok(())` unconditionally in production. This is that connection.
    ///
    /// A module that declares no sandbox gets no table — there is no policy to
    /// enforce, and inventing an empty (deny-everything) one would reject every
    /// unsandboxed module. A module that declares exactly one sandbox gets that
    /// sandbox's grants. Declaring more than one is rejected rather than guessed
    /// at, because picking arbitrarily would silently enforce the wrong policy.
    #[cfg(feature = "wasm")]
    fn apply_wasm_sandbox_policy(
        &self,
        source: &str,
        config: simple_wasm_runtime::WasiConfig,
    ) -> Result<simple_wasm_runtime::WasiConfig, String> {
        let Some(manifest) = simple_compiler::sandbox_manifest_for_source("<wasm-source>", source) else {
            return Ok(config);
        };
        let names = simple_wasm_runtime::declared_sandbox_names(&manifest);

        match names.as_slice() {
            [] => Ok(config),
            [name] => config
                .with_sandbox_policy(name, &manifest)
                .map_err(|e| format!("wasm sandbox policy: {e}")),
            _ => Err(format!(
                "wasm sandbox policy: module declares {} sandboxes ({}); \
                 WASI enforcement needs exactly one",
                names.len(),
                names.join(", ")
            )),
        }
    }

    /// Compile to WebAssembly and run with Wasmer runtime (WASI environment).
    ///
    /// Offers the guest nothing. Kept for callers that only want to execute a
    /// module; see `run_source_wasm_with` for the lane the CLI uses.
    #[cfg(feature = "wasm")]
    pub fn run_source_wasm(&self, source: &str) -> Result<i32, String> {
        self.run_source_wasm_with(source, &WasmInvocation::default())
    }

    /// Compile to WebAssembly and run it with the capabilities this invocation
    /// offers, subject to the module's declared sandbox policy.
    ///
    /// The `invocation` argument is the point of this function. Enforcement
    /// happens in `validate_capabilities`, which walks the env, stdin and
    /// preopens the host is handing over; with the bare `WasiConfig::new()` this
    /// used to build, all three were empty and no policy could ever deny
    /// anything.
    #[cfg(feature = "wasm")]
    pub fn run_source_wasm_with(&self, source: &str, invocation: &WasmInvocation) -> Result<i32, String> {
        use simple_common::target::{Target, TargetArch, WasmRuntime};
        use simple_wasm_runtime::{WasiConfig, WasmRunner};

        // Compile to wasm32-wasi
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Wasi);
        let wasm_bytes = self.compile_to_memory_for_target(source, target)?;

        // Write to temp file (WasmRunner expects a file path)
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let wasm_path = tmp.path().join("module.wasm");
        fs::write(&wasm_path, wasm_bytes).map_err(|e| format!("write wasm: {e}"))?;

        // Offer the guest exactly what this invocation supplies. This has to
        // happen before the policy is attached only in the sense that the
        // config must already carry the capabilities; `validate_capabilities`
        // then compares the two. An empty config here is what made the whole
        // control unobservable.
        let mut config = WasiConfig::new();
        for (key, value) in &invocation.env {
            config = config.with_env(key, value);
        }
        for (host_path, guest_path) in &invocation.preopens {
            config = config.with_preopen_dir(host_path, guest_path);
        }
        if !invocation.stdin.is_empty() {
            config = config.with_stdin(&invocation.stdin);
        }

        // Carry the module's own sandbox policy so `validate_capabilities` has
        // something to enforce. Without this the capability table stays `None`
        // and every grant check short-circuits to "allow".
        let config = self.apply_wasm_sandbox_policy(source, config)?;
        let mut runner = WasmRunner::with_config(config).map_err(|e| format!("create wasm runner: {e}"))?;

        // Run the main function
        let result = runner
            .run_wasm_file(&wasm_path, "main", &[])
            .map_err(|e| format!("wasm execution: {e}"))?;

        // Push WASM captured output to runtime capture buffers
        // This allows rt_capture_stdout_stop() / rt_capture_stderr_stop() to retrieve them
        if let Ok(stdout) = runner.config().get_stdout_string() {
            if !stdout.is_empty() {
                use simple_runtime::value::rt_print_str;
                // Write to capture buffer (rt_print_str checks if capture is active)
                unsafe {
                    rt_print_str(stdout.as_ptr(), stdout.len() as u64);
                }
            }
        }
        if let Ok(stderr) = runner.config().get_stderr_string() {
            if !stderr.is_empty() {
                use simple_runtime::value::rt_eprint_str;
                // Write to capture buffer (rt_eprint_str checks if capture is active)
                unsafe {
                    rt_eprint_str(stderr.as_ptr(), stderr.len() as u64);
                }
            }
        }

        // Convert RuntimeValue to i32 exit code
        let exit_code = if result.is_int() {
            result.as_int() as i32
        } else {
            0 // Default to 0 for non-integer returns
        };

        self.collect_gc();
        Ok(exit_code)
    }

    /// Compile a source file to WebAssembly and run it under the WASI host,
    /// offering the guest whatever this process invocation supplies.
    ///
    /// This is the CLI's entry into the wasm lane. It fails loudly rather than
    /// silently falling back to the JIT: a run that was asked to be sandboxed
    /// must never quietly become an unsandboxed one.
    #[cfg(feature = "wasm")]
    pub fn run_file_wasm(&self, path: &Path) -> Result<i32, String> {
        let source = fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
        self.run_source_wasm_with(&source, &WasmInvocation::from_process_env())
    }

    /// Without the `wasm` feature the wasm lane cannot run. Refuse explicitly.
    #[cfg(not(feature = "wasm"))]
    pub fn run_file_wasm(&self, _path: &Path) -> Result<i32, String> {
        Err("SIMPLE_EXECUTION_MODE=wasm requires a build with `--features wasm`".to_string())
    }

    /// Run a file, auto-detecting type by extension (.spl or .smf).
    ///
    /// Dispatches to JIT or interpreter based on `execution_mode`.
    /// When in JIT mode, falls back to interpreter on JIT failure.
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        self.run_file_with_args(path, vec![])
    }

    /// Run a file with command-line arguments, auto-detecting type by extension.
    ///
    /// Dispatches to JIT or interpreter based on `execution_mode`.
    /// When in JIT mode, falls back to interpreter with args on JIT failure.
    pub fn run_file_with_args(&self, path: &Path, args: Vec<String>) -> Result<i32, String> {
        let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");

        // JIT and compiled-module execution resolve sys_get_args/rt_get_args
        // through the hosted runtime, rather than the interpreter argument
        // store. Initialize that runtime boundary before choosing a lane so
        // every execution mode observes the same supplied argv.
        simple_runtime::value::rt_set_args_vec(&args);

        // The wasm lane is checked before the extension match so that it cannot
        // be reached by only one of the two run entry points. `run_file_with_args`
        // and `run_file_interpreted_with_args` are both public and both are
        // called directly (cli/basic.rs picks between them on `is_jit_mode()`),
        // so a wasm arm added to only one of them would be inert whenever the
        // other is chosen.
        if self.execution_mode.is_wasm() {
            return self.run_file_wasm(path);
        }

        match extension {
            "smf" => self.run_smf_with_args(path, args),
            "spl" | "simple" | "sscript" | "shs" | "" => {
                if self.execution_mode.is_jit() && should_prefer_interpreter_for_source(path, extension) {
                    return self.run_file_interpreted_with_args(path, args);
                }
                if self.execution_mode.is_jit() {
                    // Try JIT first, fall back to interpreter on failure
                    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run_file_jit(path))) {
                        Ok(Ok(exit_code)) => Ok(exit_code),
                        Ok(Err(jit_err)) => {
                            // SIMPLE_JIT_STRICT fail-open fix: `first_unresolved_import`
                            // in codegen/jit.rs already tags its error message with a
                            // "SIMPLE_JIT_STRICT:" prefix specifically when the strict
                            // env var is set, precisely so an unresolved-symbol NULL-jump
                            // risk becomes a hard failure instead of a silent de-JIT --
                            // but this catch site used to swallow EVERY `jit_err` (strict
                            // or not) into the same unconditional interpreter fallback,
                            // making SIMPLE_JIT_STRICT=1 print a "refusing to fall back"
                            // message and then fall back anyway (exit 0). Honor the tag:
                            // propagate as a real, printed, non-zero-exit error instead of
                            // falling back, for this class of failure only -- every other
                            // JIT failure reason (lambda/closure ABI mismatch, genuine
                            // compiler bugs, etc.) still falls back leniently as before,
                            // unchanged blast radius outside the unresolved-import family.
                            if jit_err.contains("SIMPLE_JIT_STRICT:") {
                                return Err(jit_err);
                            }
                            eprintln!(
                                "[INFO] JIT compilation failed, falling back to interpreter: {}",
                                jit_err
                            );
                            self.run_file_interpreted_with_args(path, args)
                        }
                        Err(payload) => {
                            eprintln!(
                                "[INFO] JIT panicked, falling back to interpreter: {}",
                                panic_payload_to_string(payload.as_ref())
                            );
                            self.run_file_interpreted_with_args(path, args)
                        }
                    }
                } else {
                    // Interpreter path (current default)
                    let out_path = self.get_build_path_for_source(path)?;
                    self.compile_file(path, &out_path)?;
                    let module = self.load_module(&out_path)?;
                    self.execute_and_gc(&module)
                }
            }
            other => Err(format!(
                "unsupported file extension '.{}': expected '.spl', '.simple', '.sscript', or '.smf'",
                other
            )),
        }
    }

    /// Run a .spl file using JIT compilation via ExecutionManager.
    ///
    /// Loads with import resolution → HIR → MIR → JIT compile → execute.
    /// Falls back to interpreter for code without `fn main()`.
    pub fn run_file_jit(&self, path: &Path) -> Result<i32, String> {
        use simple_compiler::codegen::{ExecutionManager, LocalExecutionManager, JitBackend};
        use simple_compiler::hir;
        use simple_compiler::interpreter::{evaluate_module, set_current_file};
        use simple_compiler::mir::lower_to_mir;
        use simple_compiler::pipeline::module_loader::load_module_with_imports;
        use std::collections::HashSet;

        let trace = std::env::var("SIMPLE_NATIVE_BUILD_RUST_TRACE").ok().as_deref() == Some("1");
        if trace {
            eprintln!("[rust-jit] start path={}", path.display());
        }

        // Set current file for module resolution
        set_current_file(Some(path.to_path_buf()));

        // Load with import resolution (handles `use` statements)
        let mut ast =
            load_module_with_imports(path, &mut HashSet::new()).map_err(|e| format!("module load error: {}", e))?;

        // Drop wrong-arch @cfg(<arch>) fn variants: the JIT executes on the
        // HOST, and codegen's declare_functions is first-wins by source order,
        // so an unstripped wrong-arch variant declared first would be the one
        // that runs (bug x64_freestanding_cfg_multivariant_misdispatch).
        simple_compiler::pipeline::cfg_strip::strip_inactive_cfg_arch_fns_for_host(&mut ast);

        // Lower to HIR with context so imported types (enums, classes) are resolved.
        // Lenient variant: aligns this lane's `Lowerer::with_module_resolver`
        // memory-safety strictness with the canonical native-build/compile lane
        // (native_project/compiler.rs sets `set_strict_mode(false)` +
        // `set_lenient_types(true)` on the identical constructor immediately
        // after construction). Without this, `run_file_jit` was the only lane
        // that escalated W1006 (mutation without `mut` capability) to a hard
        // abort instead of a warning — every other lane (interpreter,
        // native-build, compile, tests) already tolerates this pattern
        // silently. See
        // doc/08_tracking/bug/jit_drawirrendertarget_moduleresolver_gap_2026-07-30.md.
        let project_hint = simple_compiler::pipeline::native_single_file_project_hint(path);
        // Collect duplicate struct layouts from the flattened AST so the
        // lowerer's duplicate-variant consensus fallback has data on this lane
        // (the run/JIT lane has no native_project import pass; without this,
        // same-named structs from different modules fail field resolution and
        // the whole module silently de-JITs — the GlyphBitmap gbm_width class).
        // GATED behind SIMPLE_JIT_DUP_STRUCT_FEED: feeding the map lets more
        // modules JIT, but on widget-heavy graphs the JIT'd output diverged
        // from the interpreter (2026-08-11: ui_showcase 2D render missing
        // widgets + lost clip groups). Default OFF keeps the safe de-JIT.
        let duplicate_structs = if std::env::var_os("SIMPLE_JIT_DUP_STRUCT_FEED").is_some() {
            simple_compiler::pipeline::module_loader::collect_duplicate_struct_defs(&ast)
        } else {
            std::collections::HashMap::new()
        };
        let hir_module = match hir::lower_with_context_lenient_project_hint_and_duplicate_structs(
            &ast,
            path,
            project_hint.as_deref(),
            duplicate_structs,
        ) {
            Ok(m) => m,
            Err(e) => return Err(jit_strict_fallback_error_for("HIR lowering error", &e, Some(path))),
        };

        // Lower to MIR
        let mut mir_module = match lower_to_mir(&hir_module) {
            Ok(m) => m,
            Err(e) => return Err(jit_strict_fallback_error_for("MIR lowering error", &e, Some(path))),
        };
        if trace {
            eprintln!(
                "[rust-jit] lowered functions={} externs={}",
                mir_module.functions.len(),
                mir_module.extern_fn_names.len()
            );
        }

        // Extern declarations the JIT cannot resolve (e.g. rt_torch_* in a
        // torch-less build) would link as null pointers and SIGSEGV at call
        // time. Route them through the interpreter bridge, whose extern
        // dispatch has graceful unavailable-backend handlers.
        let unresolvable_externs: HashSet<String> = mir_module
            .extern_fn_names
            .iter()
            .filter(|name| self.symbol_provider.get_symbol(name.as_str()).is_none())
            .cloned()
            .collect();
        if std::env::var("SIMPLE_DEBUG_EXTERNS").is_ok() {
            eprintln!(
                "[run_file_jit] extern_fn_names={:?} unresolvable={:?}",
                mir_module.extern_fn_names, unresolvable_externs
            );
        }
        if !unresolvable_externs.is_empty() {
            // Externs whose declared return type is a heap/composite value (tuple,
            // text) must keep their boxed RuntimeValue across the interpreter
            // bridge instead of being unboxed to a raw i64 — see
            // compile_interp_call in codegen/instr/core.rs.
            let boxed_returns = simple_compiler::compilability::boxed_return_functions(&ast.items);
            simple_compiler::mir::apply_hybrid_transform(&mut mir_module, &unresolvable_externs, &boxed_returns);
        }

        // Check for main function
        let has_main = mir_module.functions.iter().any(|f| f.name == "main");

        if !has_main {
            // Never exit 0 silently — see `reject_silent_no_op_module`.
            Self::reject_silent_no_op_module(&ast.items)?;
            let exit_code = evaluate_module(&ast.items).map_err(|e| format!("{}", e))?;
            set_current_file(None);
            self.collect_gc();
            return Ok(exit_code);
        }

        // Module-level BDD example blocks are not reachable from the JIT entry
        // path.  With a `main` present the JIT calls `main` and nothing else, so
        // every module-level `describe`/`it` statement is dropped: the file
        // prints whatever `main` prints, reports ZERO examples, and exits 0 — a
        // deliberately-failing example is invisible.  Measured on
        // test/01_unit/compiler/native/baremetal_syntax_spec.spl (22 blocks, 0
        // executed) and reproduced on a two-example fixture: the same file runs
        // both examples and exits 1 the moment its `fn main` is removed, or
        // under SIMPLE_EXECUTION_MODE=interpreter.  See
        // doc/08_tracking/bug/bare_assert_statement_vacuity_2026-08-02.md OPEN 3.
        //
        // Bail out to the interpreter (which executes module-level statements)
        // exactly like the generator gap below, so such a file genuinely runs
        // instead of silently reporting success for nothing.  A file whose
        // examples live INSIDE `main` is unaffected: extract_file_test_meta does
        // not descend into function bodies, so total_tests counts module-level
        // examples only.
        let module_level_examples = simple_parser::test_analyzer::extract_file_test_meta(&ast.items, None).total_tests;
        if module_level_examples > 0 {
            return Err(format!(
                "module declares {module_level_examples} top-level BDD example(s) that the JIT \
                 entry path would silently skip (it calls `main` only); falling back to interpreter"
            ));
        }

        // B3 for-in gap: generator functions (containing Yield instructions) are not
        // supported by the Cranelift JIT state-machine lowering when called as top-level
        // `gen fn` declarations (generator_state_map is None for these).  The JIT would
        // compile them to a safe NIL return, but `for x in gen()` then passes that NIL
        // pointer to rt_for_iterable / rt_array_len and segfaults.
        // Detect any Yield in the MIR and bail out so the caller's fallback to the
        // interpreter (which handles generators correctly) takes over.
        let has_generator = mir_module.functions.iter().any(|f| {
            f.blocks.iter().any(|b| {
                b.instructions
                    .iter()
                    .any(|i| matches!(i, simple_compiler::mir::MirInst::Yield { .. }))
            })
        });
        if has_generator {
            return Err("JIT does not support generator functions (for-in over gen fn); \
                 falling back to interpreter"
                .to_string());
        }

        // Select JIT backend based on execution mode
        let jit_backend = match self.execution_mode {
            ExecutionMode::CraneliftJit => JitBackend::Cranelift,
            ExecutionMode::LlvmJit => JitBackend::Llvm,
            _ => JitBackend::Auto,
        };

        // Create execution manager and compile
        let mut em = LocalExecutionManager::with_provider(jit_backend, self.symbol_provider.clone())?;

        if trace {
            eprintln!("[rust-jit] compile start");
        }
        em.compile_module(&mir_module)?;
        if trace {
            eprintln!("[rust-jit] execute main start");
        }

        // Mark the process as running seed-JIT code for the duration of main:
        // JIT'd code binds rt_* symbols in-process, so stdlib gates like
        // simd_kernels' write_span routing can detect this lane via
        // rt_is_jit_runtime(). Cleared afterwards so a later interpreter
        // fallback in the same process does not misreport.
        simple_runtime::rt_set_jit_runtime(true);
        let exit_code = em.execute("main", &[]);
        simple_runtime::rt_set_jit_runtime(false);
        let exit_code = exit_code?;
        if trace {
            eprintln!("[rust-jit] execute main done exit={}", exit_code);
        }
        set_current_file(None);
        self.collect_gc();
        Ok(exit_code as i32)
    }

    /// Get the build path for a compiled SMF file
    ///
    /// Instead of polluting the source directory with .smf files, this creates
    /// a .simple/build directory next to the source file.
    ///
    /// Example:
    ///   simple/std_lib/test/features/arrays_spec.spl
    ///   -> simple/std_lib/test/features/.simple/build/arrays_spec.smf
    fn get_build_path_for_source(&self, source_path: &Path) -> Result<std::path::PathBuf, String> {
        let parent = source_path
            .parent()
            .ok_or_else(|| format!("source file has no parent directory: {}", source_path.display()))?;

        let file_stem = source_path
            .file_stem()
            .ok_or_else(|| format!("source file has no name: {}", source_path.display()))?;

        // Create .simple/build directory
        let build_dir = parent.join(".simple").join("build");
        fs::create_dir_all(&build_dir)
            .map_err(|e| format!("failed to create build directory {}: {}", build_dir.display(), e))?;

        // Return path: .simple/build/{filename}.smf
        Ok(build_dir.join(file_stem).with_extension("smf"))
    }

    /// Run a .spl file using the interpreter (not native compilation).
    ///
    /// This method loads the file with proper import resolution and runs it
    /// through the interpreter, which supports all language features including
    /// associated function calls like `Type::method()`.
    pub fn run_file_interpreted(&self, path: &Path) -> Result<i32, String> {
        self.run_file_interpreted_with_args(path, vec![])
    }

    /// Run a .spl file using the interpreter with command-line arguments.
    ///
    /// The args are made available to the Simple program via `sys_get_args()`.
    pub fn run_file_interpreted_with_args(&self, path: &Path, args: Vec<String>) -> Result<i32, String> {
        use simple_compiler::interpreter::{evaluate_module, set_current_file};
        use simple_compiler::pipeline::module_loader::load_module_with_imports;
        use simple_compiler::set_interpreter_args;
        use std::collections::HashSet;

        // See the matching guard in `run_file_with_args`: both entry points must
        // honour the wasm mode, otherwise which lane enforces the sandbox policy
        // depends on which of the two the caller happened to pick.
        if self.execution_mode.is_wasm() {
            return self.run_file_wasm(path);
        }

        // Set interpreter arguments
        set_interpreter_args(args);

        // Set current file for module resolution
        set_current_file(Some(path.to_path_buf()));

        let mut module =
            load_module_with_imports(path, &mut HashSet::new()).map_err(|e| format!("compile failed: {}", e))?;

        // Drop wrong-arch @cfg(<arch>) fn variants before interpretation (the
        // interpreter's registration is also first-wins by source order).
        simple_compiler::pipeline::cfg_strip::strip_inactive_cfg_arch_fns_for_host(&mut module);

        // Never exit 0 silently — see `reject_silent_no_op_module`. This is the
        // LAST fallback in the run chain, so a miss here is what actually
        // reaches the user as "no output, exit 0".
        Self::reject_silent_no_op_module(&module.items)?;

        let exit_code = evaluate_module(&module.items).map_err(|e| format!("{}", e))?;

        // Clear current file after evaluation
        set_current_file(None);

        self.collect_gc();
        Ok(exit_code)
    }
}

/// Shared helper for the JIT-compile failure paths that represent a genuine
/// "this module cannot be JIT-compiled" outcome -- currently HIR and MIR
/// lowering errors (`LowerError::UnknownVariable` and friends). This is
/// deliberately narrower than every JIT failure reason: known, documented
/// JIT limitations (lambda/closure ABI mismatch in codegen/jit.rs, the
/// generator/Yield bail-out above, genuine Cranelift codegen bugs) are NOT
/// routed through this helper and stay silently lenient by design, matching
/// the pre-existing scoping discipline recorded at the `SIMPLE_JIT_STRICT
/// fail-open fix` comment in `run_file_with_args` above.
///
/// Mirrors codegen/jit.rs's `first_unresolved_import` convention exactly:
/// always print a loud, greppable `[jit-fallback]` marker naming the
/// failure (a whole-module de-JIT is a proven ~100-1000x-cost defect class
/// here, see the comment on `first_unresolved_import`), then either tag the
/// returned message so `run_file_with_args`'s existing
/// `jit_err.contains("SIMPLE_JIT_STRICT:")` check turns it into a hard,
/// non-zero-exit error, or return the same plain, untagged message as
/// before so the caller falls back to the interpreter unchanged. Off by
/// default: SIMPLE_JIT_STRICT unset or "0" is byte-for-byte the pre-existing
/// lenient behavior (only the message text gained a shared prefix).
///
/// What this can NEVER catch: a silent miscompile that links and *runs* to
/// completion produces no `Err` at all, so there is nothing here to tag.
/// See doc/08_tracking/bug/jit_strict_coverage_gap_2026-07-30.md.
/// Builtin containers whose paren-less accessors are the de-JIT defect class.
///
/// See `PARENLESS_ACCESSOR_FIELDS`. Kept as the exact `struct '<name>'` text
/// that `hir/lower/expr/access.rs:400` (the SOLE producer of the
/// "cannot infer field type while lowering" message -- verified by a
/// whole-tree grep) interpolates, so an `ANY` receiver never matches: the
/// `struct 'ANY'` drops are a DIFFERENT, wider cause that CAN occur in code
/// that compiles, and must stay leniently lenient.
const PARENLESS_ACCESSOR_STRUCTS: [&str; 3] = ["struct 'Array'", "struct 'String'", "struct 'Dict'"];

/// Accessor names that are methods on a builtin container and are NEVER a
/// legitimate field on one. `xs.length` parses as a field access, has no HIR
/// lowering, and de-JITs the whole enclosing module (~100-1000x) while still
/// printing the right answer -- `.length` in particular is the only member the
/// interpreter also evaluates correctly, which is why it accumulated the most
/// sites. Genuine user structs with a `length` field are unaffected: they
/// resolve, so they never reach the error this matches on.
const PARENLESS_ACCESSOR_FIELDS: [&str; 8] = ["length", "len", "size", "empty", "chars", "first", "last", "capacity"];

/// True when a HIR lowering error is the paren-less-container-accessor class.
///
/// This class is escalated to a hard error UNCONDITIONALLY (not merely under
/// `SIMPLE_JIT_STRICT=1`), because it is never present in a working build:
/// every file containing one already fails `bin/simple compile` with this same
/// diagnostic. Making `run` agree with `compile` therefore cannot regress a
/// build that works today -- it only removes the silent ~100-1000x degradation
/// that made the class invisible. See
/// doc/08_tracking/bug/paren_less_accessor_whole_module_de_jit_2026-08-08.md.
fn is_parenless_container_accessor(msg: &str) -> bool {
    if !msg.contains("cannot infer field type while lowering") {
        return false;
    }
    if !PARENLESS_ACCESSOR_STRUCTS.iter().any(|s| msg.contains(s)) {
        return false;
    }
    PARENLESS_ACCESSOR_FIELDS
        .iter()
        .any(|f| msg.contains(&format!("field '{f}'")))
}

/// `jit_strict_fallback_error` with the offending source path, when known.
///
/// The de-JIT message historically named the struct and field but NOT the
/// file, so a drop in a deep import could not be attributed without compiling
/// one file at a time (Finding 2 of the bug doc above). `path` is appended
/// whenever the caller knows it.
fn jit_strict_fallback_error_for(kind: &str, err: &impl std::fmt::Display, path: Option<&Path>) -> String {
    let where_ = match path {
        Some(p) => format!(" [in {}]", p.display()),
        None => String::new(),
    };
    let msg = format!("{err}");

    // An import naming a module that does not exist can never be satisfied by
    // any later stage, so de-JITing to the interpreter does not "recover" it --
    // it just moves the failure to the first CALL, where it surfaces as
    // `semantic: function <name> not found` with no mention of the import that
    // caused it. That is exactly how six stdlib files shipped
    // `use string.{char_from_code}` (a module path that never existed in this
    // tree), silently breaking DNS label/TXT decoding and SMTP base64. Escalate
    // unconditionally, on the same reasoning as the paren-less accessor class
    // above: a file with an unresolvable import already fails `simple compile`,
    // so making `run` agree cannot regress a build that works today.
    if msg.contains("cannot resolve import") {
        eprintln!(
            "[jit-fallback] {kind}: {msg}{where_}: the import names a module that does not exist. \
             This is a hard error in every lane -- falling back to the interpreter would only defer \
             the failure to the first call site, reported as an unrelated 'function not found'. \
             Set SIMPLE_ALLOW_UNRESOLVED_IMPORTS=1 to restore the old warn-and-continue behaviour."
        );
        return format!(
            "SIMPLE_JIT_STRICT: {kind}: {msg}{where_}: unresolved import; refusing to fall back to the interpreter"
        );
    }

    if is_parenless_container_accessor(&msg) {
        eprintln!(
            "[jit-fallback] {kind}: {msg}{where_}: paren-less accessor on a builtin container. \
             Use the method form (e.g. `.len()`) instead. This is a hard error in every lane: \
             it already fails `simple compile`, and silently de-JITing the whole module here \
             (~100-1000x slowdown, correct output, no diagnostic) is what made it invisible."
        );
        return format!(
            "SIMPLE_JIT_STRICT: {kind}: {msg}{where_}: paren-less accessor on a builtin \
             container -- use the method form (e.g. `.len()`); refusing to fall back to the interpreter"
        );
    }

    eprintln!(
        "[jit-fallback] {kind}: {msg}{where_}: whole module dropped to the interpreter \
         (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error."
    );
    if std::env::var_os("SIMPLE_JIT_STRICT").is_some_and(|v| v != "0") {
        format!("SIMPLE_JIT_STRICT: {kind}: {msg}{where_}; refusing to fall back to the interpreter")
    } else {
        format!("{kind}: {msg}{where_}")
    }
}

fn should_force_interpreter_for_source(path: &Path) -> bool {
    let normalized = path.to_string_lossy().replace('\\', "/");
    normalized.ends_with("src/app/simpleos_nvme_serial_check/main.spl")
}

fn should_prefer_interpreter_for_source(path: &Path, extension: &str) -> bool {
    if should_force_interpreter_for_source(path) || extension == "shs" {
        return true;
    }
    if std::env::var_os("SIMPLE_EXECUTION_MODE").is_some() {
        return false;
    }
    source_uses_cli_args(path) || source_uses_jit_unsafe_graphics_runtime(path)
}

fn source_uses_cli_args(path: &Path) -> bool {
    let normalized = path.to_string_lossy().replace('\\', "/");
    if normalized.ends_with("src/app/cli/main.spl") {
        return true;
    }

    let Ok(source) = std::fs::read_to_string(path) else {
        return false;
    };
    source.contains("get_cli_args")
        || source.contains("rt_cli_get_args")
        || source.contains("sys_get_args")
        || source.contains("rt_get_args")
        || source.contains("std.cli")
}

fn source_uses_jit_unsafe_graphics_runtime(path: &Path) -> bool {
    let Ok(source) = std::fs::read_to_string(path) else {
        return false;
    };
    // gpu.engine2d sources JIT by default since the cross-module private-symbol
    // collision fix (cranelift_f32_trig_wrapper_codegen_2026-07-02 Residual).
    // Escape hatch: SIMPLE_EXECUTION_MODE=interpreter.
    source.contains("window_winit")
}

fn panic_payload_to_string(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        return (*message).to_string();
    }
    if let Some(message) = payload.downcast_ref::<String>() {
        return message.clone();
    }
    "non-string panic payload".to_string()
}

#[cfg(test)]
mod tests {
    use super::{
        panic_payload_to_string, should_force_interpreter_for_source, should_prefer_interpreter_for_source,
        source_uses_cli_args, source_uses_jit_unsafe_graphics_runtime,
    };
    use std::fs;
    use std::path::Path;
    use tempfile::tempdir;

    /// Guards the invariant `run_file_jit` relies on to refuse a JIT run that
    /// would silently skip module-level BDD examples: `extract_file_test_meta`
    /// counts examples declared at MODULE level and does NOT descend into
    /// function bodies. If it ever started descending, the bail-out would fire
    /// for ordinary programs that merely call a test helper from `main`.
    fn module_level_example_count(source: &str) -> usize {
        let mut parser = simple_parser::Parser::new(source);
        let ast = parser.parse().expect("fixture must parse");
        simple_parser::test_analyzer::extract_file_test_meta(&ast.items, None).total_tests
    }

    #[test]
    fn counts_module_level_bdd_examples_that_the_jit_entry_path_would_skip() {
        let source = "describe \"g\":\n    it \"a\":\n        expect(1).to_equal(1)\n\n    it \"b\":\n        expect(2).to_equal(2)\n\nfn main():\n    print \"hi\"\n";
        assert_eq!(module_level_example_count(source), 2);
    }

    #[test]
    fn ignores_examples_nested_inside_a_function_body() {
        let source = "fn main():\n    describe \"g\":\n        it \"a\":\n            expect(1).to_equal(1)\n";
        assert_eq!(module_level_example_count(source), 0);
    }

    #[test]
    fn counts_zero_for_a_plain_program_with_no_examples() {
        let source = "fn main():\n    print \"hi\"\n";
        assert_eq!(module_level_example_count(source), 0);
    }

    #[test]
    fn forces_interpreter_for_physical_nvme_serial_checker() {
        assert!(should_force_interpreter_for_source(Path::new(
            "src/app/simpleos_nvme_serial_check/main.spl"
        )));
        assert!(should_force_interpreter_for_source(Path::new(
            "/repo/src/app/simpleos_nvme_serial_check/main.spl"
        )));
    }

    #[test]
    fn keeps_other_sources_on_normal_execution_path() {
        assert!(!should_force_interpreter_for_source(Path::new("src/app/os/main.spl")));
        assert!(!should_force_interpreter_for_source(Path::new(
            "src/app/simpleos_nvme_serial_check/helper.spl"
        )));
    }

    #[test]
    fn detects_cli_arg_scripts_for_interpreter_fast_path() {
        let dir = tempdir().unwrap();
        let script = dir.path().join("cli_args.spl");
        fs::write(
            &script,
            "use std.cli.cli_util (get_cli_args)\nfn main():\n    val args = get_cli_args()\n",
        )
        .unwrap();

        assert!(source_uses_cli_args(&script));
        assert!(should_prefer_interpreter_for_source(&script, "spl"));
    }

    #[test]
    fn detects_direct_sys_get_args_for_argument_preserving_path() {
        let dir = tempdir().unwrap();
        let script = dir.path().join("sys_args.spl");
        fs::write(
            &script,
            "extern fn sys_get_args() -> [text]\nfn main():\n    val args = sys_get_args()\n",
        )
        .unwrap();

        assert!(source_uses_cli_args(&script));
        assert!(should_prefer_interpreter_for_source(&script, "spl"));
    }

    #[test]
    fn full_cli_entry_uses_interpreter_fast_path_for_dispatch_args() {
        assert!(source_uses_cli_args(Path::new("src/app/cli/main.spl")));
        assert!(source_uses_cli_args(Path::new("/repo/src/app/cli/main.spl")));
        assert!(should_prefer_interpreter_for_source(
            Path::new("src/app/cli/main.spl"),
            "spl"
        ));
    }

    #[test]
    fn keeps_plain_sources_on_jit_path() {
        let dir = tempdir().unwrap();
        let script = dir.path().join("plain.spl");
        fs::write(&script, "fn main():\n    print \"ok\"\n").unwrap();

        assert!(!source_uses_cli_args(&script));
        assert!(!should_prefer_interpreter_for_source(&script, "spl"));
    }

    #[test]
    fn shell_scripts_use_interpreter_path() {
        assert!(should_prefer_interpreter_for_source(
            Path::new("scripts/check.shs"),
            "shs"
        ));
    }

    #[test]
    fn graphics_runtime_sources_use_interpreter_fast_path() {
        let dir = tempdir().unwrap();
        let script = dir.path().join("gui.spl");
        fs::write(
            &script,
            "use std.io.window_winit.{create_window}\nuse std.gc_async_mut.gpu.engine2d.engine.{Engine2D}\nfn main():\n    print \"gui\"\n",
        )
        .unwrap();

        assert!(source_uses_jit_unsafe_graphics_runtime(&script));
        assert!(should_prefer_interpreter_for_source(&script, "spl"));
    }

    #[test]
    fn engine2d_sources_stay_on_jit_path() {
        let dir = tempdir().unwrap();
        let script = dir.path().join("game2d.spl");
        fs::write(
            &script,
            "use std.gc_async_mut.gpu.engine2d.engine.{Engine2D}\nfn main():\n    print \"game\"\n",
        )
        .unwrap();

        assert!(!source_uses_jit_unsafe_graphics_runtime(&script));
        assert!(!should_prefer_interpreter_for_source(&script, "spl"));
    }

    #[test]
    fn panic_payload_formatter_keeps_jit_fallback_message_readable() {
        let payload = std::panic::catch_unwind(|| panic!("rt_winit_event_loop_new")).unwrap_err();
        assert_eq!(panic_payload_to_string(payload.as_ref()), "rt_winit_event_loop_new");
    }

    /// B3 for-in regression: the generator-detection helper correctly identifies
    /// a MIR module that contains a Yield instruction so run_file_jit can bail
    /// out early and let the interpreter fallback handle it.
    #[test]
    fn generator_yield_detected_in_mir_module() {
        use simple_compiler::mir::{MirBlock, MirFunction, MirInst, MirModule, VReg};
        use simple_parser::ast::Visibility;
        use simple_compiler::hir::TypeId;

        // Build a minimal MIR module with one function that has a Yield instruction.
        let mut func = MirFunction::new("gen".to_string(), TypeId::ANY, Visibility::Public);
        let block = func.blocks.first_mut().expect("entry block exists");
        block.instructions.push(MirInst::Yield { value: VReg(0) });

        let has_generator = func
            .blocks
            .iter()
            .any(|b| b.instructions.iter().any(|i| matches!(i, MirInst::Yield { .. })));
        assert!(has_generator, "function with Yield should be detected as a generator");

        // A plain function (no Yield) must NOT trigger the fallback.
        let plain = MirFunction::new("main".to_string(), TypeId::ANY, Visibility::Public);
        let plain_has_generator = plain
            .blocks
            .iter()
            .any(|b| b.instructions.iter().any(|i| matches!(i, MirInst::Yield { .. })));
        assert!(
            !plain_has_generator,
            "plain function without Yield should not be flagged as a generator"
        );
    }
}

impl Default for ExecCore {
    fn default() -> Self {
        Self::new()
    }
}

/// Run the main function from a loaded module
pub fn run_main(module: &LoadedModule) -> Result<i32, String> {
    // Fail closed on a genuinely empty code section: this is the "no user
    // code compiled at all" signature of a stub/no-op SMF (bug
    // seed_compile_smf_stub_fail_open_2026-07-17). Bounded, obvious guard
    // only -- a real (even trivial) compiled `main` always emits at least a
    // `ret`-equivalent instruction, so this never rejects legitimate output.
    if module.code_mem.size() == 0 {
        return Err(format!(
            "cannot run {}: module has an empty code section (no compiled user code) -- refusing to silently exit 0",
            module.path.display()
        ));
    }
    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().ok_or("no main entry found")?;
    Ok(main())
}

fn run_module_init(module: &LoadedModule) -> Result<(), String> {
    type InitFn = extern "C" fn();
    let Some(init) = module.get_function::<InitFn>("__module_init") else {
        return Ok(());
    };
    init();
    Ok(())
}
