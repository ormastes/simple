//! Common execution core shared between Runner and Interpreter
//!
//! Eliminates duplication of GC setup, compilation, loading, and execution logic.

use std::fs;
use std::path::Path;
use std::sync::Arc;
use tempfile::TempDir;

use simple_common::gc::{GcAllocator, MemoryLimitConfig};
use simple_common::target::Target;
use simple_compiler::CompilerPipeline;
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
}

impl ExecutionMode {
    /// Parse from string (CLI flag or env var).
    pub fn from_str(s: &str) -> Self {
        match s {
            "interpret" | "interpreter" => ExecutionMode::Interpret,
            "cranelift" => ExecutionMode::CraneliftJit,
            "llvm" => ExecutionMode::LlvmJit,
            "jit" | "auto" | _ => ExecutionMode::Jit,
        }
    }

    /// Check if this mode uses JIT.
    pub fn is_jit(&self) -> bool {
        !matches!(self, ExecutionMode::Interpret)
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
    pub fn with_gc_and_provider(gc: GcRuntime, provider: Arc<dyn RuntimeSymbolProvider>) -> Self {
        let gc = Arc::new(gc);
        // Check SIMPLE_EXECUTION_MODE env var for default mode
        let mode = std::env::var("SIMPLE_EXECUTION_MODE")
            .map(|s| ExecutionMode::from_str(&s))
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

        // Display hints to stderr
        for hint in hints {
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

        compiler
            .compile(path, out)
            .map_err(|e| format!("compile failed ({}): {e}", path.display()))
    }

    // =========================================================================
    // Loading methods
    // =========================================================================

    /// Load an SMF module from file
    pub fn load_module(&self, path: &Path) -> Result<LoadedModule, String> {
        self.loader.load(path).map_err(|e| format!("load failed: {e}"))
    }

    /// Load an SMF module from memory buffer
    pub fn load_module_from_memory(&self, bytes: &[u8]) -> Result<LoadedModule, String> {
        self.loader
            .load_from_memory(bytes)
            .map_err(|e| format!("load failed: {e}"))
    }

    // =========================================================================
    // Unified execution helper (reduces duplication)
    // =========================================================================

    /// Execute a loaded module and collect GC afterward
    fn execute_and_gc(&self, module: &LoadedModule) -> Result<i32, String> {
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
    /// Uses JIT compilation for proper symbol resolution of runtime FFI functions.
    pub fn run_source_native(&self, source: &str) -> Result<i32, String> {
        // Delegate to in-memory version since JIT doesn't need disk I/O
        self.run_source_in_memory_native(source)
    }

    /// Compile using native codegen and run source string in memory (no disk I/O)
    ///
    /// Uses JIT compilation for proper symbol resolution of runtime FFI functions.
    /// Falls back to interpreter for code without explicit `fn main()`.
    pub fn run_source_in_memory_native(&self, source: &str) -> Result<i32, String> {
        use simple_compiler::codegen::JitCompiler;
        use simple_compiler::hir;
        use simple_compiler::interpreter::evaluate_module;
        use simple_compiler::mir::lower_to_mir;
        use simple_parser::Parser;

        // Parse source code
        let mut parser = Parser::new(source);
        let parse_result = parser.parse();

        // Display error hints (even if parsing failed)
        self.display_error_hints(&parser, source);

        // Now check if parsing succeeded
        let ast = parse_result.map_err(|e| format!("parse error: {}", e))?;

        // Lower to HIR
        let hir_module = hir::lower(&ast).map_err(|e| format!("HIR lowering error: {}", e))?;

        // Lower to MIR
        let mir_module = lower_to_mir(&hir_module).map_err(|e| format!("MIR lowering error: {}", e))?;

        // Check if we have a proper main function
        let has_main_function = mir_module.functions.iter().any(|f| f.name == "main");

        if !has_main_function {
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

    /// Compile to WebAssembly and run with Wasmer runtime (WASI environment)
    #[cfg(feature = "wasm")]
    pub fn run_source_wasm(&self, source: &str) -> Result<i32, String> {
        use simple_common::target::{Target, TargetArch, WasmRuntime};
        use simple_wasm_runtime::{WasiConfig, WasmRunner};

        // Compile to wasm32-wasi
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Wasi);
        let wasm_bytes = self.compile_to_memory_for_target(source, target)?;

        // Write to temp file (WasmRunner expects a file path)
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let wasm_path = tmp.path().join("module.wasm");
        fs::write(&wasm_path, wasm_bytes).map_err(|e| format!("write wasm: {e}"))?;

        // Create WasmRunner with WASI configuration
        let config = WasiConfig::new();
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

    /// Run a file, auto-detecting type by extension (.spl or .smf).
    ///
    /// Dispatches to JIT or interpreter based on `execution_mode`.
    /// When in JIT mode, falls back to interpreter on JIT failure.
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");

        match extension {
            "smf" => self.run_smf(path),
            "spl" | "simple" | "sscript" | "" => {
                if self.execution_mode.is_jit() {
                    // Try JIT first, fall back to interpreter on failure
                    match self.run_file_jit(path) {
                        Ok(exit_code) => Ok(exit_code),
                        Err(jit_err) => {
                            eprintln!(
                                "[INFO] JIT compilation failed, falling back to interpreter: {}",
                                jit_err
                            );
                            self.run_file_interpreted(path)
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
    /// Parses → HIR → MIR → JIT compile → execute.
    /// Falls back to interpreter for code without `fn main()`.
    pub fn run_file_jit(&self, path: &Path) -> Result<i32, String> {
        use simple_compiler::codegen::{ExecutionManager, LocalExecutionManager, JitBackend};
        use simple_compiler::hir;
        use simple_compiler::interpreter::evaluate_module;
        use simple_compiler::mir::lower_to_mir;

        // Read and parse source
        let source = std::fs::read_to_string(path).map_err(|e| format!("failed to read {}: {}", path.display(), e))?;
        let mut parser = Parser::new(&source);
        let parse_result = parser.parse();
        self.display_error_hints(&parser, &source);
        let ast = parse_result.map_err(|e| format!("parse error: {}", e))?;

        // Lower to HIR
        let hir_module = hir::lower(&ast).map_err(|e| format!("HIR lowering error: {}", e))?;

        // Lower to MIR
        let mir_module = lower_to_mir(&hir_module).map_err(|e| format!("MIR lowering error: {}", e))?;

        // Check for main function
        let has_main = mir_module.functions.iter().any(|f| f.name == "main");

        if !has_main {
            // No main function - use interpreter for module-level code
            let exit_code = evaluate_module(&ast.items).map_err(|e| format!("{}", e))?;
            self.collect_gc();
            return Ok(exit_code);
        }

        // Select JIT backend based on execution mode
        let jit_backend = match self.execution_mode {
            ExecutionMode::CraneliftJit => JitBackend::Cranelift,
            ExecutionMode::LlvmJit => JitBackend::Llvm,
            _ => JitBackend::Auto,
        };

        // Create execution manager and compile
        let mut em = LocalExecutionManager::with_provider(jit_backend, self.symbol_provider.clone())?;

        em.compile_module(&mir_module)?;

        // Execute main
        let exit_code = em.execute("main", &[])?;
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

        // Parse source to collect error hints
        let source = std::fs::read_to_string(path).map_err(|e| format!("failed to read {}: {}", path.display(), e))?;
        let mut parser = Parser::new(&source);
        let parse_result = parser.parse();

        // Display error hints (even if parsing failed)
        self.display_error_hints(&parser, &source);

        // Now check if parsing succeeded
        let _ast = parse_result.map_err(|e| format!("parse error: {}", e))?;

        // Set interpreter arguments
        set_interpreter_args(args);

        // Set current file for module resolution
        set_current_file(Some(path.to_path_buf()));

        let module =
            load_module_with_imports(path, &mut HashSet::new()).map_err(|e| format!("compile failed: {}", e))?;

        let exit_code = evaluate_module(&module.items).map_err(|e| format!("{}", e))?;

        // Clear current file after evaluation
        set_current_file(None);

        self.collect_gc();
        Ok(exit_code)
    }
}

impl Default for ExecCore {
    fn default() -> Self {
        Self::new()
    }
}

/// Run the main function from a loaded module
pub fn run_main(module: &LoadedModule) -> Result<i32, String> {
    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().ok_or("no main entry found")?;
    Ok(main())
}
