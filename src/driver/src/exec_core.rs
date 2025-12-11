//! Common execution core shared between Runner and Interpreter
//!
//! Eliminates duplication of GC setup, compilation, loading, and execution logic.

use std::fs;
use std::path::Path;
use std::sync::Arc;
use tempfile::TempDir;

use simple_common::gc::GcAllocator;
use simple_compiler::CompilerPipeline;
use simple_loader::loader::ModuleLoader as SmfLoader;
use simple_loader::LoadedModule;
use simple_runtime::gc::GcRuntime;
use simple_runtime::NoGcAllocator;

/// Core execution engine for Simple code
/// Handles GC allocation, compilation, loading, and execution
pub struct ExecCore {
    pub loader: SmfLoader,
    pub gc_alloc: Arc<dyn GcAllocator>,
    pub gc_runtime: Option<Arc<GcRuntime>>,
}

impl ExecCore {
    /// Create with a GC runtime
    pub fn with_gc(gc: GcRuntime) -> Self {
        let gc = Arc::new(gc);
        Self {
            loader: SmfLoader::new(),
            gc_alloc: gc.clone(),
            gc_runtime: Some(gc),
        }
    }

    /// Create with default GC runtime
    pub fn new() -> Self {
        Self::with_gc(GcRuntime::new())
    }

    /// Create without GC (uses NoGcAllocator)
    pub fn new_no_gc() -> Self {
        Self {
            loader: SmfLoader::new(),
            gc_alloc: Arc::new(NoGcAllocator::new()),
            gc_runtime: None,
        }
    }

    /// Create with verbose GC logging
    pub fn new_with_gc_logging() -> Self {
        Self::with_gc(GcRuntime::verbose_stdout())
    }

    /// Trigger post-run GC collection
    pub fn collect_gc(&self) {
        if let Some(gc) = &self.gc_runtime {
            let _ = gc.collect("post-run");
        } else {
            self.gc_alloc.collect();
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

    /// Compile source string to SMF bytes in memory (no disk I/O)
    pub fn compile_to_memory(&self, source: &str) -> Result<Vec<u8>, String> {
        let mut compiler =
            CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile_source_to_memory(source)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile source string to SMF bytes using native codegen (HIR → MIR → Cranelift)
    pub fn compile_to_memory_native(&self, source: &str) -> Result<Vec<u8>, String> {
        let mut compiler =
            CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile_source_to_memory_native(source)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile file to SMF
    pub fn compile_file(&self, path: &Path, out: &Path) -> Result<(), String> {
        let mut compiler =
            CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile(path, out)
            .map_err(|e| format!("compile failed: {e}"))
    }

    // =========================================================================
    // Loading methods
    // =========================================================================

    /// Load an SMF module from file
    pub fn load_module(&self, path: &Path) -> Result<LoadedModule, String> {
        self.loader
            .load(path)
            .map_err(|e| format!("load failed: {e}"))
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
    pub fn run_source_native(&self, source: &str) -> Result<i32, String> {
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let out = tmp.path().join("module.smf");
        let smf_bytes = self.compile_to_memory_native(source)?;
        fs::write(&out, smf_bytes).map_err(|e| format!("write smf: {e}"))?;
        let module = self.load_module(&out)?;
        self.execute_and_gc(&module)
    }

    /// Compile using native codegen and run source string in memory (no disk I/O)
    pub fn run_source_in_memory_native(&self, source: &str) -> Result<i32, String> {
        let smf_bytes = self.compile_to_memory_native(source)?;
        let module = self.load_module_from_memory(&smf_bytes)?;
        self.execute_and_gc(&module)
    }

    /// Run SMF from memory buffer
    pub fn run_smf_from_memory(&self, bytes: &[u8]) -> Result<i32, String> {
        let module = self.load_module_from_memory(bytes)?;
        self.execute_and_gc(&module)
    }

    /// Run a pre-compiled SMF file directly
    pub fn run_smf(&self, path: &Path) -> Result<i32, String> {
        let module = self.load_module(path)?;
        self.execute_and_gc(&module)
    }

    /// Run a file, auto-detecting type by extension (.spl or .smf)
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");

        match extension {
            "smf" => self.run_smf(path),
            "spl" | "" => {
                let out_path = path.with_extension("smf");
                self.compile_file(path, &out_path)?;
                let module = self.load_module(&out_path)?;
                self.execute_and_gc(&module)
            }
            other => Err(format!(
                "unsupported file extension '.{}': expected '.spl' or '.smf'",
                other
            )),
        }
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
