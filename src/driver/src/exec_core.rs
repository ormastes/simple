//! Common execution core shared between Runner and Interpreter
//!
//! Eliminates duplication of GC setup, compilation, and execution logic.

use std::fs;
use std::path::Path;
use std::sync::Arc;
use tempfile::TempDir;

use simple_compiler::CompilerPipeline;
use simple_common::gc::GcAllocator;
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

    /// Compile source string to SMF file
    pub fn compile_source(&self, source: &str, out: &Path) -> Result<(), String> {
        let dir = out.parent().map(Path::to_path_buf).unwrap_or_else(|| std::env::temp_dir());
        let src_path = dir.join("tmp.spl");
        fs::write(&src_path, source).map_err(|e| format!("write temp source: {e}"))?;

        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone())
            .map_err(|e| format!("{e:?}"))?;
        compiler.compile(&src_path, out)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile file to SMF
    pub fn compile_file(&self, path: &Path, out: &Path) -> Result<(), String> {
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone())
            .map_err(|e| format!("{e:?}"))?;
        compiler.compile(path, out)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Load an SMF module
    pub fn load_module(&self, path: &Path) -> Result<LoadedModule, String> {
        self.loader.load(path).map_err(|e| format!("load failed: {e}"))
    }

    /// Compile and run source string, return exit code
    pub fn run_source(&self, source: &str) -> Result<i32, String> {
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let out = tmp.path().join("module.smf");

        self.compile_source(source, &out)?;
        let module = self.load_module(&out)?;
        let exit = run_main(&module)?;
        self.collect_gc();
        Ok(exit)
    }

    /// Compile and run file, return exit code
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        let out_path = path.with_extension("smf");
        self.compile_file(path, &out_path)?;
        let module = self.load_module(&out_path)?;
        let exit = run_main(&module)?;
        self.collect_gc();
        Ok(exit)
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
