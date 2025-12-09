use std::fs;
use std::path::Path;
use std::sync::Arc;

use simple_loader::loader::ModuleLoader as SmfLoader;
use simple_loader::LoadedModule;
use simple_compiler::CompilerPipeline;
use simple_common::gc::GcAllocator;
use simple_runtime::gc::GcRuntime;
use simple_runtime::memory::no_gc::NoGcAllocator;
use tempfile::TempDir;
use tracing::instrument;

/// Runner that compiles Simple source into an SMF file and executes it.
///
/// For now, compilation is a stub that emits a minimal executable SMF with a `main` that returns 0.
pub struct Runner {
    loader: SmfLoader,
    gc_alloc: Arc<dyn GcAllocator>,
    gc_runtime: Option<Arc<GcRuntime>>,
}

impl Runner {
    pub fn new() -> Self {
        Self::with_gc_runtime(GcRuntime::new())
    }

    pub fn with_gc_runtime(gc: GcRuntime) -> Self {
        let gc = Arc::new(gc);
        Self {
            loader: SmfLoader::new(),
            gc_alloc: gc.clone(),
            gc_runtime: Some(gc),
        }
    }

    pub fn new_no_gc() -> Self {
        let alloc: Arc<dyn GcAllocator> = Arc::new(NoGcAllocator::new());
        Self {
            loader: SmfLoader::new(),
            gc_alloc: alloc,
            gc_runtime: None,
        }
    }

    /// Create a runner that logs GC events to stdout.
    pub fn new_with_gc_logging() -> Self {
        Self::with_gc_runtime(GcRuntime::verbose_stdout())
    }

    /// Access the underlying GC runtime (for tests and diagnostics).
    pub fn gc(&self) -> Arc<GcRuntime> {
        Arc::clone(self.gc_runtime.as_ref().expect("GC runtime available"))
    }

    /// Run a Simple source file from disk.
    #[instrument(skip(self), fields(path = %path.display()))]
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        let out_path = path.with_extension("smf");
        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile(path, &out_path)
            .map_err(|e| format!("compile failed: {e}"))?;
        let module = self
            .loader
            .load(&out_path)
            .map_err(|e| format!("load failed: {e}"))?;
        let exit = run_main(&module)?;
        if let Some(gc) = &self.gc_runtime {
            let _ = gc.collect("post-run");
        } else {
            self.gc_alloc.collect();
        }
        Ok(exit)
    }

    /// Compile source to an SMF at the given path.
    #[instrument(skip(self, source))]
    pub fn compile_to_smf(&self, source: &str, out: &Path) -> Result<(), String> {
        // Write the source to a temporary file for the compiler to consume.
        let dir = out.parent().map(Path::to_path_buf).unwrap_or_else(|| std::env::temp_dir());
        let src_path = dir.join("tmp.spl");
        fs::write(&src_path, source).map_err(|e| format!("write temp source: {e}"))?;

        let mut compiler = CompilerPipeline::with_gc(self.gc_alloc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile(&src_path, out)
            .map_err(|e| format!("compile failed: {e}"))
    }

    /// Compile and run a source string, returning the program exit code.
    #[instrument(skip(self, source))]
    pub fn run_source(&self, source: &str) -> Result<i32, String> {
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let out = tmp.path().join("module.smf");
        self.compile_to_smf(source, &out)
            .map_err(|e| format!("compile failed: {e}"))?;

        let module = self
            .loader
            .load(&out)
            .map_err(|e| format!("load failed: {e}"))?;

        let exit = run_main(&module)?;
        if let Some(gc) = &self.gc_runtime {
            let _ = gc.collect("post-run");
        } else {
            self.gc_alloc.collect();
        }
        Ok(exit)
    }
}

fn run_main(module: &LoadedModule) -> Result<i32, String> {
    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().ok_or("no main entry found")?;
    Ok(main())
}
