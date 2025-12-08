use std::fs;
use std::path::Path;
use std::sync::Arc;

use simple_loader::loader::ModuleLoader as SmfLoader;
use simple_loader::LoadedModule;
use simple_compiler::CompilerPipeline;
use simple_runtime::gc::GcRuntime;
use tempfile::TempDir;
use tracing::instrument;

/// Runner that compiles Simple source into an SMF file and executes it.
///
/// For now, compilation is a stub that emits a minimal executable SMF with a `main` that returns 0.
pub struct Runner {
    loader: SmfLoader,
    gc: Arc<GcRuntime>,
}

impl Runner {
    pub fn new() -> Self {
        Self::with_gc(GcRuntime::new())
    }

    pub fn with_gc(gc: GcRuntime) -> Self {
        Self {
            loader: SmfLoader::new(),
            gc: Arc::new(gc),
        }
    }

    /// Create a runner that logs GC events to stdout.
    pub fn new_with_gc_logging() -> Self {
        Self::with_gc(GcRuntime::verbose_stdout())
    }

    /// Access the underlying GC runtime (for tests and diagnostics).
    pub fn gc(&self) -> Arc<GcRuntime> {
        Arc::clone(&self.gc)
    }

    /// Run a Simple source file from disk.
    #[instrument(skip(self), fields(path = %path.display()))]
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        let out_path = path.with_extension("smf");
        let mut compiler = CompilerPipeline::with_gc(self.gc.clone()).map_err(|e| format!("{e:?}"))?;
        compiler
            .compile(path, &out_path)
            .map_err(|e| format!("compile failed: {e}"))?;
        let module = self
            .loader
            .load(&out_path)
            .map_err(|e| format!("load failed: {e}"))?;
        let exit = run_main(&module)?;
        let _ = self.gc.collect("post-run");
        Ok(exit)
    }

    /// Compile source to an SMF at the given path.
    #[instrument(skip(self, source))]
    pub fn compile_to_smf(&self, source: &str, out: &Path) -> Result<(), String> {
        // Write the source to a temporary file for the compiler to consume.
        let dir = out.parent().map(Path::to_path_buf).unwrap_or_else(|| std::env::temp_dir());
        let src_path = dir.join("tmp.spl");
        fs::write(&src_path, source).map_err(|e| format!("write temp source: {e}"))?;

        let mut compiler = CompilerPipeline::with_gc(self.gc.clone()).map_err(|e| format!("{e:?}"))?;
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
        let _ = self.gc.collect("post-run");
        Ok(exit)
    }
}

fn run_main(module: &LoadedModule) -> Result<i32, String> {
    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().ok_or("no main entry found")?;
    Ok(main())
}
