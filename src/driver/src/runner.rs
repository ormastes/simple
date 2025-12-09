use std::path::Path;
use std::sync::Arc;

use simple_runtime::gc::GcRuntime;
use tracing::instrument;

use crate::exec_core::ExecCore;

/// Runner that compiles Simple source into an SMF file and executes it.
///
/// For now, compilation is a stub that emits a minimal executable SMF with a `main` that returns 0.
pub struct Runner {
    core: ExecCore,
}

impl Runner {
    pub fn new() -> Self {
        Self { core: ExecCore::new() }
    }

    pub fn with_gc_runtime(gc: GcRuntime) -> Self {
        Self { core: ExecCore::with_gc(gc) }
    }

    pub fn new_no_gc() -> Self {
        Self { core: ExecCore::new_no_gc() }
    }

    /// Create a runner that logs GC events to stdout.
    pub fn new_with_gc_logging() -> Self {
        Self { core: ExecCore::new_with_gc_logging() }
    }

    /// Access the underlying GC runtime (for tests and diagnostics).
    pub fn gc(&self) -> Arc<GcRuntime> {
        Arc::clone(self.core.gc_runtime.as_ref().expect("GC runtime available"))
    }

    /// Run a Simple source file from disk.
    #[instrument(skip(self), fields(path = %path.display()))]
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        self.core.run_file(path)
    }

    /// Compile source to an SMF at the given path.
    #[instrument(skip(self, source))]
    pub fn compile_to_smf(&self, source: &str, out: &Path) -> Result<(), String> {
        self.core.compile_source(source, out)
    }

    /// Compile and run a source string, returning the program exit code.
    #[instrument(skip(self, source))]
    pub fn run_source(&self, source: &str) -> Result<i32, String> {
        self.core.run_source(source)
    }
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}
