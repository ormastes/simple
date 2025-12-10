use std::path::Path;
use std::sync::Arc;

use simple_runtime::gc::GcRuntime;
use tracing::instrument;

use crate::exec_core::ExecCore;

/// Runner that compiles Simple source into an SMF file and executes it.
///
/// The compiler uses the interpreter to evaluate the program, then emits an SMF
/// binary containing native code that returns the computed result.
pub struct Runner {
    core: ExecCore,
}

impl Runner {
    pub fn new() -> Self {
        Self {
            core: ExecCore::new(),
        }
    }

    pub fn with_gc_runtime(gc: GcRuntime) -> Self {
        Self {
            core: ExecCore::with_gc(gc),
        }
    }

    pub fn new_no_gc() -> Self {
        Self {
            core: ExecCore::new_no_gc(),
        }
    }

    /// Create a runner that logs GC events to stdout.
    pub fn new_with_gc_logging() -> Self {
        Self {
            core: ExecCore::new_with_gc_logging(),
        }
    }

    /// Access the underlying GC runtime (for tests and diagnostics).
    pub fn gc(&self) -> Arc<GcRuntime> {
        Arc::clone(self.core.gc_runtime.as_ref().expect("GC runtime available"))
    }

    /// Access the underlying GC runtime if present.
    pub fn gc_runtime(&self) -> Option<&GcRuntime> {
        self.core.gc_runtime.as_deref()
    }

    /// Run a Simple source file from disk.
    /// Auto-detects file type by extension: .spl (source) or .smf (binary).
    #[instrument(skip(self), fields(path = %path.display()))]
    pub fn run_file(&self, path: &Path) -> Result<i32, String> {
        self.core.run_file(path)
    }

    /// Run a pre-compiled SMF file directly.
    #[instrument(skip(self), fields(path = %path.display()))]
    pub fn run_smf(&self, path: &Path) -> Result<i32, String> {
        self.core.run_smf(path)
    }

    /// Run SMF from memory buffer.
    #[instrument(skip(self, bytes))]
    pub fn run_smf_from_memory(&self, bytes: &[u8]) -> Result<i32, String> {
        self.core.run_smf_from_memory(bytes)
    }

    /// Compile source to an SMF at the given path.
    #[instrument(skip(self, source))]
    pub fn compile_to_smf(&self, source: &str, out: &Path) -> Result<(), String> {
        self.core.compile_source(source, out)
    }

    /// Compile source to SMF bytes in memory (no disk I/O).
    #[instrument(skip(self, source))]
    pub fn compile_to_memory(&self, source: &str) -> Result<Vec<u8>, String> {
        self.core.compile_to_memory(source)
    }

    /// Compile and run a source string, returning the program exit code.
    #[instrument(skip(self, source))]
    pub fn run_source(&self, source: &str) -> Result<i32, String> {
        self.core.run_source(source)
    }

    /// Compile and run source in memory (no disk I/O).
    #[instrument(skip(self, source))]
    pub fn run_source_in_memory(&self, source: &str) -> Result<i32, String> {
        self.core.run_source_in_memory(source)
    }

    /// Compile using native codegen and run a source string, returning the program exit code.
    #[instrument(skip(self, source))]
    pub fn run_source_native(&self, source: &str) -> Result<i32, String> {
        self.core.run_source_native(source)
    }

    /// Compile using native codegen and run source in memory (no disk I/O).
    #[instrument(skip(self, source))]
    pub fn run_source_in_memory_native(&self, source: &str) -> Result<i32, String> {
        self.core.run_source_in_memory_native(source)
    }
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}
