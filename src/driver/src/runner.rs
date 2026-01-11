use std::path::Path;
use std::sync::Arc;

use simple_common::target::Target;
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

    /// Run a Simple source file using the interpreter.
    ///
    /// This method loads the file with proper import resolution and runs it
    /// through the interpreter, which supports all language features including
    /// associated function calls like `Type::method()`.
    #[instrument(skip(self), fields(path = %path.display()))]
    pub fn run_file_interpreted(&self, path: &Path) -> Result<i32, String> {
        self.core.run_file_interpreted(path)
    }

    /// Run a Simple source file using the interpreter with command-line arguments.
    ///
    /// The args are made available to the Simple program via `sys_get_args()`.
    #[instrument(skip(self, args), fields(path = %path.display()))]
    pub fn run_file_interpreted_with_args(
        &self,
        path: &Path,
        args: Vec<String>,
    ) -> Result<i32, String> {
        self.core.run_file_interpreted_with_args(path, args)
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

    /// Compile source to an SMF with options (LLM-friendly #885-887)
    #[instrument(skip(self, source, options))]
    pub fn compile_to_smf_with_options(
        &self,
        source: &str,
        out: &Path,
        options: &crate::CompileOptions,
    ) -> Result<(), String> {
        self.core.compile_source_with_options(source, out, options)
    }

    /// Compile source file to an SMF at the given path with compile options.
    /// This version takes a file path which enables module resolution for imports.
    #[instrument(skip(self, source_path))]
    pub fn compile_file_to_smf_with_options(
        &self,
        source_path: &Path,
        out: &Path,
        options: &crate::CompileOptions,
    ) -> Result<(), String> {
        self.core
            .compile_file_with_options(source_path, out, options)
    }

    /// Compile source to an SMF at the given path for a specific target architecture.
    /// This enables cross-compilation to different architectures.
    #[instrument(skip(self, source))]
    pub fn compile_to_smf_for_target(
        &self,
        source: &str,
        out: &Path,
        target: Target,
    ) -> Result<(), String> {
        self.core.compile_source_for_target(source, out, target)
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

    /// Compile to WebAssembly and run with Wasmer runtime (WASI environment).
    #[cfg(feature = "wasm")]
    #[instrument(skip(self, source))]
    pub fn run_source_wasm(&self, source: &str) -> Result<i32, String> {
        self.core.run_source_wasm(source)
    }
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}
