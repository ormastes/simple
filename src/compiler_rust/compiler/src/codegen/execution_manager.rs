//! ExecutionManager trait for unified JIT execution.
//!
//! This trait abstracts over different JIT backends (Cranelift, LLVM) and
//! provides a common interface for compiling and executing code at runtime.
//! It is designed to be shared between local execution and future remote
//! execution managers.

use crate::mir::MirModule;

/// Result of compiling a module for execution.
#[derive(Debug, Clone)]
pub struct CodeInfo {
    /// Name of the compiled module
    pub name: String,
    /// Entry point function name (typically "main")
    pub entry_point: String,
    /// All symbol names available in the compiled module
    pub symbol_names: Vec<String>,
}

/// Result of executing a function, with captured output.
#[derive(Debug, Clone)]
pub struct ExecutionResult {
    /// Exit code / return value
    pub exit_code: i64,
    /// Captured stdout output
    pub stdout: String,
    /// Captured stderr output
    pub stderr: String,
}

/// Unified interface for JIT execution backends.
///
/// Implementations can wrap Cranelift JIT, LLVM JIT, or remote execution.
/// The trait is designed to be object-safe for dynamic dispatch.
pub trait ExecutionManager: Send {
    /// Compile a MIR module, making its functions available for execution.
    fn compile_module(&mut self, mir: &MirModule) -> Result<CodeInfo, String>;

    /// Execute a compiled function by name with the given i64 arguments.
    fn execute(&self, name: &str, args: &[i64]) -> Result<i64, String>;

    /// Execute a compiled function and capture stdout/stderr.
    fn execute_captured(&self, name: &str, args: &[i64]) -> Result<ExecutionResult, String>;

    /// Check if a function has been compiled and is available.
    fn has_function(&self, name: &str) -> bool;

    /// Get the name of the underlying backend (e.g., "cranelift-jit", "llvm-jit").
    fn backend_name(&self) -> &str;

    /// Release all compiled code and free resources.
    fn cleanup(&mut self);
}
