//! Interpreter interface for running Simple code programmatically
//!
//! This module provides a clean API for embedding Simple as a scripting language,
//! system testing, and REPL implementation.

use simple_runtime::gc::GcRuntime;

use crate::exec_core::ExecCore;

/// Result of running Simple code
#[derive(Debug, Clone, Default)]
pub struct RunResult {
    /// Program exit code (from main return value)
    pub exit_code: i32,
    /// Captured stdout output (placeholder for future I/O support)
    pub stdout: String,
    /// Captured stderr output (placeholder for future I/O support)
    pub stderr: String,
}

/// Configuration for running code
#[derive(Debug, Clone, Default)]
pub struct RunConfig {
    /// Command-line arguments passed to the program
    pub args: Vec<String>,
    /// Standard input content
    pub stdin: String,
    /// Timeout in milliseconds (0 = no timeout)
    pub timeout_ms: u64,
}

/// Interpreter for running Simple code with I/O capture
pub struct Interpreter {
    core: ExecCore,
}

impl Interpreter {
    /// Create a new interpreter instance
    pub fn new() -> Self {
        Self { core: ExecCore::new() }
    }

    /// Create an interpreter that uses the no-GC allocator.
    pub fn new_no_gc() -> Self {
        Self { core: ExecCore::new_no_gc() }
    }

    /// Run Simple source code with configuration
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    /// * `config` - Execution configuration (args, stdin, timeout)
    ///
    /// # Returns
    /// * `Ok(RunResult)` - Execution result with exit code and captured output
    /// * `Err(String)` - Error message if compilation or execution failed
    pub fn run(&self, code: &str, config: RunConfig) -> Result<RunResult, String> {
        let _ = config; // TODO: use args, stdin, timeout when I/O is implemented

        let exit_code = self.core.run_source(code)?;

        Ok(RunResult {
            exit_code,
            stdout: String::new(),  // TODO: capture when I/O builtins are implemented
            stderr: String::new(),
        })
    }

    /// Run code with just stdin input
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    /// * `stdin` - Standard input content
    pub fn run_with_stdin(&self, code: &str, stdin: &str) -> Result<RunResult, String> {
        self.run(code, RunConfig {
            stdin: stdin.to_string(),
            ..Default::default()
        })
    }

    /// Run code with no input (simplest form)
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    pub fn run_simple(&self, code: &str) -> Result<RunResult, String> {
        self.run(code, RunConfig::default())
    }

    /// Access the underlying GC runtime if present.
    pub fn gc(&self) -> Option<&GcRuntime> {
        self.core.gc_runtime.as_deref()
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience function: Run Simple code and return result
///
/// This is the main interface function for embedding Simple as a scripting language.
///
/// # Arguments
/// * `code` - Simple source code to run
/// * `args` - Command-line arguments passed to the program
/// * `stdin` - Standard input content
///
/// # Returns
/// * `Ok(RunResult)` - Execution result with exit code and captured output
/// * `Err(String)` - Error message if compilation or execution failed
///
/// # Example
/// ```
/// use simple_driver::run_code;
///
/// let result = run_code("main = 42", &[], "").unwrap();
/// assert_eq!(result.exit_code, 42);
/// ```
pub fn run_code(code: &str, args: &[String], stdin: &str) -> Result<RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(code, RunConfig {
        args: args.to_vec(),
        stdin: stdin.to_string(),
        timeout_ms: 0,
    })
}
