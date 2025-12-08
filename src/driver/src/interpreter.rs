//! Interpreter interface for running Simple code programmatically
//!
//! This module provides a clean API for embedding Simple as a scripting language,
//! system testing, and REPL implementation.

use std::fs;
use tempfile::TempDir;
use simple_compiler::CompilerPipeline;
use simple_loader::loader::ModuleLoader as SmfLoader;
use simple_loader::LoadedModule;
use simple_runtime::gc::GcRuntime;

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
    loader: SmfLoader,
    gc: GcRuntime,
}

impl Interpreter {
    /// Create a new interpreter instance
    pub fn new() -> Self {
        Self {
            loader: SmfLoader::new(),
            gc: GcRuntime::new(),
        }
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

        // Create temp directory for compilation
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
        let src_path = tmp.path().join("input.spl");
        let out_path = tmp.path().join("output.smf");

        // Write source
        fs::write(&src_path, code).map_err(|e| format!("write source: {e}"))?;

        // Compile
        let mut compiler = CompilerPipeline::new().map_err(|e| format!("{e:?}"))?;
        compiler.compile(&src_path, &out_path)
            .map_err(|e| format!("compile failed: {e}"))?;

        // Load
        let module = self.loader.load(&out_path)
            .map_err(|e| format!("load failed: {e}"))?;

        // Run
        let exit_code = run_main(&module)?;

        // Collect GC
        let _ = self.gc.collect("post-run");

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

    /// Access the underlying GC runtime
    pub fn gc(&self) -> &GcRuntime {
        &self.gc
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

fn run_main(module: &LoadedModule) -> Result<i32, String> {
    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().ok_or("no main entry found")?;
    Ok(main())
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
/// ```ignore
/// use simple_driver::interpreter::run_code;
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
