//! Interpreter interface for running Simple code programmatically
//!
//! This module provides a clean API for embedding Simple as a scripting language,
//! system testing, and REPL implementation.
//!
//! The Interpreter uses Runner internally and adds I/O capture and configuration.

use simple_runtime::gc::GcRuntime;

use crate::Runner;

/// Specifies which execution mode to use when running code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RunningType {
    /// Run code using the interpreter (default)
    #[default]
    Interpreter,
    /// Compile to SMF then run the compiled binary
    Compiler,
    /// Run both interpreter and compiler, compare results
    Both,
}

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
    /// If true, compile and run in memory (no disk I/O)
    pub in_memory: bool,
    /// Execution mode: Interpreter (default), Compiler, or Both
    pub running_type: RunningType,
}

/// Interpreter for running Simple code with I/O capture
///
/// Uses Runner internally and adds configuration and I/O capture support.
pub struct Interpreter {
    runner: Runner,
}

impl Interpreter {
    /// Create a new interpreter instance
    pub fn new() -> Self {
        Self {
            runner: Runner::new(),
        }
    }

    /// Create an interpreter that uses the no-GC allocator.
    pub fn new_no_gc() -> Self {
        Self {
            runner: Runner::new_no_gc(),
        }
    }

    /// Run Simple source code with configuration
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    /// * `config` - Execution configuration (args, stdin, timeout, in_memory, running_type)
    ///
    /// # Returns
    /// * `Ok(RunResult)` - Execution result with exit code and captured output
    /// * `Err(String)` - Error message if compilation or execution failed
    pub fn run(&self, code: &str, config: RunConfig) -> Result<RunResult, String> {
        let _ = (&config.args, &config.stdin, config.timeout_ms); // TODO: use when I/O is implemented

        let exit_code = match config.running_type {
            RunningType::Interpreter => {
                if config.in_memory {
                    self.runner.run_source_in_memory(code)?
                } else {
                    self.runner.run_source(code)?
                }
            }
            RunningType::Compiler => {
                if config.in_memory {
                    self.runner.run_source_in_memory_native(code)?
                } else {
                    self.runner.run_source_native(code)?
                }
            }
            RunningType::Both => {
                let interp_result = if config.in_memory {
                    self.runner.run_source_in_memory(code)?
                } else {
                    self.runner.run_source(code)?
                };

                let compiler_result = if config.in_memory {
                    self.runner.run_source_in_memory_native(code)?
                } else {
                    self.runner.run_source_native(code)?
                };

                if interp_result != compiler_result {
                    return Err(format!(
                        "Interpreter and compiler results differ: interpreter={}, compiler={}",
                        interp_result, compiler_result
                    ));
                }
                interp_result
            }
        };

        Ok(RunResult {
            exit_code,
            stdout: String::new(), // TODO: capture when I/O builtins are implemented
            stderr: String::new(),
        })
    }

    /// Run code with just stdin input
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    /// * `stdin` - Standard input content
    pub fn run_with_stdin(&self, code: &str, stdin: &str) -> Result<RunResult, String> {
        self.run(
            code,
            RunConfig {
                stdin: stdin.to_string(),
                ..Default::default()
            },
        )
    }

    /// Run code with no input (simplest form)
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    pub fn run_simple(&self, code: &str) -> Result<RunResult, String> {
        self.run(code, RunConfig::default())
    }

    /// Run code in memory (no disk I/O)
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    pub fn run_in_memory(&self, code: &str) -> Result<RunResult, String> {
        self.run(
            code,
            RunConfig {
                in_memory: true,
                ..Default::default()
            },
        )
    }

    /// Access the underlying Runner for advanced use
    pub fn runner(&self) -> &Runner {
        &self.runner
    }

    /// Access the underlying GC runtime if present.
    pub fn gc(&self) -> Option<&GcRuntime> {
        self.runner.gc_runtime()
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
    interpreter.run(
        code,
        RunConfig {
            args: args.to_vec(),
            stdin: stdin.to_string(),
            ..Default::default()
        },
    )
}

/// Run Simple code using JIT compilation.
///
/// This compiles the code to native machine code and executes it directly,
/// providing better performance than interpretation for compute-intensive code.
///
/// # Arguments
/// * `code` - Simple source code containing a `main` function that returns i64
///
/// # Returns
/// * `Ok(RunResult)` - Execution result with exit code from the main function
/// * `Err(String)` - Error message if compilation or execution failed
///
/// # Example
/// ```
/// use simple_driver::run_jit;
///
/// let result = run_jit("fn main() -> i64:\n    return 42\n").unwrap();
/// assert_eq!(result.exit_code, 42);
/// ```
///
/// # Note
/// JIT compilation requires the code to have a `main` function with the signature
/// `fn main() -> i64`. More complex programs with I/O or GC are not yet supported.
pub fn run_jit(code: &str) -> Result<RunResult, String> {
    use simple_compiler::codegen::JitCompiler;
    use simple_compiler::hir;
    use simple_compiler::mir::lower_to_mir;
    use simple_parser::Parser;

    // Parse source code
    let mut parser = Parser::new(code);
    let ast = parser.parse().map_err(|e| format!("parse error: {}", e))?;

    // Lower to HIR
    let hir_module = hir::lower(&ast).map_err(|e| format!("HIR lowering error: {}", e))?;

    // Lower to MIR
    let mir_module = lower_to_mir(&hir_module).map_err(|e| format!("MIR lowering error: {}", e))?;

    // JIT compile
    let mut jit = JitCompiler::new().map_err(|e| format!("JIT init error: {}", e))?;

    jit.compile_module(&mir_module)
        .map_err(|e| format!("JIT compile error: {}", e))?;

    // Execute main function
    let exit_code = unsafe {
        jit.call_i64_void("main")
            .map_err(|e| format!("JIT execution error: {}", e))?
    };

    Ok(RunResult {
        exit_code: exit_code as i32,
        stdout: String::new(),
        stderr: String::new(),
    })
}
