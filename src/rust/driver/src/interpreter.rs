//! Interpreter interface for running Simple code programmatically
//!
//! This module provides a clean API for embedding Simple as a scripting language,
//! system testing, and REPL implementation.
//!
//! The Interpreter uses Runner internally and adds I/O capture and configuration.

use std::process::Command;
use std::sync::Arc;
use tempfile::TempDir;

use simple_loader::memory::PlatformAllocator;
use simple_loader::{create_executable, Settlement, SettlementConfig};
use simple_parser::error_recovery::ErrorHintLevel;
use simple_parser::Parser;
use simple_runtime::gc::GcRuntime;
use simple_runtime::value::{
    rt_capture_stderr_start, rt_capture_stderr_stop, rt_capture_stdout_start, rt_capture_stdout_stop, rt_clear_stdin,
    rt_set_stdin,
};

use crate::Runner;

/// Specifies which execution mode to use when running code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RunningType {
    /// Run code using the interpreter (default)
    #[default]
    Interpreter,
    /// Compile to native code via JIT and run (in-memory, no SMF)
    Compiler,
    /// AOT compile to SMF file, then load and execute
    CompileAndRun,
    /// Run both interpreter and compiler (JIT), compare results
    Both,
    /// Run all three modes (interpreter, JIT, AOT), compare results
    All,
    /// Compile to WebAssembly and execute with Wasmer runtime
    #[cfg(feature = "wasm")]
    Wasm,
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
    /// If true, capture stdout/stderr instead of printing to terminal
    pub capture_output: bool,
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
        Self { runner: Runner::new() }
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
    /// * `config` - Execution configuration (args, stdin, timeout, in_memory, running_type, capture_output)
    ///
    /// # Returns
    /// * `Ok(RunResult)` - Execution result with exit code and captured output
    /// * `Err(String)` - Error message if compilation or execution failed
    pub fn run(&self, code: &str, config: RunConfig) -> Result<RunResult, String> {
        // NOTE: args/timeout are accepted but not yet wired to the runtime.
        // Requires: (1) args context in interpreter
        let _ = (&config.args, config.timeout_ms);

        // Set up mock stdin if provided
        if !config.stdin.is_empty() {
            rt_set_stdin(&config.stdin);
        }

        // Start capture if enabled
        if config.capture_output {
            rt_capture_stdout_start();
            rt_capture_stderr_start();
        }

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
            RunningType::CompileAndRun => self.run_compile_and_run(code)?,
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
            RunningType::All => {
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

                let exe_result = self.run_compile_and_run(code)?;

                if interp_result != compiler_result {
                    return Err(format!(
                        "Interpreter and JIT compiler results differ: interpreter={}, jit={}",
                        interp_result, compiler_result
                    ));
                }
                if interp_result != exe_result {
                    return Err(format!(
                        "Interpreter and AOT executable results differ: interpreter={}, exe={}",
                        interp_result, exe_result
                    ));
                }
                interp_result
            }
            #[cfg(feature = "wasm")]
            RunningType::Wasm => self.runner.run_source_wasm(code)?,
        };

        // Stop capture and collect output
        let (stdout, stderr) = if config.capture_output {
            (rt_capture_stdout_stop(), rt_capture_stderr_stop())
        } else {
            (String::new(), String::new())
        };

        // Clear mock stdin
        rt_clear_stdin();

        Ok(RunResult {
            exit_code,
            stdout,
            stderr,
        })
    }

    /// Run a Simple source file from disk, with proper import resolution.
    ///
    /// This method is similar to `run()` but takes a file path instead of source code.
    /// The file path is passed to the compiler for proper module resolution,
    /// allowing imports relative to the source file location.
    ///
    /// # Arguments
    /// * `path` - Path to the .spl source file
    /// * `config` - Execution configuration
    ///
    /// # Returns
    /// * `Ok(RunResult)` - Execution result with exit code and captured output
    /// * `Err(String)` - Error message if compilation or execution failed
    pub fn run_file(&self, path: &std::path::Path, config: RunConfig) -> Result<RunResult, String> {
        // Set up mock stdin if provided
        if !config.stdin.is_empty() {
            rt_set_stdin(&config.stdin);
        }

        // Start capture if enabled
        if config.capture_output {
            rt_capture_stdout_start();
            rt_capture_stderr_start();
        }

        let exit_code_result = self.runner.run_file_interpreted(path);

        // Stop capture and collect output BEFORE returning error
        let (stdout, stderr) = if config.capture_output {
            (rt_capture_stdout_stop(), rt_capture_stderr_stop())
        } else {
            (String::new(), String::new())
        };

        // Clear mock stdin
        rt_clear_stdin();

        // Now check for error and include captured output
        let exit_code = exit_code_result.map_err(|e| {
            // Include captured output in error message if there was any
            if !stdout.is_empty() {
                format!("{}\n\nCaptured output:\n{}", e, stdout)
            } else {
                e
            }
        })?;

        Ok(RunResult {
            exit_code,
            stdout,
            stderr,
        })
    }

    /// Run code via AOT compile → settlement → executable → run.
    ///
    /// This method:
    /// 1. Compiles the source to SMF bytes
    /// 2. Loads the SMF as a module
    /// 3. Creates a Settlement and adds the module
    /// 4. Packages the settlement as an executable
    /// 5. Runs the executable and returns the exit code
    fn run_compile_and_run(&self, code: &str) -> Result<i32, String> {
        // Create temp directory for all artifacts
        let tmp = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;

        // Compile source to SMF bytes
        let smf_bytes = self.runner.compile_to_memory(code)?;

        // Load the module
        let loader = simple_loader::ModuleLoader::new();
        let module = loader
            .load_from_memory(&smf_bytes)
            .map_err(|e| format!("load module: {e}"))?;

        // Create a settlement
        let allocator = Arc::new(PlatformAllocator::new());
        let config = SettlementConfig {
            code_region_size: 4 * 1024 * 1024, // 4MB
            data_region_size: 2 * 1024 * 1024, // 2MB
            reloadable: false,
            executable: true,
        };

        let mut settlement = Settlement::new(config, allocator).map_err(|e| format!("create settlement: {e}"))?;

        // Add the module to the settlement
        settlement.add_module(&module).map_err(|e| format!("add module: {e}"))?;

        // Create executable
        let exe_path = tmp.path().join(if cfg!(windows) { "app.exe" } else { "app" });

        create_executable(&settlement, &exe_path).map_err(|e| format!("create executable: {e}"))?;

        // Make executable on Unix
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = std::fs::metadata(&exe_path)
                .map_err(|e| format!("get perms: {e}"))?
                .permissions();
            perms.set_mode(0o755);
            std::fs::set_permissions(&exe_path, perms).map_err(|e| format!("set perms: {e}"))?;
        }

        // Run the executable
        let output = Command::new(&exe_path).output().map_err(|e| format!("run exe: {e}"))?;

        // Get exit code
        let exit_code = output.status.code().unwrap_or(-1);

        // Check for runtime errors (look for "error:" or "panic" in stderr)
        let stderr_str = String::from_utf8_lossy(&output.stderr);
        if exit_code == -1 || stderr_str.contains("Load error:") || stderr_str.contains("Execution error:") {
            return Err(format!("Executable failed (exit={}): {}", exit_code, stderr_str));
        }

        Ok(exit_code)
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

    /// Run code with output capture enabled
    ///
    /// This captures all stdout/stderr output into RunResult.stdout/stderr.
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    pub fn run_with_capture(&self, code: &str) -> Result<RunResult, String> {
        self.run(
            code,
            RunConfig {
                capture_output: true,
                ..Default::default()
            },
        )
    }

    /// Run code in memory with output capture enabled
    ///
    /// # Arguments
    /// * `code` - Simple source code to run
    pub fn run_in_memory_with_capture(&self, code: &str) -> Result<RunResult, String> {
        self.run(
            code,
            RunConfig {
                in_memory: true,
                capture_output: true,
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
/// ```no_run
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
/// ```no_run
/// use simple_driver::run_jit;
///
/// let result = run_jit("fn main() -> i64:\n    return 42\n").unwrap();
/// assert_eq!(result.exit_code, 42);
/// ```
///
/// Display error hints from parser (helpful messages for common mistakes)
fn display_error_hints(parser: &Parser, source: &str) {
    let hints = parser.error_hints();
    if hints.is_empty() {
        return;
    }

    // Display hints to stderr
    for hint in hints {
        let level_str = match hint.level {
            ErrorHintLevel::Error => "\x1b[31merror\x1b[0m",     // red
            ErrorHintLevel::Warning => "\x1b[33mwarning\x1b[0m", // yellow
            ErrorHintLevel::Info => "\x1b[36minfo\x1b[0m",       // cyan
            ErrorHintLevel::Hint => "\x1b[32mhint\x1b[0m",       // green
        };

        eprintln!("{}: {}", level_str, hint.message);
        eprintln!("  --> line {}:{}", hint.span.line, hint.span.column);

        // Show source line with caret
        if let Some(line) = source.lines().nth(hint.span.line - 1) {
            eprintln!("   |");
            eprintln!("{:3} | {}", hint.span.line, line);
            eprintln!("   | {}^", " ".repeat(hint.span.column - 1));
        }

        if let Some(ref suggestion) = hint.suggestion {
            eprintln!("\nSuggestion: {}", suggestion);
        }

        if let Some(ref help) = hint.help {
            eprintln!("\nHelp:\n{}", help);
        }

        eprintln!(); // blank line between hints
    }
}

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
    let parse_result = parser.parse();

    // Display error hints (even if parsing failed)
    display_error_hints(&parser, code);

    // Now check if parsing succeeded
    let ast = parse_result.map_err(|e| format!("parse error: {}", e))?;

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
