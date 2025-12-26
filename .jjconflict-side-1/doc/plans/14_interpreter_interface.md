# Interpreter Interface Plan

## Overview

Create an interpreter module in `driver/` that provides a clean interface for running Simple code programmatically with I/O capture. This enables:
- Embedding Simple as a scripting language
- System testing with controlled input/output
- REPL implementation
- IDE integration

---

## Architecture

```
+--------------------------------------------------------------------+
|                     Interpreter Interface                            |
+--------------------------------------------------------------------+
|                                                                      |
|  Input:                         Output:                              |
|  +------------------+          +-------------------+                 |
|  | code: String     |          | exit_code: i32    |                 |
|  | args: Vec<String>|   --->   | stdout: String    |                 |
|  | stdin: String    |          | stderr: String    |                 |
|  +------------------+          +-------------------+                 |
|                                                                      |
|  +------------------------------------------------------------+     |
|  |                    Interpreter                              |     |
|  |  +----------+    +----------+    +----------+    +-------+  |     |
|  |  |  Parse   | -> | Compile  | -> |  Load    | -> | Run   |  |     |
|  |  +----------+    +----------+    +----------+    +-------+  |     |
|  |                                                             |     |
|  |  +--------------------------+                               |     |
|  |  |      I/O Capture         |                               |     |
|  |  |  stdin_reader (from str) |                               |     |
|  |  |  stdout_writer (to vec)  |                               |     |
|  |  +--------------------------+                               |     |
|  +------------------------------------------------------------+     |
|                                                                      |
+--------------------------------------------------------------------+
```

---

## API Design

### Core Struct and Result

```rust
// src/driver/src/interpreter.rs

/// Result of running Simple code
#[derive(Debug, Clone)]
pub struct RunResult {
    /// Program exit code (from main return value)
    pub exit_code: i32,
    /// Captured stdout output
    pub stdout: String,
    /// Captured stderr output
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
    gc: GcRuntime,
}
```

### Interface Function

```rust
impl Interpreter {
    /// Create a new interpreter instance
    pub fn new() -> Self;

    /// Run Simple source code with configuration
    /// Returns RunResult with exit code and captured output
    pub fn run(&self, code: &str, config: RunConfig) -> Result<RunResult, String>;

    /// Convenience: Run code with just stdin
    pub fn run_with_stdin(&self, code: &str, stdin: &str) -> Result<RunResult, String>;

    /// Convenience: Run code with no input
    pub fn run_simple(&self, code: &str) -> Result<RunResult, String>;
}
```

### Standalone Function (for simple use)

```rust
/// Run Simple code and return result
/// This is the main interface function for embedding
pub fn run_code(code: &str, args: &[String], stdin: &str) -> Result<RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(code, RunConfig {
        args: args.to_vec(),
        stdin: stdin.to_string(),
        timeout_ms: 0,
    })
}
```

---

## Implementation Plan

### Phase 1: Basic Interpreter Module

**File: `src/driver/src/interpreter.rs`**

1. Create `RunResult` struct
2. Create `RunConfig` struct
3. Create `Interpreter` struct wrapping existing Runner logic
4. Implement `run()` method that:
   - Compiles source to temp SMF
   - Loads and executes
   - Returns exit code (stdout/stderr capture in Phase 2)

### Phase 2: I/O Capture

**Requires modification to compiler/runtime to support I/O redirection**

For now, the interpreter evaluates at compile-time, so:
- Stdout/stderr capture is not yet meaningful
- The exit code is the main return value

Future work will add:
- Print/println builtin functions
- stdin/stdout redirection in runtime

### Phase 3: System Tests

**File: `src/driver/tests/interpreter_tests.rs`**

```rust
#[test]
fn interpreter_runs_simple_code() {
    let result = run_code("main = 42", &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_with_args() {
    let result = run_code(
        "main = 0",
        &["arg1".to_string()],
        ""
    ).unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_arithmetic() {
    let result = run_code("main = 10 + 20 * 2", &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_with_variables() {
    let code = r#"
let x = 10
let y = 20
main = x + y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_with_functions() {
    let code = r#"
fn add(a, b):
    return a + b
main = add(5, 7)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 12);
}

#[test]
fn interpreter_with_structs() {
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_with_enums() {
    let code = r#"
enum Color:
    Red
    Green

let c = Color::Red
main = if c is Color::Red: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_error_handling() {
    let result = run_code("invalid syntax here", &[], "");
    assert!(result.is_err());
}
```

---

## File Structure

```
src/driver/
├── src/
│   ├── lib.rs              # Add: pub mod interpreter;
│   ├── runner.rs           # Existing
│   ├── interpreter.rs      # NEW: Interpreter interface
│   ├── dependency_cache.rs # Existing
│   └── watcher/            # Existing
├── tests/
│   ├── runner_tests.rs     # Existing
│   └── interpreter_tests.rs # NEW: System tests
└── Cargo.toml
```

---

## Implementation Details

### interpreter.rs

```rust
//! Interpreter interface for running Simple code programmatically

use std::fs;
use tempfile::TempDir;
use simple_compiler::CompilerPipeline;
use simple_loader::loader::ModuleLoader as SmfLoader;
use simple_loader::LoadedModule;
use simple_runtime::gc::GcRuntime;

/// Result of running Simple code
#[derive(Debug, Clone, Default)]
pub struct RunResult {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
}

/// Configuration for running code
#[derive(Debug, Clone, Default)]
pub struct RunConfig {
    pub args: Vec<String>,
    pub stdin: String,
    pub timeout_ms: u64,
}

/// Interpreter for running Simple code with I/O capture
pub struct Interpreter {
    loader: SmfLoader,
    gc: GcRuntime,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            loader: SmfLoader::new(),
            gc: GcRuntime::new(),
        }
    }

    pub fn run(&self, code: &str, config: RunConfig) -> Result<RunResult, String> {
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
            stdout: String::new(),  // TODO: capture when I/O is implemented
            stderr: String::new(),
        })
    }

    pub fn run_with_stdin(&self, code: &str, stdin: &str) -> Result<RunResult, String> {
        self.run(code, RunConfig {
            stdin: stdin.to_string(),
            ..Default::default()
        })
    }

    pub fn run_simple(&self, code: &str) -> Result<RunResult, String> {
        self.run(code, RunConfig::default())
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
pub fn run_code(code: &str, args: &[String], stdin: &str) -> Result<RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(code, RunConfig {
        args: args.to_vec(),
        stdin: stdin.to_string(),
        timeout_ms: 0,
    })
}
```

---

## Usage Examples

### Basic Usage

```rust
use simple_driver::interpreter::run_code;

fn main() {
    let result = run_code("main = 42", &[], "").unwrap();
    println!("Exit code: {}", result.exit_code);
}
```

### With Configuration

```rust
use simple_driver::interpreter::{Interpreter, RunConfig};

fn main() {
    let interpreter = Interpreter::new();

    let result = interpreter.run(
        "main = 100",
        RunConfig {
            args: vec!["arg1".into()],
            stdin: "input data".into(),
            timeout_ms: 5000,
        }
    ).unwrap();

    assert_eq!(result.exit_code, 100);
}
```

### Error Handling

```rust
use simple_driver::interpreter::run_code;

fn main() {
    match run_code("invalid code", &[], "") {
        Ok(result) => println!("Exit: {}", result.exit_code),
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

---

## Testing Strategy

1. **Unit Tests**: Test each component in isolation
2. **Integration Tests**: Test the full pipeline
3. **System Tests**: Test with various Simple programs

Test coverage:
- Basic expressions (arithmetic, boolean)
- Variables and bindings
- Control flow (if/else, loops)
- Functions
- Structs and Enums
- Error cases (syntax errors, runtime errors)

---

## Future Enhancements

1. **I/O Capture**: When print/input builtins are added
2. **Timeout Support**: Kill long-running programs
3. **Memory Limits**: Limit heap allocation
4. **Parallel Execution**: Run multiple programs concurrently
5. **Incremental Compilation**: Cache compiled modules

---

## Summary

| Component | Purpose |
|-----------|---------|
| `RunResult` | Container for execution results |
| `RunConfig` | Execution configuration |
| `Interpreter` | Main interpreter struct |
| `run_code()` | Convenience function |
| `interpreter_tests.rs` | System tests |

This provides a clean interface for embedding Simple as a scripting language and enables comprehensive system testing.
