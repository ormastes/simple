# Plan: Migrate Tests to Use std Print Library

## Status: Phase 1-5 Complete ✓

The I/O capture infrastructure is now fully implemented. Tests can capture stdout/stderr using `RunConfig { capture_output: true }`.

### Completed Work

| Phase | Description | Status |
|-------|-------------|--------|
| 1.1 | Add I/O FFI functions to runtime | ✓ Complete |
| 1.2 | Add FFI specs to codegen | ✓ Complete |
| 2.1 | Update interpreter_extern.rs | ✓ Complete |
| 2.2 | Add capture_output to RunConfig | ✓ Complete |
| 5.1 | Add test helper functions | ✓ Complete |
| 3.1 | Auto-load prelude | Pending (optional) |
| 4 | Native I/O library for compiled code | Pending (optional) |
| 6 | Update all tests to new print | Partially done |

### Usage

```rust
// Test with output capture
let interpreter = Interpreter::new();
let result = interpreter.run(code, RunConfig {
    capture_output: true,
    ..Default::default()
}).unwrap();
assert_eq!(result.stdout, "hello\n");

// Test helpers
run_expect_stdout(src, "expected output");
run_expect_output(src, "output", 0);  // with exit code
run_expect_stdout_contains(src, "substring");
```

**Note:** Until prelude auto-import is implemented, tests need `extern fn` declarations:
```simple
extern fn println(msg)
println("hello")
main = 0
```

---

## Original Analysis (for reference)

## Current State Analysis

### 1. Ad-hoc Print Implementation

Currently, print functionality is implemented as **hardcoded extern function handlers** in the interpreter:

**File: `src/compiler/src/interpreter_extern.rs`**
```rust
match name {
    "print" => {
        check_async_violation("print")?;
        for val in &evaluated {
            print!("{}", val.to_display_string());
        }
        Ok(Value::Nil)
    }
    "println" => {
        check_async_violation("println")?;
        for val in &evaluated {
            print!("{}", val.to_display_string());
        }
        println!();
        Ok(Value::Nil)
    }
    // ...
}
```

**Problems:**
- Hardcoded in Rust, not using Simple stdlib
- No output capture for tests (`RunResult.stdout` is always empty)
- Different codepaths for interpreter vs. compiled code
- Test code uses `extern fn print(msg)` declarations

### 2. Test Infrastructure

**File: `src/driver/tests/test_helpers.rs`**
- `run_expect()` - Runs both interpreter and compiler, checks exit code
- `run_expect_interp()` - Interpreter only
- `RunResult.stdout` and `RunResult.stderr` are **always empty**

**File: `src/driver/src/interpreter.rs`**
```rust
// NOTE: stdout/stderr capture requires I/O builtins in the runtime.
// When print() builtin is added, it should write to a captured buffer.
Ok(RunResult {
    exit_code,
    stdout: String::new(),  // Always empty!
    stderr: String::new(),
})
```

### 3. New std Print Library

**File: `lib/std/host/async_nogc/io/term.spl`**
- `print(args: ..any)` - Print without newline
- `println(args: ..any)` - Print with newline
- `eprint(args: ..any)` - Print to stderr
- `eprintln(args: ..any)` - Print to stderr with newline
- `input(prompt)` - Read line from stdin

**File: `lib/std/prelude.spl`**
- Auto-imports print functions into every file

### 4. Codegen FFI

**File: `src/compiler/src/codegen/runtime_ffi.rs`**
- 50+ runtime FFI functions for arrays, dicts, objects, etc.
- **NO print/IO functions defined** - need to add

---

## What Needs to Be Done

### Phase 1: Runtime I/O Infrastructure

#### 1.1 Add I/O FFI Functions to Runtime

**File: `src/runtime/src/value/ffi.rs`** (or new `src/runtime/src/io.rs`)

```rust
// Add these FFI functions:

/// Print to captured stdout buffer
#[no_mangle]
pub extern "C" fn rt_print(value: RuntimeValue) {
    // Get thread-local or global output buffer
    let s = value.to_display_string();
    OUTPUT_BUFFER.with(|buf| buf.borrow_mut().push_str(&s));
}

/// Print with newline
#[no_mangle]
pub extern "C" fn rt_println(value: RuntimeValue) {
    rt_print(value);
    OUTPUT_BUFFER.with(|buf| buf.borrow_mut().push('\n'));
}

/// Get captured stdout
#[no_mangle]
pub extern "C" fn rt_get_stdout() -> RuntimeValue {
    OUTPUT_BUFFER.with(|buf| {
        let s = buf.borrow().clone();
        RuntimeValue::from_string(s)
    })
}

/// Clear captured stdout
#[no_mangle]
pub extern "C" fn rt_clear_stdout() {
    OUTPUT_BUFFER.with(|buf| buf.borrow_mut().clear());
}
```

#### 1.2 Add to Codegen FFI Specs

**File: `src/compiler/src/codegen/runtime_ffi.rs`**

```rust
// Add to RUNTIME_FUNCS:
RuntimeFuncSpec::new("rt_print", &[I64], &[]),
RuntimeFuncSpec::new("rt_println", &[I64], &[]),
RuntimeFuncSpec::new("rt_eprint", &[I64], &[]),
RuntimeFuncSpec::new("rt_eprintln", &[I64], &[]),
RuntimeFuncSpec::new("rt_print_str", &[I64, I64], &[]),  // ptr, len
RuntimeFuncSpec::new("rt_term_write", &[I64, I64, I64], &[I64]),  // handle, ptr, len -> written
RuntimeFuncSpec::new("rt_term_read", &[I64, I64, I64], &[I64]),   // handle, ptr, len -> read
RuntimeFuncSpec::new("rt_term_flush", &[I64], &[I32]),
RuntimeFuncSpec::new("rt_stdin", &[], &[I64]),
RuntimeFuncSpec::new("rt_stdout", &[], &[I64]),
RuntimeFuncSpec::new("rt_stderr", &[], &[I64]),
RuntimeFuncSpec::new("rt_is_tty", &[I64], &[I8]),
```

### Phase 2: Update Interpreter

#### 2.1 Modify interpreter_extern.rs

**Option A: Redirect to Runtime FFI**
```rust
"print" => {
    check_async_violation("print")?;
    // Call runtime FFI instead of direct Rust print
    for val in &evaluated {
        rt_print(val.to_runtime_value());
    }
    Ok(Value::Nil)
}
```

**Option B: Use Captured Buffer**
```rust
"print" => {
    check_async_violation("print")?;
    let output = env.get_output_buffer();
    for val in &evaluated {
        output.push_str(&val.to_display_string());
    }
    Ok(Value::Nil)
}
```

#### 2.2 Add Output Capture to RunConfig

**File: `src/driver/src/interpreter.rs`**

```rust
pub struct RunConfig {
    // ... existing fields ...

    /// If true, capture stdout/stderr instead of printing to terminal
    pub capture_output: bool,
}

impl Interpreter {
    pub fn run(&self, code: &str, config: RunConfig) -> Result<RunResult, String> {
        // Clear capture buffers before run
        if config.capture_output {
            rt_clear_stdout();
            rt_clear_stderr();
        }

        // ... run code ...

        // Collect captured output
        let stdout = if config.capture_output {
            rt_get_stdout_string()
        } else {
            String::new()
        };

        Ok(RunResult {
            exit_code,
            stdout,
            stderr,
        })
    }
}
```

### Phase 3: Module System Integration

#### 3.1 Auto-load Prelude

Currently, the prelude is not automatically loaded. Need to:

**File: `src/compiler/src/interpreter.rs`** or `src/compiler/src/pipeline.rs`

```rust
// Before evaluating user code, inject prelude imports
fn inject_prelude(ast: &mut Module) {
    // Add: use std.prelude.*
    ast.statements.insert(0, Statement::Use(UseStmt {
        path: ModulePath { segments: vec!["std", "prelude"] },
        target: ImportTarget::Glob,
    }));
}
```

#### 3.2 Configure stdlib Path

**File: `src/compiler/src/module_resolver.rs`**

```rust
impl ModuleResolver {
    pub fn new(...) -> Self {
        let mut resolver = Self { ... };

        // Add stdlib search path
        let stdlib_path = get_stdlib_path();  // lib/std/
        resolver.add_search_path(stdlib_path);

        resolver
    }
}

fn get_stdlib_path() -> PathBuf {
    // Try: 1. SIMPLE_STDLIB env var
    //      2. Relative to executable
    //      3. Relative to project root
}
```

### Phase 4: Native Library Loading (for compiled code)

#### 4.1 Create Native I/O Library

**File: `native_lib/io/src/lib.rs`**

```rust
use std::io::{self, Write, BufRead};

#[no_mangle]
pub extern "C" fn native_stdout() -> i64 {
    1  // File descriptor for stdout
}

#[no_mangle]
pub extern "C" fn native_stderr() -> i64 {
    2  // File descriptor for stderr
}

#[no_mangle]
pub extern "C" fn native_stdin() -> i64 {
    0  // File descriptor for stdin
}

#[no_mangle]
pub extern "C" fn native_term_write(handle: i64, buf: *const u8, len: u64) -> i64 {
    let slice = unsafe { std::slice::from_raw_parts(buf, len as usize) };
    match handle {
        1 => io::stdout().write(slice).map(|n| n as i64).unwrap_or(-1),
        2 => io::stderr().write(slice).map(|n| n as i64).unwrap_or(-1),
        _ => -1,
    }
}

#[no_mangle]
pub extern "C" fn native_term_read(handle: i64, buf: *mut u8, len: u64) -> i64 {
    if handle != 0 { return -1; }
    let slice = unsafe { std::slice::from_raw_parts_mut(buf, len as usize) };
    io::stdin().read(slice).map(|n| n as i64).unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn native_term_flush(handle: i64) -> i32 {
    match handle {
        1 => io::stdout().flush().map(|_| 0).unwrap_or(-1),
        2 => io::stderr().flush().map(|_| 0).unwrap_or(-1),
        _ => -1,
    }
}

#[no_mangle]
pub extern "C" fn native_is_tty(handle: i64) -> bool {
    use std::os::unix::io::AsRawFd;
    match handle {
        0 => atty::is(atty::Stream::Stdin),
        1 => atty::is(atty::Stream::Stdout),
        2 => atty::is(atty::Stream::Stderr),
        _ => false,
    }
}
```

#### 4.2 Link Native Library in Codegen

**File: `src/compiler/src/codegen/cranelift.rs`** or `jit.rs`

```rust
// When compiling, link the native I/O library
fn link_native_libs(&mut self) {
    // Link native_io library for print/input functions
    self.link_library("native_io");
}
```

### Phase 5: Update Test Helpers

#### 5.1 Add Output Assertion Helpers

**File: `src/driver/tests/test_helpers.rs`**

```rust
/// Run source and assert expected stdout output
pub fn run_expect_output(src: &str, expected_stdout: &str) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(src, RunConfig {
            capture_output: true,
            ..Default::default()
        })
        .expect("run ok");
    assert_eq!(result.stdout, expected_stdout);
}

/// Run source and assert expected stdout contains substring
pub fn run_expect_output_contains(src: &str, expected: &str) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(src, RunConfig {
            capture_output: true,
            ..Default::default()
        })
        .expect("run ok");
    assert!(
        result.stdout.contains(expected),
        "Expected stdout to contain '{}', got: '{}'",
        expected, result.stdout
    );
}

/// Run source with stdin input and check output
pub fn run_with_io(src: &str, stdin: &str, expected_stdout: &str) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(src, RunConfig {
            stdin: stdin.to_string(),
            capture_output: true,
            ..Default::default()
        })
        .expect("run ok");
    assert_eq!(result.stdout, expected_stdout);
}
```

### Phase 6: Update Test Code

#### 6.1 Remove Ad-hoc Extern Declarations

**Before:**
```simple
extern fn print(msg)

fn main():
    print("hello")
```

**After:**
```simple
# Prelude auto-imports print
fn main():
    println "hello"
```

#### 6.2 Update Test Assertions

**Before:**
```rust
#[test]
fn test_print_output() {
    let result = run_code(r#"
extern fn print(msg)
print("hello")
main = 0
"#, &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
    // Can't verify output!
}
```

**After:**
```rust
#[test]
fn test_print_output() {
    run_expect_output(r#"
println "hello"
main = 0
"#, "hello\n");
}
```

---

## Implementation Order

1. **Phase 1.1**: Add I/O FFI functions to `src/runtime/src/value/ffi.rs`
2. **Phase 1.2**: Add FFI specs to `src/compiler/src/codegen/runtime_ffi.rs`
3. **Phase 2.1**: Update `interpreter_extern.rs` to use captured buffer
4. **Phase 2.2**: Add output capture to `RunConfig` and `Interpreter`
5. **Phase 5.1**: Add test helper functions
6. **Phase 3.1**: Auto-load prelude (optional, can use explicit imports first)
7. **Phase 4**: Create native_io library for compiled code
8. **Phase 6**: Update all test code to use new print

---

## Files to Modify

| File | Changes |
|------|---------|
| `src/runtime/src/value/ffi.rs` | Add rt_print, rt_println, output capture |
| `src/runtime/src/value/mod.rs` | Export new FFI functions |
| `src/compiler/src/codegen/runtime_ffi.rs` | Add I/O FFI specs |
| `src/compiler/src/interpreter_extern.rs` | Use captured buffer |
| `src/driver/src/interpreter.rs` | Add capture_output to RunConfig |
| `src/driver/tests/test_helpers.rs` | Add output assertion helpers |
| `native_lib/io/src/lib.rs` | Create native I/O library (new) |
| `native_lib/io/Cargo.toml` | Create crate config (new) |
| `src/driver/tests/*.rs` | Update tests to use new print |

---

## Test Files Using Ad-hoc Print

These files use `extern fn print`:
- `src/driver/tests/interpreter_async_tests.rs` (line 159-175)

These files could benefit from output capture:
- `src/driver/tests/interpreter_basic.rs`
- `src/driver/tests/interpreter_expressions.rs`
- `src/driver/tests/runner_tests.rs`

---

## Alternative: Minimal Change

If full migration is too large, a minimal change would be:

1. Keep hardcoded `print`/`println` in interpreter_extern.rs
2. Add output capture buffer to Env
3. Update test helpers to capture output
4. Don't require stdlib loading for basic tests

This allows tests to verify output without full stdlib integration.
