# Basic I/O Library Plan

## Overview

Implement minimal terminal input/output for the Simple language runtime. This is essential for testing and basic program interaction.

---

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                  Simple I/O Library                      │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  ┌─────────────┐      ┌─────────────┐                   │
│  │  print()    │      │  println()  │                   │
│  │  Functions  │      │  Functions  │                   │
│  └──────┬──────┘      └──────┬──────┘                   │
│         │                    │                           │
│         ▼                    ▼                           │
│  ┌─────────────────────────────────────┐                │
│  │         StdoutWriter                 │                │
│  │    (buffered, cross-platform)        │                │
│  └──────────────┬──────────────────────┘                │
│                 │                                        │
│                 ▼                                        │
│  ┌─────────────────────────────────────┐                │
│  │     Platform Abstraction Layer       │                │
│  │  ┌─────────┐       ┌─────────────┐  │                │
│  │  │  Linux  │       │   Windows   │  │                │
│  │  │  write  │       │  WriteFile  │  │                │
│  │  └─────────┘       └─────────────┘  │                │
│  └─────────────────────────────────────┘                │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

---

## Simple Language API

### Output Functions

```simple
# Print without newline
fn print(value: Any) waitless

# Print with newline
fn println(value: Any) waitless

# Formatted print (with string interpolation)
fn printf(format: String, args: [Any]) waitless

# Print to stderr
fn eprint(value: Any) waitless
fn eprintln(value: Any) waitless
```

### Input Functions

```simple
# Read a line from stdin (blocking - NOT waitless)
fn input() -> String

# Read a line with prompt
fn input(prompt: String) -> String

# Read single character
fn read_char() -> Char

# Check if input available (non-blocking)
fn has_input() waitless -> Bool
```

---

## Rust Implementation

### File Structure

```
crates/runtime/
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── io/
    │   ├── mod.rs
    │   ├── stdout.rs
    │   ├── stdin.rs
    │   └── platform.rs
    └── builtin/
        └── io.rs
```

### Core Types (io/mod.rs)

```rust
// crates/runtime/src/io/mod.rs

mod stdout;
mod stdin;
mod platform;

pub use stdout::*;
pub use stdin::*;

use std::io::{self, Write, BufWriter};

/// Thread-local stdout buffer for performance
thread_local! {
    static STDOUT: RefCell<BufWriter<io::Stdout>> =
        RefCell::new(BufWriter::with_capacity(8192, io::stdout()));
}

/// Flush stdout buffer
pub fn flush_stdout() {
    STDOUT.with(|out| {
        out.borrow_mut().flush().ok();
    });
}

/// Write string to stdout (buffered)
pub fn write_stdout(s: &str) {
    STDOUT.with(|out| {
        out.borrow_mut().write_all(s.as_bytes()).ok();
    });
}

/// Write string to stdout with newline
pub fn writeln_stdout(s: &str) {
    STDOUT.with(|out| {
        let mut w = out.borrow_mut();
        w.write_all(s.as_bytes()).ok();
        w.write_all(b"\n").ok();
    });
}
```

### Stdout Implementation (io/stdout.rs)

```rust
// crates/runtime/src/io/stdout.rs

use std::io::{self, Write};
use std::sync::Mutex;

/// Global stdout writer with buffering
pub struct StdoutWriter {
    buffer: Vec<u8>,
    capacity: usize,
}

impl StdoutWriter {
    pub fn new() -> Self {
        Self {
            buffer: Vec::with_capacity(8192),
            capacity: 8192,
        }
    }

    pub fn write(&mut self, data: &[u8]) {
        if self.buffer.len() + data.len() > self.capacity {
            self.flush();
        }
        self.buffer.extend_from_slice(data);
    }

    pub fn writeln(&mut self, data: &[u8]) {
        self.write(data);
        self.write(b"\n");
    }

    pub fn flush(&mut self) {
        if !self.buffer.is_empty() {
            let _ = io::stdout().write_all(&self.buffer);
            self.buffer.clear();
        }
    }
}

impl Drop for StdoutWriter {
    fn drop(&mut self) {
        self.flush();
    }
}

// Global instance
lazy_static::lazy_static! {
    pub static ref STDOUT: Mutex<StdoutWriter> = Mutex::new(StdoutWriter::new());
}
```

### Stdin Implementation (io/stdin.rs)

```rust
// crates/runtime/src/io/stdin.rs

use std::io::{self, BufRead, BufReader};
use std::sync::Mutex;

/// Line-buffered stdin reader
pub struct StdinReader {
    reader: BufReader<io::Stdin>,
    line_buffer: String,
}

impl StdinReader {
    pub fn new() -> Self {
        Self {
            reader: BufReader::new(io::stdin()),
            line_buffer: String::with_capacity(256),
        }
    }

    /// Read a line (blocking)
    pub fn read_line(&mut self) -> io::Result<String> {
        self.line_buffer.clear();
        self.reader.read_line(&mut self.line_buffer)?;

        // Remove trailing newline
        if self.line_buffer.ends_with('\n') {
            self.line_buffer.pop();
            if self.line_buffer.ends_with('\r') {
                self.line_buffer.pop();
            }
        }

        Ok(self.line_buffer.clone())
    }

    /// Check if input available (non-blocking)
    #[cfg(unix)]
    pub fn has_input(&self) -> bool {
        use std::os::unix::io::AsRawFd;
        use libc::{poll, pollfd, POLLIN};

        let fd = io::stdin().as_raw_fd();
        let mut pfd = pollfd {
            fd,
            events: POLLIN,
            revents: 0,
        };

        unsafe { poll(&mut pfd, 1, 0) > 0 }
    }

    #[cfg(windows)]
    pub fn has_input(&self) -> bool {
        use windows_sys::Win32::System::Console::*;

        let handle = unsafe { GetStdHandle(STD_INPUT_HANDLE) };
        let mut events = 0u32;

        unsafe {
            GetNumberOfConsoleInputEvents(handle, &mut events) != 0 && events > 0
        }
    }
}

lazy_static::lazy_static! {
    pub static ref STDIN: Mutex<StdinReader> = Mutex::new(StdinReader::new());
}
```

### Platform Layer (io/platform.rs)

```rust
// crates/runtime/src/io/platform.rs

#[cfg(unix)]
mod unix {
    use std::io::{self, Write};
    use std::os::unix::io::AsRawFd;

    /// Direct write to stdout (unbuffered)
    pub fn write_direct(data: &[u8]) -> io::Result<usize> {
        let fd = io::stdout().as_raw_fd();
        let result = unsafe {
            libc::write(fd, data.as_ptr() as *const _, data.len())
        };

        if result < 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(result as usize)
        }
    }

    /// Set terminal to raw mode (for read_char)
    pub fn set_raw_mode() -> io::Result<libc::termios> {
        use libc::{tcgetattr, tcsetattr, TCSANOW};

        let fd = io::stdin().as_raw_fd();
        let mut old_termios = std::mem::MaybeUninit::uninit();

        unsafe {
            if tcgetattr(fd, old_termios.as_mut_ptr()) != 0 {
                return Err(io::Error::last_os_error());
            }

            let mut new_termios = old_termios.assume_init();
            new_termios.c_lflag &= !(libc::ICANON | libc::ECHO);
            new_termios.c_cc[libc::VMIN] = 1;
            new_termios.c_cc[libc::VTIME] = 0;

            if tcsetattr(fd, TCSANOW, &new_termios) != 0 {
                return Err(io::Error::last_os_error());
            }

            Ok(old_termios.assume_init())
        }
    }

    /// Restore terminal mode
    pub fn restore_mode(termios: &libc::termios) -> io::Result<()> {
        let fd = io::stdin().as_raw_fd();

        unsafe {
            if libc::tcsetattr(fd, libc::TCSANOW, termios) != 0 {
                return Err(io::Error::last_os_error());
            }
        }

        Ok(())
    }
}

#[cfg(windows)]
mod windows {
    use std::io;
    use windows_sys::Win32::System::Console::*;

    /// Direct write to stdout
    pub fn write_direct(data: &[u8]) -> io::Result<usize> {
        let handle = unsafe { GetStdHandle(STD_OUTPUT_HANDLE) };
        let mut written = 0u32;

        let result = unsafe {
            WriteConsoleA(
                handle,
                data.as_ptr(),
                data.len() as u32,
                &mut written,
                std::ptr::null(),
            )
        };

        if result == 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(written as usize)
        }
    }

    /// Set console to raw mode
    pub fn set_raw_mode() -> io::Result<u32> {
        let handle = unsafe { GetStdHandle(STD_INPUT_HANDLE) };
        let mut mode = 0u32;

        unsafe {
            if GetConsoleMode(handle, &mut mode) == 0 {
                return Err(io::Error::last_os_error());
            }

            let new_mode = mode & !(ENABLE_LINE_INPUT | ENABLE_ECHO_INPUT);
            if SetConsoleMode(handle, new_mode) == 0 {
                return Err(io::Error::last_os_error());
            }
        }

        Ok(mode)
    }

    /// Restore console mode
    pub fn restore_mode(mode: u32) -> io::Result<()> {
        let handle = unsafe { GetStdHandle(STD_INPUT_HANDLE) };

        unsafe {
            if SetConsoleMode(handle, mode) == 0 {
                return Err(io::Error::last_os_error());
            }
        }

        Ok(())
    }
}

#[cfg(unix)]
pub use unix::*;

#[cfg(windows)]
pub use windows::*;
```

### Builtin Functions (builtin/io.rs)

```rust
// crates/runtime/src/builtin/io.rs

use crate::io::{STDOUT, STDIN, flush_stdout};
use crate::value::Value;

/// print(value) - Print value without newline
pub fn builtin_print(args: &[Value]) -> Value {
    if let Some(value) = args.first() {
        let s = value.to_string();
        STDOUT.lock().unwrap().write(s.as_bytes());
    }
    Value::Nil
}

/// println(value) - Print value with newline
pub fn builtin_println(args: &[Value]) -> Value {
    if let Some(value) = args.first() {
        let s = value.to_string();
        STDOUT.lock().unwrap().writeln(s.as_bytes());
    } else {
        STDOUT.lock().unwrap().write(b"\n");
    }
    Value::Nil
}

/// input() -> String - Read line from stdin
pub fn builtin_input(args: &[Value]) -> Value {
    // Print prompt if provided
    if let Some(prompt) = args.first() {
        let s = prompt.to_string();
        STDOUT.lock().unwrap().write(s.as_bytes());
        flush_stdout();
    }

    match STDIN.lock().unwrap().read_line() {
        Ok(line) => Value::String(line),
        Err(_) => Value::String(String::new()),
    }
}

/// has_input() -> Bool - Check if input available
pub fn builtin_has_input(_args: &[Value]) -> Value {
    let has = STDIN.lock().unwrap().has_input();
    Value::Bool(has)
}

/// flush() - Flush stdout buffer
pub fn builtin_flush(_args: &[Value]) -> Value {
    flush_stdout();
    Value::Nil
}

/// Register all I/O builtins
pub fn register_io_builtins(registry: &mut BuiltinRegistry) {
    registry.register("print", builtin_print);
    registry.register("println", builtin_println);
    registry.register("input", builtin_input);
    registry.register("has_input", builtin_has_input);
    registry.register("flush", builtin_flush);
}
```

---

## Value Formatting

### To-String Conversion

```rust
// crates/runtime/src/value/display.rs

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(fl) => {
                if fl.fract() == 0.0 {
                    write!(f, "{:.1}", fl)
                } else {
                    write!(f, "{}", fl)
                }
            }
            Value::Char(c) => write!(f, "{}", c),
            Value::String(s) => write!(f, "{}", s),
            Value::Symbol(s) => write!(f, ":{}", s),
            Value::Tuple(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
            Value::Array(items) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
            Value::Struct { name, fields } => {
                write!(f, "{}(", name)?;
                for (i, (key, val)) in fields.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", key, val)?;
                }
                write!(f, ")")
            }
            Value::Function { name, .. } => {
                write!(f, "<fn {}>", name)
            }
            Value::Actor { id, type_name } => {
                write!(f, "<actor {}#{}>", type_name, id)
            }
        }
    }
}
```

---

## String Interpolation Support

For print with interpolation `{expr}`:

```rust
// crates/runtime/src/io/interpolate.rs

/// Expand string interpolation at runtime
/// Input: "Hello {name}, you are {age} years old"
/// Variables: {"name": "Alice", "age": 30}
/// Output: "Hello Alice, you are 30 years old"
pub fn interpolate(template: &str, vars: &HashMap<String, Value>) -> String {
    let mut result = String::with_capacity(template.len() * 2);
    let mut chars = template.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '{' {
            // Collect variable name
            let mut var_name = String::new();
            while let Some(&next) = chars.peek() {
                if next == '}' {
                    chars.next();
                    break;
                }
                var_name.push(chars.next().unwrap());
            }

            // Look up and format
            if let Some(value) = vars.get(&var_name) {
                result.push_str(&value.to_string());
            } else {
                result.push('{');
                result.push_str(&var_name);
                result.push('}');
            }
        } else if c == '\\' {
            // Handle escape sequences
            if let Some(&next) = chars.peek() {
                match next {
                    'n' => { chars.next(); result.push('\n'); }
                    't' => { chars.next(); result.push('\t'); }
                    'r' => { chars.next(); result.push('\r'); }
                    '\\' => { chars.next(); result.push('\\'); }
                    '{' => { chars.next(); result.push('{'); }
                    _ => result.push(c),
                }
            }
        } else {
            result.push(c);
        }
    }

    result
}
```

---

## Testing

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print_integer() {
        // Capture stdout
        let value = Value::Int(42);
        assert_eq!(value.to_string(), "42");
    }

    #[test]
    fn test_print_float() {
        let value = Value::Float(3.14);
        assert_eq!(value.to_string(), "3.14");
    }

    #[test]
    fn test_interpolation() {
        let mut vars = HashMap::new();
        vars.insert("name".into(), Value::String("Alice".into()));
        vars.insert("age".into(), Value::Int(30));

        let result = interpolate("Hello {name}, age {age}", &vars);
        assert_eq!(result, "Hello Alice, age 30");
    }
}
```

---

## Cargo.toml

```toml
[package]
name = "simple-runtime"
version = "0.1.0"
edition = "2021"

[dependencies]
lazy_static = "1.4"

[target.'cfg(unix)'.dependencies]
libc = "0.2"

[target.'cfg(windows)'.dependencies]
windows-sys = { version = "0.52", features = [
    "Win32_System_Console",
    "Win32_Foundation",
] }
```

---

## Summary

| Component | Purpose |
|-----------|---------|
| `StdoutWriter` | Buffered stdout for performance |
| `StdinReader` | Line-buffered stdin |
| `platform.rs` | OS-specific raw I/O |
| `builtin/io.rs` | Simple language builtins |
| `interpolate.rs` | String interpolation support |

This provides the minimal I/O needed to run and test Simple programs.
