# SFFI - Simple Foreign Function Interface

**Version:** 0.5.0
**Status:** Production Ready

---

## Overview

SFFI (Simple FFI) is Simple's mechanism for calling C/C++/Rust functions. It uses a layered wrapper pattern that keeps unsafe code isolated and provides clean Simple APIs.

**Key Concepts:**
- **Raw FFI** (`extern fn rt_*`) -- Direct C function declarations
- **SFFI Wrapper** (`fn safe_name()`) -- Safe Simple wrapper around raw FFI
- **External Library Pattern** -- Three-tier wrapping for third-party libraries

---

## Two-Tier Pattern (Runtime Functions)

The standard pattern for wrapping runtime C functions:

### Tier 1: Raw FFI Declaration

```simple
# In src/lib/ffi/mod.spl
extern fn rt_file_read_text(path: text) -> text
extern fn rt_file_write_text(path: text, content: text) -> bool
extern fn rt_file_exists(path: text) -> bool
```

Naming convention: `rt_` prefix maps to C functions in `src/runtime/runtime.c`.

### Tier 2: Safe Simple Wrapper

```simple
# In src/lib/fs/mod.spl
use std.ffi.{rt_file_read_text, rt_file_write_text, rt_file_exists}

fn file_read(path: text) -> text:
    rt_file_read_text(path)

fn file_write(path: text, content: text) -> bool:
    rt_file_write_text(path, content)

fn file_exists(path: text) -> bool:
    rt_file_exists(path)
```

### Usage

```simple
use std.fs.{file_read, file_write, file_exists}

fn main():
    if file_exists("config.sdn"):
        val config = file_read("config.sdn")
        print "Config: {config}"
```

---

## Three-Tier Pattern (External Libraries)

For wrapping external C/C++ libraries (PyTorch, OpenCV, SQLite, etc.):

### Tier 1: C/C++ Glue Code

Write a thin C wrapper that exposes a C-compatible interface:

```c
// src/lib/ffi/torch_ffi.cpp
#include <torch/torch.h>

extern "C" {
    void* spl_torch_zeros(int rows, int cols) {
        auto* t = new torch::Tensor(torch::zeros({rows, cols}));
        return static_cast<void*>(t);
    }

    int spl_torch_numel(void* handle) {
        auto* t = static_cast<torch::Tensor*>(handle);
        return t->numel();
    }

    void spl_torch_free(void* handle) {
        delete static_cast<torch::Tensor*>(handle);
    }
}
```

### Tier 2: Raw FFI Declaration

```simple
# src/lib/ffi/torch.spl
extern fn spl_torch_zeros(rows: i32, cols: i32) -> i64
extern fn spl_torch_numel(handle: i64) -> i32
extern fn spl_torch_free(handle: i64)
```

### Tier 3: Safe Simple API

```simple
# src/lib/torch/tensor.spl
use std.ffi.torch.{spl_torch_zeros, spl_torch_numel, spl_torch_free}

class Tensor:
    handle: i64

    static fn zeros(rows: i32, cols: i32) -> Tensor:
        val h = spl_torch_zeros(rows, cols)
        Tensor(handle: h)

    fn numel() -> i32:
        spl_torch_numel(self.handle)

    fn free():
        spl_torch_free(self.handle)
```

### Usage

```simple
use std.torch.tensor.{Tensor}

fn main():
    val t = Tensor.zeros(3, 4)
    print "Elements: {t.numel()}"
    t.free()
```

---

## Common Patterns

### Opaque Handle Pattern

External objects are represented as `i64` handles in Simple:

```simple
extern fn spl_db_open(path: text) -> i64      # Returns handle
extern fn spl_db_query(handle: i64, sql: text) -> text
extern fn spl_db_close(handle: i64)           # Frees handle

class Database:
    handle: i64

    static fn open(path: text) -> Database:
        Database(handle: spl_db_open(path))

    fn query(sql: text) -> text:
        spl_db_query(self.handle, sql)

    fn close():
        spl_db_close(self.handle)
```

### Feature Detection Pattern

Check if an external library is available before using it:

```simple
extern fn spl_torch_available() -> bool

fn with_torch():
    if not spl_torch_available():
        print "PyTorch not available, using CPU fallback"
        return
    # Use PyTorch...
```

### Error Handling Pattern

Return error codes or Result types:

```simple
extern fn spl_file_open(path: text) -> i64  # Returns -1 on error

fn open_file(path: text) -> Result<i64, text>:
    val handle = spl_file_open(path)
    if handle < 0:
        Err("Failed to open: {path}")
    else:
        Ok(handle)
```

---

## SFFI-Gen: Code Generation

SFFI-gen automatically generates FFI wrappers from specification files.

### Specification Format

```simple
# specs/file_io.spl
class InternFnSpec:
    name: text           # Function name (e.g., "file_read")
    rt_name: text        # C function name (e.g., "rt_file_read_text")
    params: List<Param>  # Parameter list
    ret_type: text       # Return type
    category: text       # Module category (e.g., "fs")
```

### Type Mappings

| Simple Type | C Type | FFI Declaration |
|-------------|--------|-----------------|
| `text` | `const char*` | `text` |
| `i32` | `int32_t` | `i32` |
| `i64` | `int64_t` | `i64` |
| `bool` | `bool` | `bool` |
| `f64` | `double` | `f64` |
| `()` (unit) | `void` | (no return) |

### Running SFFI-Gen

```bash
# Generate all FFI wrappers from specs
bin/simple sffi-gen

# Generate for specific module
bin/simple sffi-gen --module fs

# Preview without writing
bin/simple sffi-gen --dry-run
```

### Generated Output

SFFI-gen produces:
1. **Raw FFI declarations** in `src/lib/ffi/`
2. **Safe wrappers** in the appropriate `src/lib/` module
3. **C stubs** in `src/runtime/` (if needed)

### Adding a New FFI Function

1. Add the C implementation to `src/runtime/runtime.c`
2. Add the spec to the appropriate spec file
3. Run `bin/simple sffi-gen`
4. Or manually: add `extern fn` to `src/lib/ffi/mod.spl` and wrapper to module

---

## FFI Syscalls Reference

### File I/O

| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_file_read_text` | `(path: text) -> text` | Read entire file as text |
| `rt_file_write_text` | `(path: text, content: text) -> bool` | Write text to file |
| `rt_file_exists` | `(path: text) -> bool` | Check if file exists |
| `rt_file_delete` | `(path: text) -> bool` | Delete a file |
| `rt_file_size` | `(path: text) -> i64` | Get file size in bytes |

### Directory Operations

| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_dir_create` | `(path: text) -> bool` | Create directory |
| `rt_dir_list` | `(path: text) -> text` | List directory entries (newline-separated) |
| `rt_dir_exists` | `(path: text) -> bool` | Check if directory exists |

### Environment and Process

| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_env_get` | `(name: text) -> text` | Get environment variable |
| `rt_env_set` | `(name: text, value: text) -> bool` | Set environment variable |
| `rt_process_exit` | `(code: i32)` | Exit with status code |
| `rt_process_args` | `() -> text` | Get command-line arguments |

### System Information

| Function | Signature | Description |
|----------|-----------|-------------|
| `rt_sys_platform` | `() -> text` | Get platform name (linux/darwin/windows) |
| `rt_sys_arch` | `() -> text` | Get CPU architecture |
| `rt_time_now_ms` | `() -> i64` | Current time in milliseconds |
| `rt_time_monotonic_ns` | `() -> i64` | Monotonic clock in nanoseconds |

### Memory Management

All FFI calls that return text or handles manage memory automatically through the runtime. Text values returned from C are copied into Simple's managed heap. Handles (`i64`) must be explicitly freed using the corresponding `_free` or `_close` function.

### Platform Support

| Function Group | Linux | macOS | Windows |
|---------------|-------|-------|---------|
| File I/O | Full | Full | Full |
| Directory | Full | Full | Full |
| Environment | Full | Full | Full |
| Process | Full | Full | Partial |
| System Info | Full | Full | Full |
| Time | Full | Full | Full |

---

## Signal Handler SFFI

Signal handling for graceful shutdown and cleanup:

### API

```simple
extern fn rt_signal_handler_available() -> bool
extern fn rt_signal_handler_install(signal: i32) -> bool
extern fn rt_atexit_register(callback_id: i32) -> bool
```

### Signal Constants

| Signal | Value | Description |
|--------|-------|-------------|
| `SIGINT` | 2 | Interrupt (Ctrl+C) |
| `SIGTERM` | 15 | Termination request |
| `SIGHUP` | 1 | Hangup (Linux/macOS only) |

### Usage

```simple
fn setup_signal_handling():
    if not rt_signal_handler_available():
        print "Signal handling not available on this platform"
        return

    # Install handler for Ctrl+C
    if rt_signal_handler_install(2):
        print "SIGINT handler installed"

    # Register cleanup on exit
    rt_atexit_register(0)
```

### Platform Support

| Feature | Linux | macOS | Windows |
|---------|-------|-------|---------|
| SIGINT | Yes | Yes | Partial |
| SIGTERM | Yes | Yes | No |
| SIGHUP | Yes | Yes | No |
| atexit | Yes | Yes | Yes |

### Thread Safety

Signal handlers run in signal context. Only async-signal-safe operations are permitted in handlers. The runtime queues signals for processing in the main thread.

---

## File Organization

```
src/lib/ffi/           # Raw FFI declarations (extern fn)
  mod.spl              # Runtime FFI functions
  torch.spl            # PyTorch FFI
  opencv.spl           # OpenCV FFI
  sqlite.spl           # SQLite FFI

src/lib/               # Safe wrappers (organized by module)
  fs/mod.spl           # File system wrappers
  net/mod.spl          # Network wrappers
  torch/tensor.spl     # PyTorch wrappers

src/runtime/           # C implementations
  runtime.c            # Core runtime functions
  runtime.h            # C headers
```

---

## Best Practices

1. **Always wrap raw FFI** -- Never use `extern fn` directly in application code
2. **Use opaque handles** -- Represent C objects as `i64`, not raw pointers
3. **Check availability** -- Use feature detection before calling optional FFI
4. **Handle errors** -- Return `Result<T, E>` from wrappers, not raw error codes
5. **Document ownership** -- Clearly state who frees handles (Simple or C)
6. **Prefix conventions** -- `rt_` for runtime, `spl_` for external library glue
7. **Keep glue minimal** -- C/C++ glue should only convert types, not implement logic

---

## Troubleshooting

| Error | Cause | Fix |
|-------|-------|-----|
| `undefined symbol: rt_*` | Missing C implementation | Add function to `runtime.c` |
| `link error: spl_torch_*` | Library not linked | Add `-ltorch` to link flags |
| Segfault in FFI call | Invalid handle or null pointer | Check handle validity before use |
| Wrong return value | Type mismatch between C and Simple | Verify type mappings match |
| `extern fn` not found | Missing FFI declaration | Add to `src/lib/ffi/mod.spl` |

---

## Related Documentation

- Full syntax reference: `doc/07_guide/quick_reference/syntax_quick_reference.md`
- Wrapper generator: `doc/07_guide/ffi/wrapper_gen.md`
- GPU FFI: `doc/07_guide/apps/gpu.md`
