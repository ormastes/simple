# FFI Syscalls Quick Reference

**Binary:** `rust/target/release/libffi_syscalls.so` (11 KB)
**Crate:** `rust/ffi_syscalls/`
**Tests:** `test/system/ffi/syscalls_test.spl`

## Build Commands

```bash
# Build the syscalls crate
cd rust
cargo build -p ffi_syscalls --release

# Check binary size
ls -lh target/release/libffi_syscalls.so

# Verify exports (should show 16)
nm target/release/libffi_syscalls.so | grep " T " | grep rt_ | wc -l
```

## Function Reference (16 total)

### File I/O (9 functions)

| Function | Signature | Syscalls | Returns |
|----------|-----------|----------|---------|
| `rt_file_exists` | `(path: text) -> bool` | `stat()` | true if exists |
| `rt_file_read_text` | `(path: text) -> text` | `open()`, `read()`, `close()` | file contents or null |
| `rt_file_write_text` | `(path: text, content: text) -> bool` | `open()`, `write()`, `close()` | true if success |
| `rt_file_delete` | `(path: text) -> bool` | `unlink()` | true if success |
| `rt_file_size` | `(path: text) -> i64` | `stat()` | size or -1 |
| `rt_dir_create` | `(path: text, recursive: bool) -> bool` | `mkdir()` | true if success |
| `rt_dir_list` | `(path: text) -> [text]` | `opendir()`, `readdir()`, `closedir()` | array of names |
| `rt_file_lock` | `(path: text) -> i64` | `open()`, `fcntl(F_SETLK)` | fd or -1 |
| `rt_file_unlock` | `(fd: i64) -> bool` | `fcntl(F_UNLCK)`, `close()` | true if success |

### Environment (3 functions)

| Function | Signature | Syscalls | Returns |
|----------|-----------|----------|---------|
| `rt_env_cwd` | `() -> text` | `getcwd()` | current directory |
| `rt_env_get` | `(key: text) -> text` | `getenv()` | value or "" |
| `rt_env_home` | `() -> text` | `getenv("HOME")`, `getpwuid()` | home directory |

### Process (2 functions)

| Function | Signature | Syscalls | Returns |
|----------|-----------|----------|---------|
| `rt_getpid` | `() -> i64` | `getpid()` | process ID |
| `rt_process_run` | `(cmd: text, args: [text]) -> i32` | `fork()`, `execvp()`, `waitpid()` | exit code |

### System Info (2 functions)

| Function | Signature | Syscalls | Returns |
|----------|-----------|----------|---------|
| `rt_system_cpu_count` | `() -> i64` | `sysconf(_SC_NPROCESSORS_ONLN)` | CPU count |
| `rt_hostname` | `() -> text` | `gethostname()` | hostname |

## Usage in Simple

```simple
# File operations
extern fn rt_file_exists(path: text) -> bool
extern fn rt_file_read_text(path: text) -> text
extern fn rt_file_write_text(path: text, content: text) -> bool

fn example_file_ops():
    val path = "/tmp/test.txt"

    # Write
    rt_file_write_text(path, "Hello!")

    # Read
    if rt_file_exists(path):
        val content = rt_file_read_text(path)
        print content

    # Delete
    rt_file_delete(path)

# Environment
extern fn rt_env_cwd() -> text
extern fn rt_env_get(key: text) -> text
extern fn rt_env_home() -> text

fn example_env():
    val cwd = rt_env_cwd()
    val path = rt_env_get("PATH")
    val home = rt_env_home()

    print "Working in: {cwd}"
    print "Home: {home}"

# Process
extern fn rt_getpid() -> i64
extern fn rt_process_run(cmd: text, args: [text]) -> i32

fn example_process():
    val pid = rt_getpid()
    print "My PID: {pid}"

    val exit_code = rt_process_run("ls", ["-la"])
    if exit_code == 0:
        print "Command succeeded"

# System info
extern fn rt_system_cpu_count() -> i64
extern fn rt_hostname() -> text

fn example_system():
    val cpus = rt_system_cpu_count()
    val hostname = rt_hostname()

    print "Running on {hostname} with {cpus} CPUs"
```

## Memory Management

**Important:** Strings returned by FFI functions are allocated with `malloc()` and must be freed by the caller.

```rust
// In Rust runtime:
let text = rt_file_read_text(path);
// ... use text ...
libc::free(text as *mut c_void);  // Must free!
```

## Error Handling

| Type | Error Indication | Example |
|------|-----------------|---------|
| Boolean | `false` | `rt_file_exists()` returns `false` if not found |
| Pointer | `null` | `rt_file_read_text()` returns `null` on error |
| Integer | `-1` | `rt_file_size()` returns `-1` on error |
| String | `""` | `rt_env_get()` returns empty string if not set |

## Platform Support

### Currently Supported
- ✅ Linux (POSIX syscalls)
- ✅ macOS (POSIX syscalls)
- ✅ BSD (POSIX syscalls)

### Not Yet Supported
- ❌ Windows (needs Win32 API implementation)
- ❌ WebAssembly (needs WASI wrappers)

## Implementation Details

### File Structure
```
rust/ffi_syscalls/
├── Cargo.toml          # Minimal config (only libc)
└── src/
    └── lib.rs          # 350 lines, 16 functions, #![no_std]
```

### Key Features
- `#![no_std]` - No standard library
- Only dependency: `libc = "0.2"`
- Panic handler: `libc::abort()`
- Manual memory management
- Direct syscalls (no abstractions)

### Optimization Settings
```toml
[profile.release]
opt-level = "z"      # Optimize for size
lto = true           # Link-time optimization
codegen-units = 1    # Single codegen unit
panic = "abort"      # No unwinding
strip = true         # Strip symbols
```

## Adding New Syscall Functions

1. **Add to spec:** `src/app/ffi_gen/specs/syscalls_core.spl`
2. **Implement:** `rust/ffi_syscalls/src/lib.rs`
3. **Export:** Use `#[no_mangle]` and `extern "C"`
4. **Test:** Add to `test/system/ffi/syscalls_test.spl`
5. **Document:** Update this quick reference

## Troubleshooting

### Build fails with "panic handler required"
- Solution: Add panic handler to `lib.rs` (already done)

### Build fails with "unwinding panics not supported"
- Solution: Set `panic = "abort"` in workspace `Cargo.toml` (already done)

### Function not exported
- Check: `#[no_mangle]` attribute present
- Check: `pub extern "C"` signature
- Verify: `nm libffi_syscalls.so | grep function_name`

### Binary size too large
- Check: Using `--release` profile
- Check: `opt-level = "z"` in Cargo.toml
- Check: `lto = true` and `strip = true`

## Performance Characteristics

| Operation | Syscalls | Time Complexity | Notes |
|-----------|----------|----------------|-------|
| File exists | 1 (`stat`) | O(1) | Fast, kernel lookup |
| File read | 3 (`open`, `read`, `close`) | O(n) | n = file size |
| File write | 3 (`open`, `write`, `close`) | O(n) | n = content size |
| Dir list | Many (`opendir`, `readdir`*n, `closedir`) | O(n) | n = entries |
| Process run | 3+ (`fork`, `exec`, `wait`) | O(1) startup | + child execution time |

## Comparison to Standard Libraries

| Feature | ffi_syscalls | std::fs | std::env | std::process |
|---------|-------------|---------|----------|--------------|
| Binary size | 11 KB | ~2 MB | ~2 MB | ~2 MB |
| Dependencies | libc only | std + many | std + many | std + many |
| Platform support | Unix only | Cross-platform | Cross-platform | Cross-platform |
| Error handling | Manual | Result types | Result types | Result types |
| Safety | Unsafe | Safe | Safe | Safe |

**Trade-off:** We sacrifice cross-platform support and safe abstractions for minimal size and zero dependencies.

## References

- **Implementation:** `rust/ffi_syscalls/src/lib.rs`
- **Spec:** `src/app/ffi_gen/specs/syscalls_core.spl`
- **Tests:** `test/system/ffi/syscalls_test.spl`
- **Report:** `doc/report/ffi_syscalls_implementation_2026-02-04.md`
- **Plan:** `doc/report/ffi_dependency_reduction_plan.md`
