# FFI Boundary Specification
## Date: February 3, 2026

## Overview

This document defines the boundary between Simple (.spl) code and Rust implementation code. It specifies which operations require FFI (Foreign Function Interface) calls to Rust and which can be implemented purely in Simple.

**Total FFI Functions:** 549 declarations across Simple codebase

## Design Principles

### When to Use FFI (Rust Implementation)

✅ **Use FFI for:**
- System calls (file I/O, process management)
- Performance-critical operations (GC, memory management)
- Unsafe operations (raw pointers, ptrace debugging)
- OS-specific functionality (platform detection, signals)
- Low-level runtime operations (bytecode execution, JIT)
- External library bindings (C libraries, system APIs)

❌ **Don't Use FFI for:**
- Business logic and application code
- Pure computation (algorithms, data transformation)
- CLI tools and user-facing applications
- Build scripts and development tools
- Code analysis and formatting
- Test utilities and test generation

## FFI Function Categories

### 1. File System Operations (rt_file_*)

**Most Used FFI Functions:**
- `rt_file_exists(path: str) -> bool` - Check if file exists (36 uses)
- `rt_file_read_text(path: str) -> str` - Read file as text (25 uses)
- `rt_file_write_text(path: str, content: str)` - Write text to file (16 uses)
- `rt_file_delete(path: str)` - Delete file (4 uses)
- `rt_file_copy(src: str, dest: str)` - Copy file (3 uses)
- `rt_file_size(path: str) -> i64` - Get file size (3 uses)

**Legacy Functions (Being Replaced):**
- `native_fs_read_string(path: String) -> Any` (7 uses) → Use `rt_file_read_text`
- `native_fs_write_string(path: String, content: String) -> Any` (6 uses) → Use `rt_file_write_text`
- `native_fs_exists(path: String) -> Bool` (5 uses) → Use `rt_file_exists`

**Rationale:** File I/O requires system calls and error handling. Keep in Rust.

### 2. Directory Operations (rt_dir_*)

**Functions:**
- `rt_dir_create(path: str)` - Create directory (14 uses)
- `rt_dir_walk(path: str) -> [FileInfo]` - Recursive directory walk (6 uses)
- `rt_dir_remove_all(path: str)` - Delete directory recursively

**Rationale:** Directory traversal can be I/O intensive. Rust implementation provides better error handling.

### 3. Process Management (rt_process_*)

**Functions:**
- `rt_process_run(cmd: str, args: [str]) -> ProcessHandle` - Spawn process (13 uses)
- `rt_process_output(cmd: str, args: [str]) -> ProcessOutput` - Run and capture output (4 uses)
- `rt_shell(command: String) -> ShellResult` - Execute shell command (2 uses)

**Rationale:** Process spawning requires OS-level operations. Keep in Rust.

### 4. Environment & System (rt_env_*, sys_*)

**Functions:**
- `rt_env_cwd() -> str` - Current working directory (17 uses)
- `rt_env_get(key: str) -> str?` - Get environment variable (9 uses)
- `rt_env_home() -> str` - User home directory (3 uses)
- `sys_get_args() -> List<String>` - Command-line arguments (9 uses)
- `sys_exit(code: Int)` - Exit process (2 uses)

**Rationale:** Environment variables and system state require OS interaction.

### 5. Time Operations (rt_time_*)

**Functions:**
- `rt_time_now_unix_micros() -> i64` - Current time in microseconds (6 uses)

**Rationale:** High-precision timing requires system calls.

### 6. Package Management (rt_package_*)

**Functions:**
- `rt_package_sha(path: str) -> str` - Calculate file hash (3 uses)
- `rt_package_remove_dir_all(path: str)` - Delete directory (3 uses)
- `rt_package_is_dir(path: str) -> bool` - Check if directory (3 uses)
- `rt_package_file_size(path: str) -> i64` - Get file size (3 uses)

**Rationale:** Package operations may require crypto/hashing. Keep in Rust for now, consider migration later.

### 7. Debugging & Tracing (rt_ptrace_*)

**Functions:**
- `rt_ptrace_attach(pid: i32)` - Attach debugger to process (2 uses)
- `rt_ptrace_detach(pid: i32)` - Detach debugger (2 uses)
- `rt_ptrace_continue(pid: i32)` - Continue execution (2 uses)
- `rt_ptrace_single_step(pid: i32)` - Single-step execution (2 uses)
- `rt_ptrace_get_registers(pid: i32) -> Registers` - Read CPU registers (2 uses)
- `rt_ptrace_read_memory(pid: i32, addr: u64, len: usize) -> [u8]` (2 uses)
- `rt_ptrace_write_memory(pid: i32, addr: u64, data: [u8])` (2 uses)
- `rt_ptrace_wait_stop(pid: i32)` - Wait for process stop (2 uses)

**Rationale:** Debugging requires unsafe operations and system calls. Must stay in Rust.

### 8. Generic FFI (call_ffi_*)

**Functions:**
- `call_ffi_0(ptr: RawPtr) -> u64` - Call C function (0 args)
- `call_ffi_1(ptr: RawPtr, a1: u64) -> u64` - Call C function (1 arg)
- `call_ffi_2(ptr: RawPtr, a1: u64, a2: u64) -> u64` - Call C function (2 args)
- `call_ffi_3(ptr: RawPtr, a1: u64, a2: u64, a3: u64) -> u64` - Call C function (3 args)
- `call_ffi_4(ptr: RawPtr, a1: u64, a2: u64, a3: u64, a4: u64) -> u64` - Call C function (4 args)
- `dlopen(path: &str) -> Result<RawPtr, String>` - Load dynamic library
- `dlclose(handle: RawPtr)` - Unload dynamic library
- `dlsym(handle: RawPtr, name: &str) -> Result<RawPtr, String>` - Get function pointer

**Rationale:** Raw FFI calls require unsafe code. Must stay in Rust.

### 9. Runtime Core (rt_*)

**Functions:**
- `rt_i(value: Any) -> RuntimeValue` - Convert to runtime value (5 uses)

**Rationale:** Runtime value conversion is performance-critical. Keep in Rust.

### 10. Path Utilities (rt_path_*)

**Functions:**
- `rt_path_basename(path: str) -> str` - Extract filename from path (3 uses)

**Migration Candidate:** Could be implemented in Simple as pure string manipulation.

## Migration Targets

### High Priority: Remove Legacy FFI

Replace legacy `native_fs_*` functions with `rt_file_*`:

**Before:**
```simple
extern fn native_fs_read_string(path: String) -> Any
extern fn native_fs_write_string(path: String, content: String) -> Any
extern fn native_fs_exists(path: String) -> Bool
```

**After:**
```simple
extern fn rt_file_read_text(path: str) -> str
extern fn rt_file_write_text(path: str, content: str)
extern fn rt_file_exists(path: str) -> bool
```

**Impact:** ~18 uses across 7 files

**Files to Update:**
- `src/app/formatter/main.spl`
- `src/app/lint/main.spl`
- `src/app/depgraph/parser.spl`
- `src/app/depgraph/scanner.spl`
- `src/app/depgraph/generator.spl`
- `src/app/depgraph/test_parse3.spl`
- `src/app/mcp/main.spl`

### Medium Priority: Path Utilities

**Migrate `rt_path_*` functions to Simple stdlib:**

```simple
# Current (FFI):
extern fn rt_path_basename(path: str) -> str

# Target (Pure Simple):
module std.path:
    fn basename(path: str) -> str:
        """Extract filename from path."""
        val parts = path.split("/")
        parts.last ?? ""
```

**Estimated effort:** 2 hours
**Impact:** Remove 3 FFI calls, add to std.path module

### Low Priority: Package Utilities

**Consider migrating `rt_package_*` functions:**
- `rt_package_is_dir` → Can use `rt_file_exists` + stat
- `rt_package_file_size` → Duplicate of `rt_file_size`

**Keep in Rust (for now):**
- `rt_package_sha` → Requires crypto library
- `rt_package_remove_dir_all` → Already have `rt_dir_remove_all`

## FFI Usage by Module

### Application Layer (src/app/)

**High FFI usage:**
- `formatter/main.spl` - File I/O (4 FFI functions)
- `lint/main.spl` - File I/O (4 FFI functions)
- `depgraph/` - File system operations (6 FFI functions)
- `build/` - Process, file, environment (15+ FFI functions)
- `mcp/main.spl` - File I/O, process (4 FFI functions)

**Low FFI usage:**
- `cli/main.spl` - Only `sys_get_args` (1 FFI function)
- `repl/main.spl` - Minimal FFI
- `verify/main.spl` - Minimal FFI

### Compiler Layer (src/compiler/)

**Moderate FFI usage:**
- File I/O for reading source files
- Process management for invoking tools

### Standard Library (src/lib/)

**High FFI usage:**
- `std.fs` - All file system operations
- `std.process` - Process management
- `std.env` - Environment variables
- `std.time` - Time operations

## FFI Performance Characteristics

### Zero-Cost Abstractions (Keep in Rust)
- GC allocation/deallocation
- Bytecode interpretation
- Type checking hot paths
- Pattern matching compilation

### Negligible Overhead (Can Migrate to Simple)
- File I/O wrappers
- Path string manipulation
- Configuration parsing
- CLI argument processing
- Test utilities

### Measurement Needed
- Large-scale file operations (directory walking)
- Process spawning (benchmark vs std::process)
- JSON/YAML parsing (if migrated)

## FFI Naming Conventions

### Current Convention

| Prefix | Category | Example | Keep in Rust? |
|--------|----------|---------|---------------|
| `rt_*` | Runtime operations | `rt_file_read_text` | ✅ Yes (core runtime) |
| `sys_*` | System calls | `sys_get_args`, `sys_exit` | ✅ Yes (OS interface) |
| `native_*` | Legacy FFI | `native_fs_read_string` | ❌ Deprecated |
| `call_ffi_*` | Generic FFI | `call_ffi_2` | ✅ Yes (unsafe) |

### Proposed Convention (Future)

Consolidate to two prefixes:
- `rt.*` - Runtime operations (keep in Rust)
- `ffi.*` - External library bindings (keep in Rust)

Remove `native_*` and `sys_*`, replace with `rt.*`.

## Verification & Testing

### FFI Function Audit

**Command:**
```bash
# List all FFI functions
grep -rh "extern fn" src/ --include="*.spl" | sort | uniq

# Count FFI usage per file
grep -r "extern fn" src/ --include="*.spl" | cut -d: -f1 | sort | uniq -c | sort -rn

# Find most-used FFI functions
grep -rh "extern fn" src/ --include="*.spl" | sed 's/extern fn \([a-z_]*\).*/\1/' | sort | uniq -c | sort -rn
```

### FFI Contract Testing

Each FFI function should have:
1. **Documentation** - Purpose, parameters, return value
2. **Error handling** - What errors can occur?
3. **Test coverage** - At least one test calling the function
4. **Alternatives** - Can this be implemented in Simple?

## Migration Strategy

### Phase 1: Remove Legacy FFI (Week 1)
1. ✅ Document FFI boundaries (this document)
2. ⏳ Replace `native_fs_*` with `rt_file_*` (~18 uses)
3. ⏳ Update documentation to prefer `rt_*` prefix
4. ⏳ Add deprecation warnings to legacy functions

**Deliverable:** All application code uses modern `rt_*` FFI

### Phase 2: Consolidate Path Utilities (Week 2)
1. ⏳ Implement `std.path` module in Simple
2. ⏳ Replace `rt_path_basename` calls with `std.path.basename`
3. ⏳ Remove `rt_path_*` FFI functions

**Deliverable:** Path manipulation in pure Simple

### Phase 3: Review Package FFI (Week 3)
1. ⏳ Audit `rt_package_*` functions
2. ⏳ Migrate duplicates to existing `rt_file_*`/`rt_dir_*`
3. ⏳ Keep crypto/hash functions in Rust

**Deliverable:** Minimal package management FFI surface

### Phase 4: Document Core Boundary (Week 4)
1. ⏳ Document "must stay in Rust" functions with rationale
2. ⏳ Create FFI stability guarantees
3. ⏳ Add FFI versioning for backward compatibility

**Deliverable:** Stable FFI contract

## FFI Stability Guarantees

### Stable FFI (Will Not Change)
- `rt_file_*` - File I/O operations
- `rt_dir_*` - Directory operations
- `rt_process_*` - Process management
- `rt_env_*` - Environment variables
- `rt_time_*` - Time operations
- `call_ffi_*` - Generic FFI calls
- `rt_ptrace_*` - Debugging operations

### Unstable FFI (May Change)
- `sys_*` - Being migrated to `rt_*`
- `native_*` - Being deprecated
- `rt_package_*` - Under review

### Deprecated FFI (Will Be Removed)
- `native_fs_read_string` → Use `rt_file_read_text`
- `native_fs_write_string` → Use `rt_file_write_text`
- `native_fs_exists` → Use `rt_file_exists`

## Related Documents

- `doc/spec/rust_to_simple_ffi.md` - FFI implementation guide
- `doc/report/rust_to_simple_migration_2026-02-03.md` - Migration plan
- `rust/runtime/src/ffi/` - Rust FFI implementation
- `src/app/interpreter/ffi/` - FFI interpreter integration

---

**Status:** FFI boundary documented
**Total FFI Functions:** 549 declarations
**Migration Target:** Reduce to ~500 by removing legacy functions
**Next Steps:** Phase 1 - Remove legacy native_fs_* FFI
