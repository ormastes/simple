# File I/O Unification Plan - 2026-02-05

**Goal:** Provide all file I/O features without duplication between `app.io` and `std.infra`

---

## Current State Analysis

### Module 1: `src/app/io/mod.spl` (Low-level, SFFI-based)

**Purpose:** Application-level I/O, runtime integration, CLI utilities
**Pattern:** Shell commands + runtime FFI
**API Style:** Simple return types (bool, text, tuples)

**Features:**

| Category | Functions | Return Types |
|----------|-----------|--------------|
| **File Basic** | file_exists, file_read, file_write, file_copy, file_delete | bool, text |
| **File Advanced** | file_atomic_write, file_append, file_remove, file_size | bool, i64 |
| **File Special** | file_hash_sha256, file_modified_time, file_lock, file_unlock | text, i64 |
| **File Lines** | file_read_lines | [text]? |
| **Directory** | dir_create, dir_create_all, dir_walk, dir_remove_all, dir_list, dir_remove, is_dir | bool, [text], i32 |
| **Environment** | cwd, home, env_get, env_set | text, bool |
| **Process** | process_run, process_run_timeout, process_run_with_limits, process_output, shell | tuples, text |
| **Time** | time_now_unix_micros, current_time_unix, current_time_ms | i64 |
| **Timestamp** | timestamp_year, timestamp_month, timestamp_day, timestamp_hour, timestamp_minute, timestamp_second | i64 |
| **System** | getpid, hostname, cpu_count, path_basename | i64, text |
| **Runtime FFI** | rt_file_rename, rt_sleep_ms, rt_getpid, rt_timestamp_now | Various |
| **CLI** | cli_* (35+ functions for CLI operations) | Various |
| **Math** | math_exp, math_ln, math_sqrt, math_cos, math_sin, math_random | f64 |
| **Fault** | fault_set_* (4 functions) | () |
| **Context** | context_generate, context_stats | Various |
| **Print** | eprintln | () |

**Total:** ~90+ functions

---

### Module 2: `src/std/src/infra.spl` (High-level, Result-based)

**Purpose:** Standard library file I/O with proper error handling
**Pattern:** Shell commands, Pure Simple
**API Style:** Result<T, IoError> for all fallible operations

**Features:**

| Category | Functions | Return Types |
|----------|-----------|--------------|
| **File Reading** | read_file, read_lines, read_bytes | Result<text/[text]/[i64], IoError> |
| **File Writing** | write_file, append_file, write_bytes | Result<(), IoError> |
| **File Ops** | move_file, remove_file, file_exist | Result<(), IoError>, bool |
| **Directory** | create_dir, create_dir_all, walk_dir, remove_dir, remove_dir_all | Result<() /[text], IoError> |
| **Path Utils** | stem, relative_path, path_join, current_dir | text |
| **Special** | set_current_dir | Result<(), IoError> (not implemented) |

**Total:** 16 functions

---

## Feature Gap Analysis

###  In `app.io` but NOT in `std.infra`:

**Critical Missing (High Priority):**
- `file_copy(src, dst)` - File copying
- `file_atomic_write(path, content)` - Atomic write (important for data integrity)
- `file_hash_sha256(path)` - File hashing (security/integrity)
- `file_lock(path, timeout)` / `file_unlock(handle)` - File locking (concurrency)
- `file_modified_time(path)` - Metadata access
- `file_size(path)` - File size query
- `dir_list(path)` - List directory contents (non-recursive)
- `is_dir(path)` - Check if path is directory

**Environment & System (Medium Priority):**
- `home()` - Home directory path
- `env_get(key)`, `env_set(key, value)` - Environment variables
- `getpid()`, `hostname()`, `cpu_count()` - System info
- `path_basename(path)` - Path manipulation

**Process Execution (Medium Priority):**
- `process_run(cmd, args)` - Process execution
- `process_run_timeout(cmd, args, timeout)` - With timeout
- `process_run_with_limits(...)` - With resource limits
- `process_output(cmd, args)` - Capture output
- `shell(command)` - Shell command execution

**Time Functions (Low Priority - could be separate module):**
- `time_now_unix_micros()`, `current_time_unix()`, `current_time_ms()`
- `timestamp_year/month/day/hour/minute/second()`

**Runtime FFI (Internal - not needed in std):**
- `rt_file_rename`, `rt_sleep_ms`, `rt_getpid`, `rt_timestamp_now`

**CLI Functions (Internal - not needed in std):**
- `cli_*` (35+ functions) - These are application-specific

**Math Functions (Should be in std.math, not std.infra):**
- `math_exp`, `math_ln`, `math_sqrt`, `math_cos`, `math_sin`, `math_random`

**Fault Handling (Should be in std.runtime, not std.infra):**
- `fault_set_stack_overflow_detection`, `fault_set_max_recursion_depth`
- `fault_set_timeout`, `fault_set_execution_limit`

**Other (Various):**
- `context_generate`, `context_stats`, `settlement_main`
- `eprintln` (should be in std.io)

###  In `std.infra` but NOT in `app.io`:

**Advanced File I/O:**
- `read_bytes(path)` - Binary reading (returns [i64])
- `write_bytes(path, data)` - Binary writing
- `move_file(src, dest)` - File moving (atomic)

**Path Utilities:**
- `stem(path)` - Extract filename without extension
- `relative_path(target, base)` - Compute relative paths
- `path_join(dir, file)` - Join path components

**Result Types:**
- All functions return Result<T, IoError> for proper error handling

---

## Duplication Analysis

### Duplicated Functions (Need Reconciliation):

| Feature | `app.io` | `std.infra` | Issues |
|---------|----------|-------------|--------|
| **Read file** | `file_read()` → text | `read_file()` → Result<text, E> | Different error handling |
| **Write file** | `file_write()` → bool | `write_file()` → Result<(), E> | Different error handling |
| **Append file** | `file_append()` → bool | `append_file()` → Result<(), E> | Different error handling |
| **Read lines** | `file_read_lines()` → [text]? | `read_lines()` → Result<[text], E> | Different types |
| **File exists** | `file_exists()` → bool | `file_exist()` → bool | Same, but naming |
| **Remove file** | `file_remove()` → bool | `remove_file()` → Result<(), E> | Different error handling |
| **Create dir** | `dir_create()` → bool | `create_dir()` → Result<(), E> | Different error handling |
| **Create dir all** | `dir_create_all()` → bool | `create_dir_all()` → Result<(), E> | Different error handling |
| **Walk dir** | `dir_walk()` → [text] | `walk_dir()` → Result<[text], E> | Different error handling |
| **Remove dir all** | `dir_remove_all()` → i32 | `remove_dir_all()` → Result<(), E> | Different return types |
| **Remove dir** | `dir_remove()` → bool | `remove_dir()` → Result<(), E> | Different error handling |
| **Current dir** | `cwd()` → text | `current_dir()` → text | Naming only |

**Pattern:** `app.io` uses simple returns (bool/text), `std.infra` uses Result types

---

## Unification Strategy

### Principle: Layered Architecture

```
┌─────────────────────────────────────────┐
│  src/std/src/infra.spl                  │  ← Public API (Result-based)
│  (High-level, error handling)           │
└─────────────────┬───────────────────────┘
                  │ uses
┌─────────────────▼───────────────────────┐
│  src/app/io/mod.spl                     │  ← Internal (bool/text)
│  (Low-level, shell commands, FFI)       │
└─────────────────────────────────────────┘
```

**Design:**
1. **`app.io`** - Keep as low-level internal implementation
2. **`std.infra`** - Expand to provide ALL user-facing file I/O with Result types
3. **`std.infra`** wraps `app.io` functions and adds Result error handling

---

## Implementation Plan

### Phase 1: Add Missing Core Features to `std.infra`

**File Operations:**
```simple
fn copy_file(src: text, dest: text) -> Result<(), IoError>
fn atomic_write(path: text, content: text) -> Result<(), IoError>
fn file_size(path: text) -> Result<i64, IoError>
fn file_hash(path: text) -> Result<text, IoError>
fn modified_time(path: text) -> Result<i64, IoError>
fn lock_file(path: text, timeout_secs: i64) -> Result<i64, IoError>
fn unlock_file(handle: i64) -> Result<(), IoError>
```

**Directory Operations:**
```simple
fn list_dir(path: text) -> Result<[text], IoError>
fn is_directory(path: text) -> Result<bool, IoError>
```

**Environment:**
```simple
fn home_dir() -> Result<text, IoError>
fn get_env(key: text) -> text?  # None if not set
fn set_env(key: text, value: text) -> Result<(), IoError>
```

**System Info:**
```simple
fn get_pid() -> i64
fn get_hostname() -> text
fn get_cpu_count() -> i64
fn basename(path: text) -> text
```

**Process Execution:**
```simple
struct ProcessResult:
    stdout: text
    stderr: text
    exit_code: i64

fn run_process(cmd: text, args: [text]) -> Result<ProcessResult, IoError>
fn run_with_timeout(cmd: text, args: [text], timeout_ms: i64) -> Result<ProcessResult, IoError>
fn run_with_limits(cmd: text, args: [text], limits: ProcessLimits) -> Result<ProcessResult, IoError>
fn run_shell(command: text) -> Result<ProcessResult, IoError>
```

### Phase 2: Export Organization

**`std.infra` exports (organized):**
```simple
# File reading
export read_file, read_lines, read_bytes

# File writing
export write_file, append_file, write_bytes

# File operations
export copy_file, move_file, remove_file, atomic_write
export file_exist, file_size, file_hash, modified_time

# File locking
export lock_file, unlock_file

# Directory operations
export create_dir, create_dir_all, list_dir, walk_dir
export remove_dir, remove_dir_all, is_directory

# Path utilities
export stem, basename, relative_path, path_join, current_dir

# Environment
export home_dir, get_env, set_env

# System info
export get_pid, get_hostname, get_cpu_count

# Process execution
export ProcessResult, ProcessLimits
export run_process, run_with_timeout, run_with_limits, run_shell

# Error types
export IoError
```

### Phase 3: Deprecation Strategy

1. **Keep `app.io` as-is** - Internal use only
2. **Update all code to use `std.infra`** - Public API
3. **Add deprecation warnings** to direct `app.io` imports (if any exist)

### Phase 4: Module Separation (Optional, future)

Consider splitting `std.infra` into focused modules:
- `std.fs` - File system operations
- `std.path` - Path utilities
- `std.env` - Environment variables
- `std.process` - Process execution
- `std.system` - System information

---

## Migration Examples

### Before (app.io):
```simple
use app.io.{file_read, file_write}

fn main():
    val content = file_read("/tmp/test.txt")  # Returns empty string on error
    val success = file_write("/tmp/out.txt", content)  # Returns bool
    if not success:
        print "Error writing file"
```

### After (std.infra):
```simple
use std.infra.{read_file, write_file}

fn main():
    match read_file("/tmp/test.txt"):
        Ok(content):
            match write_file("/tmp/out.txt", content):
                Ok(_):
                    print "Success"
                Err(e):
                    print "Error writing file: {e.message}"
        Err(e):
            print "Error reading file: {e.message}"
```

---

## Implementation Checklist

### Phase 1: Core Features (High Priority)

- [ ] `copy_file()` - Wrap `file_copy()`
- [ ] `atomic_write()` - Wrap `file_atomic_write()`
- [ ] `file_size()` - Wrap `file_size_raw()`
- [ ] `file_hash()` - Implement SHA256 (or wrap if available)
- [ ] `modified_time()` - Wrap `file_modified_time()`
- [ ] `lock_file()` / `unlock_file()` - Wrap file lock functions
- [ ] `list_dir()` - Wrap `dir_list()`
- [ ] `is_directory()` - Wrap `is_dir()`
- [ ] `home_dir()` - Wrap `home()`
- [ ] `get_env()` / `set_env()` - Wrap environment functions
- [ ] `get_pid()` - Wrap `getpid()`
- [ ] `get_hostname()` - Wrap `hostname()`
- [ ] `get_cpu_count()` - Wrap `cpu_count()`
- [ ] `basename()` - Wrap `path_basename()`

### Phase 2: Process Execution

- [ ] Define `ProcessResult` struct (reuse existing)
- [ ] Define `ProcessLimits` struct
- [ ] `run_process()` - Wrap `process_run()`
- [ ] `run_with_timeout()` - Wrap `process_run_timeout()`
- [ ] `run_with_limits()` - Wrap `process_run_with_limits()`
- [ ] `run_shell()` - Wrap `shell()`

### Phase 3: Documentation

- [ ] Update `std.infra` module docs
- [ ] Add migration guide
- [ ] Update examples in tests
- [ ] Create feature matrix documentation

### Phase 4: Testing

- [ ] Add tests for all new functions
- [ ] Verify Result error handling
- [ ] Test edge cases (permissions, missing files, etc.)
- [ ] Performance benchmarks

---

## Timeline

- **Phase 1:** Core features - 1 session (this session)
- **Phase 2:** Process execution - 1 session
- **Phase 3:** Documentation - Ongoing
- **Phase 4:** Testing - Ongoing

---

## Benefits

1. ✅ **Single Public API** - Users only import from `std.infra`
2. ✅ **Consistent Error Handling** - All functions use Result types
3. ✅ **No Duplication** - Clear separation (internal vs public)
4. ✅ **Better DX** - Result types enable proper error handling
5. ✅ **Maintainability** - Changes in `app.io` don't affect public API
6. ✅ **Extensibility** - Easy to add new features to `std.infra`

---

## Status

**Current:** Analysis complete, plan created
**Next:** Implement Phase 1 - Add missing core features to `std.infra`
