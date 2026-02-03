# FFI Skill - Simple Language FFI Wrappers

## Overview

FFI (Foreign Function Interface) connects Simple code to native runtime functions. **All FFI wrappers are written in Simple using a two-tier pattern.**

## Key Principle

```
❌ NEVER write Rust (.rs) files manually
✅ Write FFI wrappers in Simple (.spl) using extern fn + wrapper pattern
```

## Two-Tier Pattern

Every FFI function uses two layers:

```simple
# Tier 1: Extern declaration (raw FFI binding)
extern fn rt_file_read_text(path: text) -> text

# Tier 2: Simple-friendly wrapper (idiomatic API)
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

**Why two tiers?**
1. `extern fn` - Raw binding to runtime, prefixed with `rt_`
2. Wrapper `fn` - Clean API for Simple users, handles type conversions

## Type Conversions

### Basic Types (Direct Mapping)

| Simple Type | Rust Type | Notes |
|-------------|-----------|-------|
| `i64` | `i64` | Direct |
| `i32` | `i32` | Direct |
| `bool` | `bool` | Direct |
| `f64` | `f64` | Direct |
| `text` | `String` | Automatic conversion |
| `str` | `&str` | String slice |

### Collection Types

| Simple Type | Rust Type | Notes |
|-------------|-----------|-------|
| `[text]` | `Vec<String>` | Array of strings |
| `[i64]` | `Vec<i64>` | Array of integers |
| `dict` | `HashMap` | Key-value map |

### Tuple Types (Multiple Returns)

```simple
# Extern returns tuple
extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)

# Wrapper destructures
fn process_run(cmd: text, args: [text]) -> (text, text, i64):
    rt_process_run(cmd, args)

# Usage
val (stdout, stderr, exit_code) = process_run("ls", ["-la"])
```

### Optional Types

```simple
# Extern returns optional
extern fn rt_file_read_lines(path: text) -> [text]?

# Wrapper passes through
fn file_read_lines(path: text) -> [text]?:
    rt_file_read_lines(path)

# Usage with optional chaining
val lines = file_read_lines("data.txt")
if lines.?:
    for line in lines.unwrap():
        print line
```

## Error Handling Patterns

### Pattern 1: Boolean Return

```simple
extern fn rt_file_write_text(path: text, content: text) -> bool

fn file_write(path: text, content: text) -> bool:
    rt_file_write_text(path, content)

# Usage
if not file_write("output.txt", data):
    print "Write failed"
```

### Pattern 2: Exit Code Return

```simple
extern fn rt_cli_run_lint(args: [str]) -> i64

fn cli_run_lint(args: [str]) -> i64:
    rt_cli_run_lint(args)

# Usage
val code = cli_run_lint(["--fix", "src/"])
if code != 0:
    print "Lint failed with code {code}"
```

### Pattern 3: Tuple with Error Info

```simple
extern fn rt_process_run_timeout(cmd: text, args: [text], timeout_ms: i64) -> (text, text, i32)

fn process_run_timeout(cmd: text, args: [text], timeout_ms: i64) -> (text, text, i32):
    rt_process_run_timeout(cmd, args, timeout_ms)

# Usage
val (stdout, stderr, exit_code) = process_run_timeout("slow_cmd", [], 5000)
if exit_code != 0:
    eprintln("Error: {stderr}")
```

### Pattern 4: Empty String for Failure

```simple
extern fn rt_env_get(key: text) -> text

fn env_get(key: text) -> text:
    rt_env_get(key)

# Usage
val value = env_get("MY_VAR")
if value == "":
    print "Variable not set"
```

## Adding New FFI Functions

### Step 1: Add Extern Declaration

In `src/app/io/mod.spl`:

```simple
# --- My new category ---

extern fn rt_my_function(arg1: text, arg2: i64) -> bool
```

### Step 2: Add Wrapper Function

```simple
fn my_function(arg1: text, arg2: i64) -> bool:
    rt_my_function(arg1, arg2)
```

### Step 3: Document the Category

Group related functions with section comments:

```simple
# --- Database operations ---

extern fn rt_db_connect(url: text) -> i64
extern fn rt_db_query(conn: i64, sql: text) -> dict
extern fn rt_db_close(conn: i64) -> bool

fn db_connect(url: text) -> i64:
    rt_db_connect(url)

fn db_query(conn: i64, sql: text) -> dict:
    rt_db_query(conn, sql)

fn db_close(conn: i64) -> bool:
    rt_db_close(conn)
```

### Step 4: Ensure Runtime Implementation

The `rt_` function must exist in the Rust runtime. If adding new native functions, coordinate with runtime team.

## Naming Conventions

| Convention | Example | Description |
|------------|---------|-------------|
| `rt_` prefix | `rt_file_read` | Raw extern functions |
| Category prefix | `rt_file_`, `rt_env_` | Group by functionality |
| Snake case | `file_read_text` | All function names |
| Verb first | `read_file`, `write_data` | Action-oriented names |

## Categories in io/mod.spl

| Category | Prefix | Functions |
|----------|--------|-----------|
| File | `rt_file_` | read, write, exists, copy, delete, append, hash |
| Directory | `rt_dir_` | create, list, walk, remove |
| Environment | `rt_env_` | cwd, home, get, set |
| Process | `rt_process_` | run, run_timeout, run_with_limits |
| Time | `rt_time_`, `rt_timestamp_` | now, year, month, day, hour, minute, second |
| System | `rt_getpid`, `rt_hostname` | pid, hostname, cpu_count |
| CLI | `rt_cli_` | run_file, run_tests, run_lint, etc. |
| Cargo | `rt_cargo_` | build, test, clean, check, lint, fmt |
| Coverage | `rt_coverage_` | dump_sdn, enabled, clear |
| Fault | `rt_fault_` | set_timeout, set_execution_limit |

## Best Practices

### DO

- Use the two-tier pattern consistently
- Group related functions with section comments
- Use descriptive wrapper names (remove `rt_` prefix)
- Return tuples for multiple values
- Use `bool` for success/failure
- Use `i64` for handles/IDs

### DON'T

- Write Rust files manually
- Expose `rt_` prefixed functions directly
- Use complex type conversions in wrappers
- Add business logic in wrappers (keep them thin)

## File Reference

| File | Purpose |
|------|---------|
| `src/app/io/mod.spl` | Main FFI wrapper module |
| `src/std/io/*.spl` | Stdlib I/O modules |
| `doc/guide/ffi_gen_guide.md` | Legacy FFI generation guide |

## Examples

### Complete File Operation

```simple
# Extern declarations
extern fn rt_file_exists(path: text) -> bool
extern fn rt_file_read_text(path: text) -> text
extern fn rt_file_write_text(path: text, content: text) -> bool

# Wrappers
fn file_exists(path: text) -> bool:
    rt_file_exists(path)

fn file_read(path: text) -> text:
    rt_file_read_text(path)

fn file_write(path: text, content: text) -> bool:
    rt_file_write_text(path, content)

# Usage in app code
if file_exists("config.sdn"):
    val config = file_read("config.sdn")
    # process config...
else:
    file_write("config.sdn", default_config)
```

### Process Execution

```simple
# Extern
extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)

# Wrapper
fn process_run(cmd: text, args: [text]) -> (text, text, i64):
    rt_process_run(cmd, args)

# Usage
val (stdout, stderr, code) = process_run("cargo", ["build", "--release"])
if code == 0:
    print "Build successful"
    print stdout
else:
    eprintln("Build failed: {stderr}")
```

### CLI Delegation

```simple
# Extern
extern fn rt_cli_run_tests(args: [str], gc_log: bool, gc_off: bool) -> i64

# Wrapper
fn cli_run_tests(args: [str], gc_log: bool, gc_off: bool) -> i64:
    rt_cli_run_tests(args, gc_log, gc_off)

# Usage
val exit_code = cli_run_tests(["--tag=unit"], false, false)
exit(exit_code)
```

## See Also

- `src/app/io/mod.spl` - Complete FFI wrapper implementations
- `/coding` skill - Simple language coding standards
- `doc/guide/ffi_gen_guide.md` - Legacy FFI generation (for reference)
