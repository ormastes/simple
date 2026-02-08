# SFFI Skill - Simple FFI Wrappers

## Overview

**SFFI (Simple FFI)** is the Simple language's approach to FFI wrappers. SFFI provides **two patterns**:

1. **Two-Tier Pattern**: For runtime built-ins (file I/O, process, etc.)
2. **Three-Tier Pattern**: For external libraries (C++ libs, Rust crates, etc.)

**Terminology:**
- **SFFI**: Simple FFI - FFI wrappers written in Simple
- **Raw FFI**: Direct `extern fn` declarations
- **SFFI wrapper**: The Simple wrapper function
- **wrapper-gen**: Tool to generate native wrappers from `.wrapper_spec` files

## Key Principle

```
✅ Write SFFI wrappers in Simple (.spl) using extern fn + wrapper pattern
✅ Use `simple wrapper-gen` to generate Tier 1 native code from specs
✅ For C++ libraries, use three-tier pattern with `lang: cpp`
✅ For Rust crates, use three-tier pattern with `lang: rust`
```

## Two-Tier Pattern (Runtime Built-ins)

Use this for functionality **built into** the Simple runtime:

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

**Location**: `src/app/io/mod.spl`

## Three-Tier Pattern (External Libraries)

Use this for **external** libraries NOT in the runtime. Supports two Tier 1 backends:

| Backend | `lang` field | Use case | Tier 1 output |
|---------|-------------|----------|---------------|
| **C++** | `lang: cpp` (default) | C/C++ libraries (PyTorch, OpenCV, SQLite) | cxx bridge + C++ (`bridge.h`, `bridge.cpp`, `lib.rs`) |
| **Rust** | `lang: rust` | Rust crates (regex, reqwest, gilrs) | Handle table + Rust FFI (`lib.rs` only) |

```
┌──────────────────────────────────┐
│ Tier 3: Simple API (mod.spl)    │  <- User code
│   class Tensor:                  │
│     fn zeros(shape) -> Tensor    │
└─────────────┬────────────────────┘
              │ calls
┌─────────────▼────────────────────┐
│ Tier 2: SFFI Bindings (ffi.spl) │  <- extern fn
│   extern fn rt_torch_zeros()     │
└─────────────┬────────────────────┘
              │ links to
┌─────────────▼────────────────────┐
│ Tier 1: Native Wrapper (lib.rs) │  <- Memory safety
│   lang: cpp  -> cxx bridge + C++ │
│   lang: rust -> Handle table     │
│   #[no_mangle] extern "C"        │
└─────────────┬────────────────────┘
              │ links to
┌─────────────▼────────────────────┐
│ Tier 0: External Library          │
│   C++: libtorch.so               │
│   Rust: regex crate              │
└──────────────────────────────────┘
```

**Key Principles**:
1. **Tier 1 is THIN**: Only memory safety, no business logic
2. **Tier 2 is MINIMAL**: Just `extern fn` declarations
3. **Tier 3 is RICH**: Full idiomatic Simple API with RAII
4. **All logic in Simple**: Don't put business logic in native wrapper
5. **Backend is transparent**: Tiers 2 and 3 are identical regardless of `lang`

## Wrapper Spec Format (`.wrapper_spec`)

```yaml
wrapper_lib:
    name: regex                    # Library name
    version: 0.1.0                 # Wrapper version
    lang: rust                     # Backend: "cpp" (default) or "rust"
    rust_crate: regex              # Rust crate name (lang: rust only)
    rust_crate_version: 1          # Rust crate version (lang: rust only)
    link: [torch, c10]            # Link libraries (lang: cpp only)
    search_paths: ["/usr/local/lib"]  # Library search paths (lang: cpp only)
    cpp_include: "torch/torch.h"  # C++ header (lang: cpp only)
    include_paths: ["/opt/include"]   # Include paths (lang: cpp only)

handle_types:
    - name: RegexHandle
      cpp_type: "regex::Regex"     # Underlying type
      drop_fn: "drop"

functions:
    - name: new
      cpp_fn: "regex::Regex::new"
      params:
          - name: pattern
            type: text
      return: RegexHandle

methods:
    - handle: RegexHandle
      name: is_match
      cpp_method: "is_match"
      params:
          - name: text
            type: text
      return: bool
```

## Wrapper Generator (`wrapper-gen`)

```bash
# Generate all tiers (backend auto-detected from lang field)
simple wrapper-gen torch.wrapper_spec           # lang: cpp
simple wrapper-gen regex.wrapper_spec           # lang: rust

# Generate specific tier
simple wrapper-gen regex.wrapper_spec --tier=1  # Only Tier 1

# Preview without writing files
simple wrapper-gen regex.wrapper_spec --dry-run --verbose

# Verify generated Rust compiles
simple wrapper-gen regex.wrapper_spec --verify
```

**Output by backend:**

| Backend | Tier 1 output location | Files |
|---------|----------------------|-------|
| `lang: cpp` | `.build/rust/ffi_<lib>/` | `Cargo.toml`, `build.rs`, `src/lib.rs`, `bridge.h`, `bridge.cpp` |
| `lang: rust` | `.build/rust/ffi_<lib>/` | `Cargo.toml`, `src/lib.rs` |

### Rust Backend: Handle Table Pattern

For `lang: rust`, Tier 1 uses a handle table pattern:
- `HashMap<i64, RustObject>` stores live objects
- `AtomicI64` counter for unique handle IDs
- All functions take/return `i64` handles (not raw pointers)
- Thread-safe via `Mutex`

```rust
// Auto-generated for each handle type
static REGEXHANDLE_NEXT_ID: AtomicI64 = AtomicI64::new(1);
static REGEXHANDLE_HANDLES: Mutex<Option<HashMap<i64, regex::Regex>>> = Mutex::new(None);

#[no_mangle]
pub extern "C" fn rt_regex_new(pattern: *const c_char) -> i64 {
    let pattern_s = unsafe { cstr_to_str(pattern) };
    match regex::Regex::new(pattern_s) {
        Ok(result) => regexhandle_alloc(result),
        Err(_) => 0,  // 0 = invalid handle
    }
}
```

### C++ Backend: cxx Bridge Pattern

For `lang: cpp`, Tier 1 uses the cxx bridge pattern:
- `bridge.h` / `bridge.cpp` for C++ side
- `lib.rs` with `#[cxx::bridge]` for Rust side
- Links to system C++ libraries

## Type Conversions

### Basic Types (Direct Mapping)

| Simple Type | Rust Type | C ABI Type | Notes |
|-------------|-----------|------------|-------|
| `i64` | `i64` | `i64` | Direct |
| `i32` | `i32` | `i32` | Direct |
| `bool` | `bool` | `bool` | Direct |
| `f64` | `f64` | `f64` | Direct |
| `text` | `String` | `*const c_char` / `*mut c_char` | Auto conversion |

### Collection Types

| Simple Type | Rust Type | Notes |
|-------------|-----------|-------|
| `[text]` | `Vec<String>` | Array of strings |
| `[i64]` | `Vec<i64>` | Array of integers |
| `dict` | `HashMap` | Key-value map |

### Handle Types

| Simple Type | C ABI Type | Notes |
|-------------|------------|-------|
| Handle (e.g. `RegexHandle`) | `i64` | Handle ID (0 = invalid) |

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

if not file_write("output.txt", data):
    print "Write failed"
```

### Pattern 2: Exit Code Return

```simple
extern fn rt_cli_run_lint(args: [str]) -> i64

fn cli_run_lint(args: [str]) -> i64:
    rt_cli_run_lint(args)

val code = cli_run_lint(["--fix", "src/"])
if code != 0:
    print "Lint failed with code {code}"
```

### Pattern 3: Tuple with Error Info

```simple
extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)

fn process_run(cmd: text, args: [text]) -> (text, text, i64):
    rt_process_run(cmd, args)

val (stdout, stderr, exit_code) = process_run("cmd", [])
```

### Pattern 4: Empty String for Failure

```simple
extern fn rt_env_get(key: text) -> text

fn env_get(key: text) -> text:
    rt_env_get(key)

val value = env_get("MY_VAR")
if value == "":
    print "Variable not set"
```

## Adding New SFFI Functions

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

## Adding External Library Wrappers

### Step 1: Create Wrapper Spec

Create `examples/<lib>.wrapper_spec`:

```yaml
wrapper_lib:
    name: mylib
    version: 0.1.0
    lang: rust               # or cpp
    rust_crate: my-rust-crate
    rust_crate_version: 1.0

handle_types:
    - name: MyHandle
      cpp_type: "my_crate::MyType"
      drop_fn: "drop"

functions:
    - name: create
      cpp_fn: "my_crate::MyType::new"
      params: []
      return: MyHandle

methods:
    - handle: MyHandle
      name: do_thing
      cpp_method: "do_thing"
      params:
          - name: input
            type: text
      return: text
```

### Step 2: Generate Tiers

```bash
simple wrapper-gen examples/mylib.wrapper_spec --dry-run   # Preview
simple wrapper-gen examples/mylib.wrapper_spec              # Generate
```

### Step 3: Build Tier 1

```bash
cd .build/rust/ffi_mylib && cargo build --release
```

### Step 4: Write Tests

```simple
# test/lib/mylib_spec.spl
use std.spec.{describe, it, expect}
use lib.mylib.*

describe "MyLib":
    it "creates and uses handle":
        val h = mylib_create()
        val result = mylib_do_thing(h, "input")
        expect(result).to_equal("expected")
```

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

- Use the two-tier pattern consistently for runtime built-ins
- Use three-tier pattern with `lang` field for external libraries
- Group related functions with section comments
- Use descriptive wrapper names (remove `rt_` prefix)
- Return tuples for multiple values
- Use `bool` for success/failure
- Use `i64` for handles/IDs (0 = invalid handle)

### DON'T

- Expose `rt_` prefixed functions directly (use SFFI wrappers)
- Use complex type conversions in wrappers
- Add business logic in wrappers (keep them thin)
- Mix C++ and Rust backends in the same wrapper spec

## File Reference

| File | Purpose |
|------|---------|
| `src/app/io/mod.spl` | Main SFFI wrapper module (two-tier) |
| `src/app/io/*_ffi.spl` | Per-library SFFI modules (regex, http, gamepad, etc.) |
| `src/app/wrapper_gen/mod.spl` | Wrapper generator main entry point |
| `src/app/wrapper_gen/spec_parser.spl` | `.wrapper_spec` parser |
| `src/app/wrapper_gen/tier1_gen.spl` | Tier 1 generator (C++ backend: cxx bridge) |
| `src/app/wrapper_gen/tier1_rust_gen.spl` | Tier 1 generator (Rust backend: handle tables) |
| `src/app/wrapper_gen/tier2_gen.spl` | Tier 2 generator (Simple `extern fn` declarations) |
| `src/app/wrapper_gen/tier3_gen.spl` | Tier 3 generator (Simple API scaffold) |
| `examples/torch.wrapper_spec` | Example: C++ library (PyTorch) |
| `examples/regex.wrapper_spec` | Example: Rust crate (regex) |
| `doc/design/sffi_external_library_pattern.md` | Design document |
| `doc/guide/sffi_gen_guide.md` | SFFI generation guide |

## SFFI vs Raw FFI

| Aspect | SFFI (Simple FFI) | Raw FFI |
|--------|-------------------|---------|
| **Where** | Simple code (.spl) | Rust code (.rs) |
| **Pattern** | Two-tier or three-tier | Direct FFI |
| **Prefix** | `rt_` for extern, clean name for wrapper | `rt_` exposed directly |
| **Generation** | `simple wrapper-gen` from specs | Manual code |
| **Example** | `fn file_read()` calls `extern fn rt_file_read()` | Direct `pub extern "C" fn rt_file_read()` |

**Use SFFI for**: User-facing APIs, type conversions, Simple idioms
**Use Raw FFI for**: Performance-critical paths, direct C interop

## See Also

- `src/app/io/mod.spl` - Complete SFFI wrapper implementations
- `/coding` skill - Simple language coding standards
- `doc/guide/sffi_gen_guide.md` - SFFI generation guide
- `doc/design/sffi_external_library_pattern.md` - Three-tier design
