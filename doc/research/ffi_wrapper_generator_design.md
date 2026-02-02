# FFI Wrapper Generator Design

**Status**: Research / Phase 1
**Date**: 2026-02-02

## Problem

The Simple compiler has **571 manually registered extern functions** across 36 Rust modules (~12,600 lines in `rust/compiler/src/interpreter_extern/`). Each FFI function requires:

1. A Rust implementation in `interpreter_extern/*.rs`
2. A dispatch entry in `mod.rs` (1,072-line match statement)
3. An `extern fn` declaration in Simple stdlib `.spl` files

This is error-prone, tedious, and makes it difficult to bind new Rust crates.

## Goal

An **FFI wrapper generator** (written in Simple) that automates binding to external Rust/C libraries. Users annotate `extern class` with `@Lib(...)` and the generator produces compiled wrappers automatically.

## Current FFI Architecture

### Dispatch Pattern

```
Simple code → extern fn declaration → call_extern_function() → match on name string → module::function() → FFI into simple_runtime
```

### Key Types

- `Value` enum: 40+ variants (Int, Float, Bool, Str, Array, Dict, Object, Enum, etc.)
- `ExternDef`: parser AST node for `extern fn` declarations
- `ExternClassDef`: parser AST node for `extern class` with methods
- `ExternMethodKind`: Static / Immutable / Mutable

### Existing Parser Support

The parser already supports `ExternClassDef` with attributes:

```rust
// rust/parser/src/ast/nodes/definitions.rs
ExternClassDef { name, generic_params, methods, attributes, ... }
ExternMethodDef { name, kind, params, return_type, attributes, ... }
```

### Module Breakdown (36 files, 12,603 lines total)

| Category | Files | Lines | Can Auto-Generate? |
|----------|-------|-------|--------------------|
| Collections (HashMap, etc.) | collections.rs | 1,792 | Yes - mechanical wrappers |
| Atomic ops | atomic.rs | 923 | Yes - pattern-based |
| Cranelift codegen | cranelift.rs | 665 | No - complex logic |
| Concurrency | concurrency.rs | 594 | Partial |
| Coverage | coverage.rs | 576 | No - compiler integration |
| File I/O | file_io.rs | 570 | Yes - pure FFI wrappers |
| Math | math.rs | 547 | Yes - trivial wrappers |
| CLI | cli.rs | 494 | Partial - some logic |
| System | system.rs | 413 | Yes - mostly wrappers |
| Cargo | cargo.rs | 404 | Could move to Simple |
| GPU | gpu.rs | 374 | Yes - pure FFI |
| Others (20 files) | various | ~5,251 | Mixed |

## Annotation Design: `@Lib`

The annotation is **language-aware** and specifies a **downloadable package name with version**:

```simple
# Rust crate from crates.io
@Lib(lang: "rust", name: "regex", version: "1.10")
extern class Regex:
    static fn new(pattern: text) -> Regex
    fn is_match(input: text) -> bool

# Rust crate with features
@Lib(lang: "rust", name: "serde_json", version: "1.0", features: ["preserve_order"])
extern class JsonValue:
    static fn from_str(s: text) -> JsonValue
    fn to_string() -> text

# C library (system-installed)
@Lib(lang: "c", name: "sqlite3")
extern class Sqlite3:
    static fn open(path: text) -> Sqlite3
    fn exec(sql: text) -> i32
    fn close()

# C library with pkg-config name
@Lib(lang: "c", name: "libcurl", pkg_config: "libcurl")
extern class Curl:
    static fn easy_init() -> Curl
    fn set_url(url: text)
    fn perform() -> i32

# Future: Python, Go, etc.
@Lib(lang: "python", name: "numpy", version: "1.26")
extern class NdArray:
    static fn zeros(shape: [i32]) -> NdArray
    fn dot(other: NdArray) -> NdArray
```

### Annotation Fields

| Field | Required | Description |
|-------|----------|-------------|
| `lang` | Yes | Language: `"rust"`, `"c"`, `"cpp"`, `"python"` (future) |
| `name` | Yes | Package name (crate name, pkg name, pip name) |
| `version` | No | Version constraint (semver for Rust, any for others) |
| `features` | No | Language-specific features (Rust crate features, etc.) |
| `pkg_config` | No | pkg-config name for C/C++ libs |
| `link` | No | Linker flag override (e.g., `"-lsqlite3"`) |

### Language Support Roadmap

| Lang | Download From | Build Tool | Status |
|------|--------------|------------|--------|
| `rust` | crates.io | cargo | Phase 2 (first) |
| `c` | system / pkg-config | cc crate | Phase 3 |
| `cpp` | system / pkg-config | cc crate | Phase 3 |
| `python` | PyPI | pyo3/cffi | Future |
| `go` | go modules | cgo | Future |

## Architecture

```
Simple source with @Lib(lang: "rust", name: "regex", version: "1.10") extern class
    │
    ▼
src/app/ffi_gen/main.spl  ← The generator (written in Simple)
    │
    ├── Parses @Lib annotations + extern class/fn declarations
    ├── Dispatches to language-specific codegen backend
    │   ├── rust_codegen.spl → Rust wrapper + Cargo.toml
    │   ├── c_codegen.spl → C wrapper + build.rs (future)
    │   └── ...
    ├── Downloads dependency (cargo add / pkg-config / pip)
    ├── Calls build tool to compile wrapper → .so/.a
    └── Outputs extern fn dispatch entries
```

### Generated Code Pattern (Rust)

For each `extern class`, the generator produces:

```rust
#[no_mangle] pub extern "C" fn ClassName_new(...) -> *mut ClassName
#[no_mangle] pub extern "C" fn ClassName_method(ptr: *mut ClassName, ...) -> ReturnType
#[no_mangle] pub extern "C" fn ClassName_destroy(ptr: *mut ClassName)
```

### Build Integration

When `@Lib` is found during `simple build`:

```
simple build
  ├── Scan .spl files for @Lib annotations
  ├── For each @Lib crate:
  │   ├── Generate Rust wrapper (src/app/ffi_gen/)
  │   ├── Generate Cargo.toml with dependency
  │   └── cargo build --profile=<matching profile>
  ├── Link FFI .so/.a files
  └── Continue normal Cargo build of simple_runtime
```

## Type Mapping

| Simple Type | C ABI Type | Rust Type |
|-------------|-----------|-----------|
| i32 | int32_t | i32 |
| i64 | int64_t | i64 |
| f32 | float | f32 |
| f64 | double | f64 |
| bool | uint8_t | bool |
| text | *const u8 + u64 len | &str / String |
| [T] | RuntimeValue (opaque) | Vec<T> via conversion |
| Option<T> | nullable pointer | Option<T> |
| Object handle | *mut T | Box<T> raw pointer |

### String Passing

Strings cross the FFI boundary as pointer+length pairs:

```rust
// Simple → Rust: text parameter
fn wrap_method(ptr: *const u8, len: u64) {
    let s = unsafe { std::str::from_utf8_unchecked(
        std::slice::from_raw_parts(ptr, len as usize)
    )};
    // use s
}

// Rust → Simple: text return
fn wrap_returning_string() -> (*const u8, u64) {
    let s = String::from("result");
    let ptr = s.as_ptr();
    let len = s.len() as u64;
    std::mem::forget(s); // Simple runtime takes ownership
    (ptr, len)
}
```

### Object Handles

Objects are passed as opaque pointers. The generated wrapper manages lifetime:

```rust
// Construction: Box::into_raw
#[no_mangle]
pub extern "C" fn Regex_new(pattern_ptr: *const u8, pattern_len: u64) -> *mut Regex {
    let pattern = unsafe { /* ... */ };
    Box::into_raw(Box::new(Regex::new(pattern).unwrap()))
}

// Method call: borrow from raw
#[no_mangle]
pub extern "C" fn Regex_is_match(ptr: *mut Regex, input_ptr: *const u8, input_len: u64) -> u8 {
    let regex = unsafe { &*ptr };
    let input = unsafe { /* ... */ };
    regex.is_match(input) as u8
}

// Destruction: Box::from_raw + drop
#[no_mangle]
pub extern "C" fn Regex_destroy(ptr: *mut Regex) {
    unsafe { drop(Box::from_raw(ptr)); }
}
```

## Performance

### C ABI Overhead

Direct `extern "C"` calls have near-zero overhead (single indirect call). The primary cost is data marshalling:

- **Primitive types** (i32, f64, bool): Zero-copy, register-passed
- **Strings**: One pointer dereference + length check
- **Object handles**: One pointer dereference

### Cross-Language LTO (Phase 5)

With `-C linker-plugin-lto` enabled:
- LLVM can inline across Simple→Rust boundary
- Generated wrappers can be completely eliminated
- Achieves true zero-overhead FFI for Cranelift-compiled code

## Implementation Files

### Simple App (`src/app/ffi_gen/`)

| File | Purpose | Lines (est.) |
|------|---------|-------------|
| `main.spl` | CLI entry point, orchestration | ~300 |
| `parser.spl` | Parse `@Lib(...)` annotations + extern decls | ~400 |
| `rust_codegen.spl` | Generate Rust wrapper source code | ~500 |
| `c_codegen.spl` | Generate C wrapper source code (future) | ~300 |
| `cargo_gen.spl` | Generate Cargo.toml with dependency | ~150 |
| `type_mapping.spl` | Simple ↔ Rust/C type mapping rules | ~200 |
| `builder.spl` | Invoke cargo/cc build on generated crate | ~150 |

### Build System Integration

| File | Change |
|------|--------|
| `src/app/cli/main.spl` | Add `ffi-gen` command dispatch |
| `src/app/build/cli_entry.spl` | Add `ffi-gen` build subcommand |
| `src/app/build/orchestrator.spl` | Integrate FFI generation before Cargo build |
| `src/app/build/cargo.spl` | Add `build_ffi_crates()` function |
| `src/app/build/config.spl` | Add `FfiBuildConfig` struct |

## Usage Example

```simple
# user_code.spl
@Lib(lang: "rust", name: "regex", version: "1.10")
extern class Regex:
    static fn new(pattern: text) -> Regex
    fn is_match(input: text) -> bool
    fn find(input: text) -> Option<text>

fn main():
    val re = Regex.new("[0-9]+")
    if re.is_match("hello 42 world"):
        print "Found a number!"
```

```bash
# Generate wrappers
simple ffi-gen src/user_code.spl --output generated/

# Or automatically during build
simple build  # detects @Lib, generates + compiles wrappers
```

## Migration Plan for Existing Modules

Migrate existing `interpreter_extern` modules incrementally:

1. **math.rs** (547 lines) — simplest, pure function wrappers
2. **file_io.rs** (570 lines) — straightforward FFI
3. **system.rs** (413 lines) — mostly wrappers
4. **collections.rs** (1,792 lines) — object handles, more complex
5. Skip: `cranelift.rs`, `coverage.rs`, `concurrency.rs` (compiler-integrated)

Each migration:
- Write equivalent `@Lib` extern class declarations
- Verify generated wrappers match manual implementations
- Run existing tests to confirm no regression
- Remove manual Rust code

## Open Questions

1. **Error handling**: How should Rust panics/Results propagate to Simple? Options:
   - Convert `Result<T, E>` to Simple's `Result<T, E>` enum
   - Panic → Simple exception
   - Return error codes with separate error message query

2. **Generic types**: How to handle Rust generics in extern declarations?
   - Monomorphize at declaration site (user specifies concrete types)
   - Generate wrapper per instantiation

3. **Callback support**: How to pass Simple closures to Rust functions expecting `Fn`?
   - Trampoline function with context pointer
   - Requires runtime support for closure capture layout

4. **Thread safety**: How to mark extern objects as Send/Sync?
   - Annotation field: `@Lib(lang: "rust", ..., thread_safe: true)`
   - Default to non-Send (single-threaded access)
