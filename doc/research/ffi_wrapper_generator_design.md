# FFI Wrapper Generator Design

**Status**: Implemented (Phases 1-3 complete, Phase 4 in progress)
**Date**: 2026-02-02 (updated 2026-02-10)

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

### Build Directory Layout

```
build/
  rust/                          ← Persistent Rust build environment
    rust-toolchain.toml          ← Generated from simple.sdn ffi.rust config
    ffi_gen/                     ← Generated FFI wrapper crate
      Cargo.toml                 ← Auto-generated with @Lib dependencies
      src/
        lib.rs                   ← Auto-generated extern "C" wrappers
      target/                    ← Cargo build output (cached across runs)
        release/
          libsimple_ffi_wrapper.so
```

The `build/rust/` environment is **set up once** from `simple.sdn` config and **persists
across runs** to avoid repeated Rust toolchain setup overhead. Only `--clean` removes it.

### Config in simple.sdn

```sdn
ffi:
  rust:
    channel: stable        # Rust toolchain: stable, nightly, 1.78.0, etc.
    edition: 2021          # Cargo edition for generated crates
    components: [clippy]   # Extra rustup components
```

### Generation Flow

```
Simple source with @Lib(lang: "rust", name: "regex", version: "1.10") extern class
    │
    ▼
src/app/ffi_gen/main.spl  ← The generator (written in Simple)
    │
    ├── Reads ffi.rust config from simple.sdn
    ├── Ensures build/rust/ env exists (rust-toolchain.toml)
    ├── Parses @Lib annotations + extern class/fn declarations
    ├── Dispatches to language-specific codegen backend
    │   ├── rust_codegen.spl → Rust wrapper + Cargo.toml
    │   ├── c_codegen.spl → C wrapper + build.rs (future)
    │   └── ...
    ├── Writes generated crate to build/rust/ffi_gen/
    ├── Calls cargo build (uses build/rust/rust-toolchain.toml)
    └── Outputs .so/.a in build/rust/ffi_gen/target/release/
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
  ├── Ensure build/rust/ env (from simple.sdn ffi.rust config)
  ├── Scan .spl files for @Lib annotations
  ├── For each @Lib crate:
  │   ├── Generate Rust wrapper → build/rust/ffi_gen/src/lib.rs
  │   ├── Generate Cargo.toml → build/rust/ffi_gen/Cargo.toml
  │   └── cargo build --release (uses build/rust/rust-toolchain.toml)
  ├── Link .so/.a from build/rust/ffi_gen/target/release/
  └── Continue normal Cargo build of simple_runtime
```

The `build/rust/` directory persists across builds. Only `simple ffi-gen --clean`
removes it to force a fresh Rust environment setup.

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

## Implementation Files (Actual)

### Simple App (`src/app/ffi_gen/`) — 18 core files, 3,699 lines

| File | Purpose | Lines |
|------|---------|-------|
| `main.spl` | CLI entry point, orchestration, env setup | 1,034 |
| `parser.spl` | Parse `@Lib(...)` annotations + extern decls | 310 |
| `rust_codegen.spl` | Generate Rust extern "C" wrappers | 269 |
| `cargo_gen.spl` | Generate Cargo.toml with dependencies | 60 |
| `type_mapping.spl` | Simple ↔ Rust/C type mapping rules | 115 |
| `builder.spl` | Invoke cargo build on generated crate | 31 |
| `types.spl` | Extended type specs (ImportSpec, FieldSpec, EnumVariantSpec, FnSpec, etc.) | 429 |
| `intern_codegen.spl` | Generate `interpreter_extern` Rust module from spec | 302 |
| `module_gen.spl` | Generate complete Rust module source from ModuleSpec | 172 |
| `workspace_gen.spl` | Generate multi-crate Cargo workspace (16 FFI crates) | 181 |
| `lib_gen.spl` | Generate `simple_ffi_lib` top-level crate | 78 |
| `fn_gen.spl` | Generate Rust function bodies | 137 |
| `struct_gen.spl` | Generate Rust struct definitions | 121 |
| `enum_gen.spl` | Generate Rust enum definitions | 113 |
| `impl_gen.spl` | Generate Rust impl blocks | 113 |
| `bootstrap_gen.spl` | Generate bootstrap/startup code | 57 |
| `package.spl` | Package management for FFI crates | 67 |
| `test_gen.spl` | Generate Rust test code | 110 |

### FFI Spec Files (`src/app/ffi_gen/specs/`) — 50+ files, 8,374 lines

Declarative specifications for all FFI bindings, organized by domain:

| Category | Files | Description |
|----------|-------|-------------|
| Runtime core | `runtime_value.spl`, `runtime_value_full.spl` | Value type conversions |
| GC/Memory | `gc.spl`, `gc_full.spl`, `exec_memory.spl`, `memory_syscalls.spl`, `mmap.spl`, `mmap_syscalls.spl` | Memory management |
| I/O | `file_io.spl`, `file_io_full.spl`, `io_print.spl`, `io_full.spl`, `dir_io.spl` | File/directory I/O |
| System | `system.spl`, `system_full.spl`, `system_mod.spl`, `env.spl`, `fault.spl` | System calls |
| Process | `process.spl`, `process_full.spl`, `process_mod.spl` | Process management |
| Time | `time.spl`, `time_full.spl`, `time_mod.spl` | Time functions |
| Collections | `collections.spl`, `im_rs.spl` | Collection types |
| Codegen | `cranelift_core.spl`, `cranelift_ops.spl`, `cranelift_codegen.spl`, `cranelift_advanced.spl`, `codegen_mod.spl` | Cranelift codegen |
| CLI | `cli.spl`, `cli_mod.spl`, `cargo.spl` | CLI tools |
| Network | `net_mod.spl` | Networking |
| Serialization | `json.spl`, `serde_mod.spl` | JSON/serde |
| Other | `crypto_mod.spl`, `archive_mod.spl`, `concurrent_mod.spl`, `data_mod.spl`, `glob.spl`, `treesitter.spl`, `compiler_query.spl` | Misc |

### Build System Integration

| File | Change |
|------|--------|
| `src/app/cli/main.spl` | `ffi-gen` command dispatch |
| `build/rust/` | Persistent Rust build environment |
| `simple.sdn` | `ffi.rust` config section |

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
simple ffi-gen src/user_code.spl

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

## Implementation Status

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 1 | Research document | DONE |
| Phase 2 | Simple app (`src/app/ffi_gen/`) | DONE — 18 core files, 3,699 lines |
| Phase 2.5 | `build/rust/` persistent environment + `simple.sdn` config | DONE |
| Phase 3 | Type mapping (`type_mapping.spl`) | DONE |
| Phase 3.5 | Full code generation (module_gen, workspace_gen, lib_gen, etc.) | DONE |
| Phase 3.6 | FFI spec files (50+ specs, 8,374 lines) | DONE |
| Phase 3.7 | Verification test suite | DONE |
| Phase 4 | Migrate existing wrappers (math, file_io, system, collections) | NOT STARTED |
| Phase 5 | Cross-Language LTO | NOT STARTED |
| Phase 6 | Bootstrap build integration | NOT STARTED |

**Total implementation: ~12,073 lines across 68 files.**

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
