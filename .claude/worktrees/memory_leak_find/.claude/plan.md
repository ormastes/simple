# Plan: Zero-Overhead FFI Wrapper Generator for Simple

## Key Change from Original Plan
**The generator is implemented in Simple (`src/app/ffi_gen/`), not Rust.** This follows the project's "Simple-first" architecture where all tooling lives in `src/app/` as `.spl` files.

## Context

571 manually registered extern functions across 35 Rust modules (~12,600 lines in `rust/compiler/src/interpreter_extern/`). Each FFI function requires:
1. A Rust implementation in `interpreter_extern/*.rs`
2. A dispatch entry in `mod.rs` (1,072-line match statement)
3. An `extern fn` declaration in Simple stdlib `.spl` files

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

**Annotation fields:**
| Field | Required | Description |
|-------|----------|-------------|
| `lang` | Yes | Language: `"rust"`, `"c"`, `"cpp"`, `"python"` (future) |
| `name` | Yes | Package name (crate name, pkg name, pip name) |
| `version` | No | Version constraint (semver for Rust, any for others) |
| `features` | No | Language-specific features (Rust crate features, etc.) |
| `pkg_config` | No | pkg-config name for C/C++ libs |
| `link` | No | Linker flag override (e.g., `"-lsqlite3"`) |

**Language support roadmap:**
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

## Implementation Plan

### Phase 1: Research Document
**Create**: `doc/research/ffi_wrapper_generator_design.md`
- Full design document with architecture, type mapping, examples

### Phase 2: Simple App — `src/app/ffi_gen/`

**Create** (following existing app patterns like `lint/`, `fix/`, `depgraph/`):

| File | Purpose | Lines (est.) |
|------|---------|-------------|
| `src/app/ffi_gen/main.spl` | CLI entry point, orchestration | ~300 |
| `src/app/ffi_gen/parser.spl` | Parse `@Lib(lang, name, version, ...)` annotations + extern decls | ~400 |
| `src/app/ffi_gen/rust_codegen.spl` | Generate Rust wrapper source code (lang: "rust") | ~500 |
| `src/app/ffi_gen/c_codegen.spl` | Generate C wrapper source code (lang: "c"/"cpp") — future | ~300 |
| `src/app/ffi_gen/cargo_gen.spl` | Generate Cargo.toml with dependency name+version | ~150 |
| `src/app/ffi_gen/type_mapping.spl` | Simple ↔ Rust/C type mapping rules | ~200 |
| `src/app/ffi_gen/builder.spl` | Invoke cargo/cc build on generated crate | ~150 |

**Pattern** (same as `lint`, `fix`, `depgraph`):
```simple
# main.spl
extern fn native_fs_read_string(path: String) -> Any
extern fn native_fs_write_string(path: String, content: String) -> Any
extern fn native_fs_exists(path: String) -> Bool
extern fn sys_get_args() -> List<String>

fn main() -> Int:
    val args = sys_get_args()
    val input_file = args[0]

    # Parse @Lib annotations + extern declarations
    val source = native_fs_read_string(input_file)
    val extern_classes = parse_lib_externs(source)

    # Generate Rust wrapper code
    val rust_source = generate_rust_wrappers(extern_classes)

    # Write and build
    native_fs_write_string("generated/src/lib.rs", rust_source)
    generate_cargo_toml("generated/Cargo.toml", extern_classes)
    build_wrapper_crate("generated/")

    return 0
```

### Phase 3: Type Mapping (in Simple)

`type_mapping.spl` defines the conversion rules:

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

### Phase 4: Migrate Existing Wrappers
Use the generator to auto-produce existing `interpreter_extern` modules:
- Start with `math.rs` (simplest — pure function wrappers)
- Then `file_io.rs`, `system.rs`
- Then `collections.rs`
- Skip: `cranelift.rs`, `coverage.rs` (compiler-integrated)

### Phase 5: Cross-Language LTO
- Enable `-C linker-plugin-lto` in Rust build
- Configure Cranelift backend to emit compatible IR

## Files to Create/Modify

### Create
- `doc/research/ffi_wrapper_generator_design.md`
- `src/app/ffi_gen/main.spl`
- `src/app/ffi_gen/parser.spl`
- `src/app/ffi_gen/rust_codegen.spl`
- `src/app/ffi_gen/c_codegen.spl` (future)
- `src/app/ffi_gen/cargo_gen.spl`
- `src/app/ffi_gen/type_mapping.spl`
- `src/app/ffi_gen/builder.spl`

### Modify
- `src/app/cli/main.spl` — add `ffi-gen` command dispatch
- `src/app/build/cli_entry.spl` — add `ffi-gen` build subcommand
- `src/app/build/orchestrator.spl` — integrate FFI generation before Cargo build
- `src/app/build/cargo.spl` — add `build_ffi_crates()` function
- `src/app/build/config.spl` — add `FfiBuildConfig` struct

### Phase 6: Bootstrap Build Integration

The FFI builder must be part of the bootstrap build so `@Lib` crates are compiled during `simple build`.

**Modify `src/app/build/cli_entry.spl`** — add `ffi-gen` case to `handle_build()`:
```simple
case "ffi-gen":
    return handle_ffi_gen(args[1:])
```

**Modify `src/app/build/orchestrator.spl`** — integrate FFI generation into the build pipeline:
- Before Cargo build, scan source files for `@Lib` annotations
- Generate Rust wrapper crates into `generated/ffi/`
- Build wrapper crates as workspace members or cdylib dependencies
- Link resulting `.so`/`.a` into the final binary

**Modify `src/app/build/cargo.spl`** — add FFI crate compilation:
- New function `build_ffi_crates(ffi_specs: [FfiSpec])` that:
  1. Generates Cargo.toml for each `@Lib` crate
  2. Generates Rust wrapper source
  3. Runs `cargo build` on the wrapper workspace
  4. Returns paths to compiled libraries

**Modify `src/app/build/config.spl`** — add FFI config:
```simple
struct FfiBuildConfig:
    enabled: bool           # --no-ffi to skip
    output_dir: text        # Default: generated/ffi/
    ffi_sources: [text]     # .spl files with @Lib
```

**Bootstrap profile consideration**: FFI-generated crates should also use the bootstrap Cargo profile when building with `--bootstrap`, so the size stays minimal.

**Build flow with FFI**:
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

### Modify `src/app/cli/main.spl`
Add `ffi-gen` as a top-level command:
```simple
case "ffi-gen":
    return run_app("src/app/ffi_gen/main.spl", args)
```

## Completed
- **Phase 1**: Research document (`doc/research/ffi_wrapper_generator_design.md`)
- **Phase 2**: Simple app (`src/app/ffi_gen/`) with CLI, parser, codegen, cargo gen, builder
- **Phase 2.5**: `build/rust/` persistent environment, `simple.sdn` ffi.rust config
- **Phase 3**: Type mapping (in `type_mapping.spl`)
- **Verification**: Test suite (`test/ffi_gen/`) — parser, codegen, e2e build tests

## Usage Example

```simple
# In user's .spl file:
@Lib(lang: "rust", name: "regex", version: "1.10")
extern class Regex:
    static fn new(pattern: text) -> Regex
    fn is_match(input: text) -> bool
    fn find(input: text) -> Option<text>

# Run generator:
# simple ffi-gen src/my_regex_wrapper.spl
```

Generator produces `generated/src/lib.rs`:
```rust
use regex::Regex as RustRegex;

#[no_mangle]
pub extern "C" fn Regex_new(pattern_ptr: *const u8, pattern_len: u64) -> *mut RustRegex {
    let pattern = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(pattern_ptr, pattern_len as usize)) };
    Box::into_raw(Box::new(RustRegex::new(pattern).unwrap()))
}

#[no_mangle]
pub extern "C" fn Regex_is_match(ptr: *mut RustRegex, input_ptr: *const u8, input_len: u64) -> u8 {
    let regex = unsafe { &*ptr };
    let input = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(input_ptr, input_len as usize)) };
    regex.is_match(input) as u8
}

#[no_mangle]
pub extern "C" fn Regex_destroy(ptr: *mut RustRegex) {
    unsafe { drop(Box::from_raw(ptr)); }
}
```
