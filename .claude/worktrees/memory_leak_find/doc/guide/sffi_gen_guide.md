# SFFI Guide (Simple FFI)

## Overview

Simple uses a **Simple-first approach** for FFI wrappers, called **SFFI (Simple FFI)**. All SFFI wrappers are written directly in Simple using the two-tier pattern.

**Primary approach: SFFI Wrappers** (see `/sffi` skill)

```simple
# In src/app/io/mod.spl

# Tier 1: Extern declaration
extern fn rt_file_read_text(path: text) -> text

# Tier 2: Wrapper function
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

## Why SFFI (Simple-First FFI)?

1. **Single source of truth** - FFI defined in Simple, not Rust
2. **Consistency** - All SFFI wrappers follow the two-tier pattern
3. **Maintainability** - Edit `.spl` files, not `.rs` files
4. **Type safety** - Simple compiler validates types
5. **Documentation** - Self-documenting Simple code
6. **Clear distinction** - SFFI wrappers vs raw FFI code

**Terminology:**
- **SFFI (Simple FFI)**: FFI wrappers written in Simple
- **SFFI wrapper**: The two-tier pattern (extern fn + wrapper)
- **SFFI-gen**: Tool to generate Rust FFI from specs
- **Raw FFI**: Direct Rust FFI code (low-level only)

---

## SSFFI Code Generation

For generating Rust boilerplate from SSFFI specs (advanced use cases only):

## Quick Start

### Generate All SFFI Modules

```bash
simple ssffi-gen --gen-all
```

This generates all SSFFI modules from specs in `src/app/ffi_gen/specs/` to `build/rust/ffi_gen/`.

### Preview Generated Code

```bash
simple ssffi-gen --gen-all --dry-run
```

### Generate and Verify

```bash
simple sffi-gen --gen-all --verify
```

This runs `cargo check` on the generated code to ensure it compiles.

## Architecture

```
src/app/ffi_gen/
├── main.spl              # Entry point, CLI handling
├── parser.spl            # Parse @Lib annotations
├── types.spl             # Type definitions (ModuleSpec, etc.)
├── rust_codegen.spl      # Generate Rust source
├── cargo_gen.spl         # Generate Cargo.toml
├── module_gen.spl        # Generate module files
├── workspace_gen.spl     # Generate workspace config
├── intern_codegen.spl    # Generate interpreter extern modules
└── specs/                # SFFI specifications
    ├── file_io.spl
    ├── process.spl
    ├── time.spl
    ├── system.spl
    ├── runtime_value_full.spl
    └── gc_full.spl

build/rust/ffi_gen/       # Generated output
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── runtime_value.rs
    ├── gc.rs
    ├── file_io.rs
    └── ...
```

## Writing FFI Specs

### InternFnSpec Structure

Each FFI function is defined using `InternFnSpec`:

```simple
use app.ffi_gen.intern_codegen (InternFnSpec, InternParamSpec)

fn my_specs() -> [InternFnSpec]:
    var specs: [InternFnSpec] = []

    specs.push(InternFnSpec(
        name: "rt_file_read_text",      # Extern function name
        category: "file_io",             # Module category
        params: [                        # Parameters
            InternParamSpec(name: "path", value_type: "String")
        ],
        return_type: "String",           # Return type
        runtime_fn: "rt_file_read_text", # Runtime function name
        doc: "Read entire file as text"  # Documentation
    ))

    specs
```

### Parameter Types

| Spec Type | Simple Type | Rust FFI Type |
|-----------|-------------|---------------|
| `String` | `text` | `*const c_char, usize` |
| `i64` | `i64` | `i64` |
| `i32` | `i32` | `i32` |
| `bool` | `bool` | `bool` |
| `f64` | `f64` | `f64` |
| `Value` | `any` | `*mut RuntimeValue` |

### Return Types

| Spec Type | Generated Rust |
|-----------|----------------|
| `void` | No return value |
| `String` | `*mut c_char` (caller frees) |
| `i64` | `i64` |
| `bool` | `bool` |
| `Value` | `*mut RuntimeValue` |

## Adding New FFI Functions

### Step 1: Create or Edit Spec File

Create `src/app/ffi_gen/specs/my_module.spl`:

```simple
# My Module - FFI Spec
use app.ffi_gen.intern_codegen (InternFnSpec, InternParamSpec)

fn my_module_specs() -> [InternFnSpec]:
    var specs: [InternFnSpec] = []

    specs.push(InternFnSpec(
        name: "rt_my_function",
        category: "my_module",
        params: [
            InternParamSpec(name: "input", value_type: "String"),
            InternParamSpec(name: "count", value_type: "i64")
        ],
        return_type: "bool",
        runtime_fn: "rt_my_function",
        doc: "Process input and return success"
    ))

    specs
```

### Step 2: Register in Generator (for full modules)

Edit `src/app/ffi_gen/main.spl` to import and use your spec.

### Step 3: Generate

```bash
simple sffi-gen --gen-all --verify
```

### Step 4: Declare Extern in Simple

In `src/app/io/mod.spl`:

```simple
extern fn rt_my_function(input: text, count: i64) -> bool

fn my_function(input: text, count: i64) -> bool:
    rt_my_function(input, count)
```

## Full Module Specs

For complete modules with structs, enums, and impls, use `ModuleSpec`:

```simple
use app.ffi_gen.types*

fn my_full_module() -> ModuleSpec:
    var module = ModuleSpec.empty("my_module")

    # Add uses
    module.uses.push("std::ffi::CString")

    # Add structs
    module.structs.push(StructSpec(
        name: "MyStruct",
        fields: [
            FieldSpec(name: "value", field_type: "i64", public: true)
        ]
    ))

    # Add functions
    module.functions.push(FnSpec(
        name: "rt_my_create",
        params: [],
        return_type: "*mut MyStruct",
        body: "Box::into_raw(Box::new(MyStruct { value: 0 }))",
        no_mangle: true,
        extern_c: true
    ))

    module
```

## Configuration

### simple.sdn

```sdn
ffi:
  rust:
    channel: stable       # Rust toolchain channel
    edition: 2021         # Cargo edition year
    components: [clippy]  # Extra rustup components
```

### Generated rust-toolchain.toml

The generator creates `build/rust/rust-toolchain.toml` based on your config:

```toml
[toolchain]
channel = "stable"
components = ["clippy"]
```

## Commands Reference

| Command | Description |
|---------|-------------|
| `simple sffi-gen --gen-all` | Generate all modules |
| `simple sffi-gen --gen-module <spec>` | Generate single module |
| `simple sffi-gen --gen-intern <spec>` | Generate interpreter extern |
| `simple sffi-gen --dry-run` | Preview without writing |
| `simple sffi-gen --verify` | Run cargo check after |
| `simple sffi-gen --clean` | Remove and recreate build/rust/ |
| `simple sffi-gen --verbose` | Verbose output |
| `simple sffi-gen --help` | Show all options |

## Troubleshooting

### "No @Lib annotations found"

For `--gen-intern` mode, ensure your spec file defines a function returning `[InternFnSpec]`.

### Cargo check fails

1. Check generated code: `simple sffi-gen --gen-all --dry-run`
2. Look for type mismatches in specs
3. Ensure all dependencies are declared

### Missing runtime function

1. Verify spec has the function
2. Regenerate: `simple sffi-gen --gen-all`
3. Check `src/app/io/mod.spl` has matching `extern fn`

### Clean slate

```bash
simple sffi-gen --clean
simple sffi-gen --gen-all --verify
```

## Best Practices

1. **One category per spec file** - Keep specs focused
2. **Document all functions** - Use `doc` field in specs
3. **Verify after changes** - Always run with `--verify`
4. **Preview first** - Use `--dry-run` before generating
5. **Match signatures exactly** - Spec must match `extern fn` in io/mod.spl

## Recommended Approach

**For most FFI needs, use the Simple-first approach:**

1. Add `extern fn rt_...` declaration to `src/app/io/mod.spl`
2. Add wrapper function with clean name
3. Done - no code generation needed

**Use FFI generation only for:**
- Generating large amounts of boilerplate Rust code
- Complex struct/enum definitions that need Rust representation
- Bootstrap tooling that requires generated Rust

## See Also

- `/ffi` skill - **Primary reference** for Simple FFI wrappers
- `src/app/io/mod.spl` - Main FFI wrapper module (extern declarations)
- `src/app/ffi_gen/specs/` - Spec files for code generation (legacy)
- `CLAUDE.md` - FFI Wrappers section
