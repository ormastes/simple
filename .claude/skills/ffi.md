# FFI Wrapper Generation Skill

## Overview

FFI wrappers connect Simple code to native Rust libraries. **All FFI code is generated from `.spl` spec files - never write `.rs` files manually.**

## Key Principle

```
❌ NEVER write Rust (.rs) files manually
✅ Write FFI specs in Simple (.spl), then generate
```

## Quick Reference

### Generate FFI Code

```bash
# Generate all modules
simple ffi-gen --gen-all

# Generate single module
simple ffi-gen --gen-module src/app/ffi_gen/specs/file_io.spl

# Preview without writing
simple ffi-gen --gen-all --dry-run

# Generate + verify compilation
simple ffi-gen --gen-all --verify
```

### File Locations

| What | Where |
|------|-------|
| Spec files | `src/app/ffi_gen/specs/*.spl` |
| Generator code | `src/app/ffi_gen/` |
| Generated output | `build/rust/ffi_gen/` |
| Rust toolchain config | `build/rust/rust-toolchain.toml` |

## Writing FFI Specs

### Basic Function Spec

```simple
use app.ffi_gen.intern_codegen (InternFnSpec, InternParamSpec)

fn my_module_specs() -> [InternFnSpec]:
    var specs: [InternFnSpec] = []

    specs.push(InternFnSpec(
        name: "rt_my_function",
        category: "my_module",
        params: [
            InternParamSpec(name: "path", value_type: "String"),
            InternParamSpec(name: "count", value_type: "i64")
        ],
        return_type: "bool",
        runtime_fn: "rt_my_function",
        doc: "Does something useful"
    ))

    specs
```

### Parameter Types

| Simple Type | Rust Type | Notes |
|-------------|-----------|-------|
| `String` | `*const c_char, usize` | Length-prefixed |
| `i64` | `i64` | Direct |
| `bool` | `bool` | Direct |
| `Value` | `*mut RuntimeValue` | For complex types |
| `void` | `()` | No return |

### Return Types

| Simple Type | Rust Return | Notes |
|-------------|-------------|-------|
| `String` | `*mut c_char` | Caller frees with `rt_string_free` |
| `i64` | `i64` | Direct |
| `bool` | `bool` | Direct |
| `Value` | `*mut RuntimeValue` | Runtime value pointer |
| `void` | No return | Procedure |

## Existing Spec Files

| File | Category | Functions |
|------|----------|-----------|
| `file_io.spl` | File operations | read, write, exists, copy, delete |
| `process.spl` | Process execution | run, output, shell |
| `time.spl` | Time operations | now, timestamp parsing |
| `system.spl` | System info | pid, hostname, cpu_count |
| `runtime_value_full.spl` | Runtime values | value operations |
| `gc_full.spl` | GC | malloc, collect |

## Adding New FFI Module

1. **Create spec file**: `src/app/ffi_gen/specs/my_module.spl`

2. **Define specs function**:
   ```simple
   use app.ffi_gen.intern_codegen (InternFnSpec, InternParamSpec)

   fn my_module_specs() -> [InternFnSpec]:
       var specs: [InternFnSpec] = []
       # Add function specs...
       specs
   ```

3. **Register in generator** (if full module):
   - Edit `src/app/ffi_gen/main.spl`
   - Add import and generation call

4. **Generate**:
   ```bash
   simple ffi-gen --gen-all --verify
   ```

5. **Declare in io/mod.spl**:
   ```simple
   extern fn rt_my_function(path: text, count: i64) -> bool
   ```

## Troubleshooting

### Generated code doesn't compile

```bash
# Check what's generated
simple ffi-gen --gen-all --dry-run

# Verify with cargo
simple ffi-gen --gen-all --verify
```

### Missing function in runtime

1. Check spec file has the function
2. Regenerate: `simple ffi-gen --gen-all`
3. Check `src/app/io/mod.spl` declares `extern fn`

### Clean regeneration

```bash
simple ffi-gen --clean
simple ffi-gen --gen-all --verify
```

## Configuration

In `simple.sdn`:

```sdn
ffi:
  rust:
    channel: stable    # Rust toolchain
    edition: 2021      # Cargo edition
    components: [clippy, rustfmt]
```

## See Also

- `src/app/ffi_gen/main.spl` - Generator entry point
- `src/app/ffi_gen/types.spl` - Type definitions
- `src/app/ffi_gen/rust_codegen.spl` - Rust code generation
- `doc/guide/ffi_gen_guide.md` - Full guide
