---
name: SFFI (Simple FFI) Reference
description: FFI wrapper patterns, runtime vs external library, wrapper-gen, type conversions, naming conventions
type: reference
---

## Two Patterns

### Runtime Pattern (built-ins)
```simple
extern fn rt_file_read_text(path: text) -> text   # Raw FFI, rt_ prefix
fn file_read(path: text) -> text:                  # Wrapper, clean name
    rt_file_read_text(path)
```
Location: `src/lib/ffi/` (externs), `src/app/io/mod.spl` (wrappers)

### External Library Pattern (C++/Rust libs)
`Simple API (mod.spl) → SFFI Bindings (ffi.spl, extern fn) → Native Wrapper (lib.rs) → External Lib`
- `lang: cpp` → cxx bridge + C++ (bridge.h, bridge.cpp, lib.rs)
- `lang: rust` → Handle table + Rust FFI (lib.rs only)

## Wrapper Generator
```bash
simple wrapper-gen lib.wrapper_spec [--dry-run] [--verify]
```
Output: `.build/rust/ffi_<lib>/` (Cargo.toml + src/lib.rs)

## Type Conversions
| Simple | Rust | C ABI |
|--------|------|-------|
| i64/i32/bool/f64 | same | same |
| text | String | `*const c_char` |
| Handle | — | i64 (0=invalid) |
| [text] | Vec<String> | — |

## Naming Conventions
- `rt_` prefix for extern fns, category prefix (`rt_file_`, `rt_env_`, `rt_process_`)
- Snake case, verb first (`read_file`, `write_data`)

## Key Files
- `src/lib/ffi/` — Centralized extern declarations
- `src/app/io/mod.spl` — I/O wrappers
- `src/app/wrapper_gen/` — Generator (mod.spl, spec_parser.spl)
- `doc/07_guide/ffi/sffi.md` — Guide
