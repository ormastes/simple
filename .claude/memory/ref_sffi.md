---
name: SFFI (Simple FFI) Reference
description: FFI wrapper patterns, runtime vs external library, wrapper-gen, type conversions, naming conventions
type: reference
---

## Two Patterns

## Native-counterpart gate

Before choosing SFFI, search `doc/00_llm_process/llm_wiki.md`, `src/lib/**`, and
`src/os/**` for a pure-Simple owner. In particular, “Simple embedded DB” and
“Simple SQLite” mean `std.database.pure_sql.PureDatabase`; `sqlite_sffi` is only
the C SQLite adapter. Prefer cached SMF/LSM or native database artifacts in
production, even when the requesting command runs in interpreter mode.

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
- `doc/07_guide/platform/ffi/sffi.md` — Guide

## Verification / signing — there is NONE (measured 2026-08-23)

No SFFI binding is signed, attested, or arity-verified at runtime. "Signature"
in this tree = ABI arity/type, not crypto. Loader admission is planned, not built.

- `@unsafe(reason: ..., capabilities: [ffi])` is the real tagging contract.
- The lint that requires it, `raw_sffi_call` (RAW-RT-001), is **`allow` by
  default** (`_LintMain/config_and_model.spl:230`); `deny` only under
  Robust/Critical tiers. Needs a baseline-and-ratchet, not a flip.
- `FfiManifest`/`validate_library` (`src/lib/nogc_sync_mut/ffi/ffi_signature.spl`)
  is implemented + tested but has **zero production callers** — every `dlopen`
  path admits providers unchecked.
- Unbacked extern ⇒ **silently returns nil**. 1,501 / 3,959 symbols (37.9%) are
  neither backed nor `@unsafe`-tagged.
- Authority for backing: `sh scripts/check/extern-backing-census.shs` (`nm` on
  real link artifacts). Never text-grep for a definition.
- Audit: `doc/09_report/sffi_signing_audit_2026-08-23.md`
