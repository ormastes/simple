---
name: Stdlib Reference
description: Standard library directory structure, variant system matrix, memory models, capabilities, module patterns
type: reference
---

## Directory Structure
```
src/lib/
  common/             # Pure functions, no mutation
  nogc_sync_mut/      # Sync mutable, no GC (ffi, fs, net, http, spec, etc.)
  nogc_async_mut/     # Async mutable, no GC (actors, async, threads)
  gc_async_mut/       # GC + async (gpu, cuda, torch, ML)
  nogc_async_mut_noalloc/  # Baremetal, execution, memory
```

## Variant Matrix
| Directory | GC | Mutable | Use Case |
|-----------|-----|---------|----------|
| `core/` | Yes | Yes | General purpose |
| `core_immut/` | Yes | No | Persistent data |
| `core_nogc/` | No | Yes | Performance critical |
| `core_nogc_immut/` | No | No | Static allocation |

Host default: `async_nogc_mut` (Async + NoGC + Mutable)

## Capabilities
Declare in `__init__.spl`: `requires [fs, net, io]`
Available: `io`, `fs`, `net`, `unsafe`, `verify`, `trusted`
Effect decorators: `@pure`, `@io`, `@fs`, `@net`

## Module Pattern
```simple
# __init__.spl
requires [fs]
pub use .types.*
pub use .functions.*
```

## Import Resolution
- `use std.X` and `use lib.X` both resolve from `src/lib/`; resolver strips leading `std`/`std_lib`. Prefer `use std.X` in new code.
- **Two independent axes** (full detail: `doc/07_guide/compiler/modules/module_resolver.md`):
  - **Memory-model family** — chosen by fixed fallback order, NOT a config knob:
    `nogc_async_mut → nogc_sync_mut → nogc_async_immut → common → gc_async_mut → nogc_async_mut_noalloc`. First match wins; host default `async_nogc_mut`.
  - **SIMD tier** — `variants/<tier>/` (avx512/avx2/sse2…) prepended via `stdlib_variant.rs`, hardware-selected. Orthogonal to family.
- **`std.io` single-segment shim** → `nogc_sync_mut/io/__init__.spl` (`module_loader.rs` ~L229). Multi-segment `std.io.X` uses the fallback above instead.
- **Tree-neutral abstractions live in `common/`**: I/O traits `Read/Write/Seek/Close` + types `IoError/SeekFrom` → `common/io/`; JSON → `common/json/`; bcrypt → `common/bcrypt/`. Imported as `std.io.traits` / `lib.common.io.*` (both reach `src/lib/common/...`). Do NOT duplicate per family. Tree-specific *implementations* (`io/file.spl`, `io/tcp.spl`) stay in their family dir.
- A module that exists in one family but is imported by another = import debt; fix with a facade or import rewrite, never a wider cross-family fallback (`doc/03_plan/language/imports/import_warning_debt_2026-05-13.md`). The seed std `core/traits.spl` defines Rust-style `Read/Write/Seek` (no `Close`) with different signatures — do NOT conflate with `common/io`.
