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
- `use std.X` and `use lib.X` both resolve from `src/lib/`
- Resolver rewrites `std` → `lib` internally
- Prefer `use std.X` in new code
