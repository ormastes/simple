# Audit: GC / No-GC Runtime Families

**Date:** 2026-04-04
**Feature:** Runtime family organization and compiler enforcement

## Implemented Core -- Six Runtime Families

| Family | Path | Files | Contract |
|--------|------|-------|----------|
| **common** | `src/lib/common/` | 799 | Pure functions, no mutation, no GC |
| **nogc_sync_mut** | `src/lib/nogc_sync_mut/` | 820 | Ownership-based sync mutable (hosts GC implementation itself) |
| **nogc_async_mut** | `src/lib/nogc_async_mut/` | 175 | Async mutable, no GC (actors, generators, threads) |
| **gc_async_mut** | `src/lib/gc_async_mut/` | 45 | GC + async (GPU, CUDA, Torch, ML) |
| **nogc_async_immut** | `src/lib/nogc_async_immut/` | 22 | Persistent data structures, lock-free CAS |
| **nogc_async_mut_noalloc** | `src/lib/nogc_async_mut_noalloc/` | 90 | Baremetal: no alloc, no GC, no OS |

**Compiler infrastructure:**
- `src/compiler/00.common/gc_config.spl` -- `GcMode` enum (Gc/NoGc), `GcConfig` with provenance tracking
- `src/compiler/00.common/gc_boundary.spl` -- `GcBoundaryChecker` warns on cross-mode calls/returns
- `src/compiler/55.borrow/gc_analysis/{mod,roots,barriers,escape}.spl` -- MIR-level GC safety
- `src/compiler/55.borrow/borrow_check/{mod,borrow_graph,lifetime,nll}.spl` -- Ownership checking
- `src/compiler/70.backend/target_presets.spl` -- `no_gc`/`no_std` flags for embedded targets

**Module resolution order** (both Rust and Simple compilers):
`nogc_async_mut > nogc_sync_mut > nogc_async_immut > common > gc_async_mut > nogc_async_mut_noalloc`

## Coverage Matrix

| Execution Path | GC (gc_async_mut) | No-GC (nogc_*) | Baremetal (noalloc) | Pure (common) |
|---|---|---|---|---|
| **Interpreter** | Resolved, GcMode not enforced | Full resolution | Resolves, no baremetal exec | Full |
| **Native (AOT/JIT)** | GcConfig propagated, boundary warnings, GC safety analysis | Borrow checker operates, ownership enforced | `no_gc: true`, `no_std: true` presets, baremetal CRT | No special handling |
| **Loader/SMF** | `__init__.spl` sets GcConfig, children inherit | Same inheritance, `@no_gc` attribute available | N/A | Transparent |
| **Baremetal (QEMU)** | Not supported (GC requires OS heap) | Primary mode | Full: `crt_baremetal.c` + `runtime_minimal.c`, 6 archs | Pure compute only |

## Known Limits

1. **Interpreter does not enforce GcMode** -- GC/no-GC is compile-time (native path) only
2. **gc_async_mut is smallest** (45 files) -- limited to GPU/CUDA/Torch; GC collector lives in `nogc_sync_mut/gc.spl`
3. **nogc_async_immut has zero test files** -- 22 source files lack dedicated specs
4. **nogc_async_mut_noalloc has minimal test coverage** -- 13 test files for 90 source files
5. **GC safety analysis may not be fully exercised** -- `gc_analysis/mod.spl` has non-standard method call patterns
6. **`@no_gc` attribute unused in stdlib** -- GC mode determined by directory convention, not per-file attributes
7. **C runtime has no GC collector** -- GC only works when Simple-implemented GC library is linked in native compilation

## Proof References

**Compiler:** `gc_config.spl`, `gc_boundary.spl`, `55.borrow/gc_analysis/` (4 files), `55.borrow/borrow_check/` (4 files), `target_presets.spl`
**Runtime:** `src/runtime/runtime.c`, `runtime_memtrack.c`, `startup/baremetal/` (6 arch)
**Library:** `src/lib/nogc_sync_mut/gc.spl` (mark-and-sweep GC in Simple)
**Tests:** Borrow check specs (20), GC-related specs (223), baremetal specs (41), QEMU specs (56), nogc_async_immut specs (0 -- gap)

## Recommended README Wording

> **Runtime families** -- Six stdlib tiers (`common`, `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `nogc_async_immut`, `nogc_async_mut_noalloc`) with compiler-enforced GC boundary warnings, MIR-level borrow/escape/barrier analysis, and per-target `no_gc`/`no_std` presets for embedded cross-compilation
