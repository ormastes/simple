# CUDA driver: dynamic load (no link-time dependency)

Plan: `doc/03_plan/release/1.0.0/robust_boundaries_library_units_sffi_backends_plan_2026-11-15.md`
(Optional Backend Hardening). Module: `src/lib/gc_async_mut/cuda/driver_loader.spl`.

## Contract

- A binary with CUDA support never links `nvcuda`/`libcuda`. The driver is
  opened at first GPU use: `nvcuda.dll` (Windows), `libcuda.so.1` then
  `libcuda.so` (Linux/FreeBSD). macOS has no CUDA driver (empty candidate list).
- The binary therefore starts on a machine without CUDA. The first GPU use
  returns a named error instead of crashing:
  - `CUDA-E001` — no driver library could be loaded (names every candidate).
  - `CUDA-E002` — the library loaded but a required symbol is missing (names
    the library and the symbol; usually a driver older than the API we use).
- Required symbols are resolved **once**, all-or-nothing. A partial table is
  never published.

## Publication (lockless)

State lives in an `AtomicI64` (0 unresolved, 1 resolving, 2 published).
A caller that sees 2 returns the published result. Otherwise it resolves
(idempotent — the OS loader refcounts the library), then tries `CAS 0 -> 1`; the
winner writes the immutable result and `store(2, Release)`. A loser never waits:
it returns the published result if state is already 2, else its own. No mutex, no spin.

## Layering

Pure Simple over the existing hardened SFFI owner
(`std.nogc_sync_mut.sffi.dynamic.DynLib`), which already wraps
`LoadLibrary`/`dlopen`. No new C. The existing C provider
(`src/runtime/providers/cuda/bitmap_provider_v1.c`) and the Rust seed
(`cuda_runtime.rs`, `libloading` + `OnceLock`) already load dynamically and are
unchanged.
