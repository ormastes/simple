## Closed 2026-09-13 — already fixed, verified by running (MEASURED)

The "Required fix" in this entry has landed. The interpreter now resolves and
executes the mutable-span SIMD externs, and the Simple side routes through them
with a scalar fallback.

Static wiring (all present at 2026-09-13):

- interpreter bridge — `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2091-2095`
  registers `rt_engine2d_simd_fill_row_u32`, `..._fill_rows_u32`,
  `..._fill_span_u32`, `..._copy_span_u32`, `..._blend_span_u32`
- implementation — `interpreter_extern/simd.rs:1474` `rt_engine2d_simd_fill_span_u32`
  unpacks, fills via `sffi_fill_row_u32`, and repacks
- MIR lowering — `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1390`
- LLVM decls — `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:190-191`
- Simple routing — `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:1406,1439`
  (`self.buf = rt_engine2d_simd_fill_span_u32(...)`), gated by
  `native_pixel_rows_enabled`, with `_scalar_fill_row` as the documented fallback

Measured on Windows x86_64 with the Rust seed `bin/simple.exe`
(`Simple Language v1.0.0-rc.1`):
`bin/simple.exe run src/app/test/engine2d_jit_timing_probe.spl` → exit 0, all
`TIMING kernel=fill_const|src_over|copy_span ... engine=jit` rows emitted for
buckets 64..16384. The externs resolve and execute; there is no unknown-extern
failure and no native/interpreter split.

Design note, stated rather than hidden: the resolution is a **value-returning**
bridge (`dst` in, new array out), not in-place mutation of
`Value::Array(Arc<Vec<Value>>)`. The entry's literal claim — that the by-value
bridge cannot mutate the caller's array in place — is still true; it was
resolved by changing the contract, which the entry's own "Required fix" allows.

Perf observation, NOT part of this entry and not a regression against anything
it claims: under the interpreter/JIT the SIMD path measures ~14-40x SLOWER than
the scalar path (e.g. bucket=16384 `fill_const` scalar 1,915,000 ns vs simd
77,652,000 ns), which is the expected Value pack/unpack cost of an interpreted
extern. Native-lane ratios were not measured here.

---

# CPU SIMD mutable array extern wiring

Status: Open.

Date: 2026-05-31

## Status

Open.

## Context

Phase 2 of the 2D rendering optimization plan added hosted C runtime entrypoints
for native CPU SIMD span operations:

- `rt_engine2d_simd_fill_u32`
- `rt_engine2d_simd_copy_u32`

These mutate `[u32]`-style runtime arrays in native execution. The current
interpreter extern bridge receives `Value` arguments by value and cannot safely
mutate the caller's `Value::Array(Arc<Vec<Value>>)` in place.

## Impact

`simd_kernels.spl` must keep using the pure Simple scalar/SIMD-compatible
implementation in interpreter mode. Wiring the new C entrypoints directly into
the public Simple `fill_span`/`copy_span` functions would either fail in the
interpreter with unknown externs or risk a native/interpreter behavior split.

## Required fix

Add a proven mutable typed-array extern bridge for interpreter mode, or add a
native-only dispatch mechanism that semantic analysis accepts without requiring
the interpreter to resolve and execute the native C symbol.

After that exists, route `fill_span` and `copy_span` through the native
entrypoints when the host reports a matching SIMD tier, and keep the existing
Simple loops as fallback/reference paths.
