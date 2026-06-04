# CPU SIMD mutable array extern wiring

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
