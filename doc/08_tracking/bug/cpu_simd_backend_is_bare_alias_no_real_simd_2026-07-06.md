# Honesty/Perf: "cpu_simd" backend is a bare alias to plain CPU, no real SIMD in hot path

- **Date:** 2026-07-06
- **Severity:** MEDIUM (false capability claim + missed perf opportunity)
- **Area:** src/lib/gc_async_mut/gpu/engine2d/engine.spl, backend_cpu.spl, backend_software.spl; src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl

## Summary

Selecting the `"cpu_simd"` backend instantiates the **identical `CpuBackend.create()` class** as plain `"cpu"`, differing only in the `selected_backend_name` string. No distinct SIMD code path executes. Genuine NEON/SSE/AVX kernels do exist (simd_kernels.spl) but are never called from the software rasterization hot path. The only SIMD signal in the live code is a telemetry counter. Capability name is dishonest and performance is identical to plain CPU.

## Evidence

- **Identical instantiation:** `engine.spl:271-279` constructor for `"cpu_simd"` calls `CpuBackend.create()` verbatim identical to the `"cpu"` path (lines 264-270), differing only in the `selected_backend_name` string literal
- **CpuBackend forwards to SoftwareBackend:** `backend_cpu.spl:9-87` is pure composition over `SoftwareBackend` (`sw:` field); every method is a one-line forward (confirmed zero independent rasterization)
- **SoftwareBackend scalar loops:** `backend_software.spl:135-183+` implements all rasterization as plain scalar `while` loops; no vectorization anywhere
- **Telemetry only, no dispatch:** `simd_provider.spl` contains `record_simd_fill_hit()` counter increments, but no actual vector kernel launch; confirmed zero matches grepping `backend_software.spl`/`backend_cpu.spl` for `simd_fill_row`/`fill_span`/any NEON function name
- **Real NEON kernels exist but orphaned:** `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:333-378` defines genuine `extern`-backed C NEON intrinsics per file comment "Genuine NEON (C kernel)"; their only confirmed consumer is an unrelated `cpu_simd_session.spl` API not called from `RenderBackend` hot path
- **Probe detects SIMD capability but never used:** `backend_probe.spl` has real per-arch NEON/SSE/AVX detection (`cpu_simd_arm`/`cpu_simd_x86` branches lines 119-145, calls `detect_simd_level()`) but this detection feeds `compute_dispatch.spl` path (§c-9 in audit), not `Engine2D.create_requested_backend()`'s render path

## Failure scenario

1. Application developer calls `Engine2D.create_with_backend(w, h, "cpu_simd")` expecting SIMD acceleration
2. Backend instantiation succeeds with `selected_backend_name="cpu_simd"`
3. All rasterization runs through scalar `SoftwareBackend` loops, identical to `"cpu"` selection
4. Performance identical or unmeasurably different from plain CPU; NEON kernels never invoked
5. Developer cannot distinguish capability claim from delivery; migration from `"cpu"` to `"cpu_simd"` shows no improvement

## Fix direction

**Option A (wire real SIMD):** integrate the existing NEON/SSE/AVX span kernels (simd_kernels.spl) into `backend_software.spl`'s fill/blend hot path, gated by architecture and a `cpu_simd_session.spl`-style capability query; add proof measurement (kernel executed counter, timing delta) that vector path is actually running.

**Option B (honest rename):** eliminate `"cpu_simd"` as a distinct backend name; either merge it as a config flag on `CpuBackend`, or delete it entirely and leave SIMD as an internal optimization inside `SoftwareBackend` that users cannot directly select.

## Verification targets

- Selecting `"cpu_simd"` and measuring a large fill operation (e.g. 1024x1024 rect) shows measurable speedup vs. `"cpu"` on ARM64 and x86_64 hosts
- A test or perf counter confirms NEON/AVX span kernels are invoked during `draw_rect_filled` on cpu_simd backend
- If `"cpu_simd"` is removed: Engine2D backend list does not include it; no stale references remain
- If SIMD is wired: proof includes before/after timing and vector-instruction profiling (e.g. neon-cycles or perf-events)
