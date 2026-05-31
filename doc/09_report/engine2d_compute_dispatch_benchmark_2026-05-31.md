# Engine2D Compute Dispatch Benchmark Evidence - 2026-05-31

## Scope

Phase 6 target from `doc/03_plan/render_2d_optimization_plan_2026-05-30.md`:
1920x1080 fill + blit + scroll throughput for CUDA, HIP/ROCm, OpenCL,
CPU-SIMD AVX2, CPU-SIMD NEON, and scalar CPU.

This report records the current runnable evidence and the remaining full-mode
measurement gate. It does not claim GPU throughput where the local host cannot
initialize that backend.

## Host

- Host: Linux 6.8.0-117-generic x86_64
- Date: 2026-05-31
- Smoke command: `bin/simple test/perf/graphics_2d/simple_runner.spl`
- Structural command: `bin/simple test test/perf/graphics_2d/report_spec.spl --mode=interpreter`

## Current Smoke Results

`simple_runner.spl` is currently in smoke mode: 16x16 framebuffer, 1 warmup
frame, 3 timed frames. The run fell back from JIT to interpreter because HIR
lowering rejected mutation through the framebuffer object:

`Memory safety error [W1006]: mutation without mut capability`

| Scene | Backend | Mode | p50 ns | p50 ms | p95 ms | Pixels/sec | Draws/sec | Pixel hash |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| fill_1080p | simple_cpu_scalar | smoke | 156250615 | 156 | 166 | 1638 | 646 | 5652535538643359510 |
| blit_tiles | simple_cpu_scalar | smoke | 35720477 | 35 | 37 | 7166 | 55 | 3806217878923355429 |
| clipped_scroll | simple_cpu_scalar | smoke | 13477267 | 13 | 13 | 18994 | 816 | -1273962105834214439 |

`report_spec.spl` passed 18/18 structural checks. It emitted a non-fatal
artifact-manifest warning because one generated scenario artifact directory name
exceeded the filesystem filename limit.

## Backend Matrix Status

| Backend | Phase 6 target | Current evidence path | Current status |
|---|---|---|---|
| CUDA | 1920x1080 fill/blit/scroll throughput | `ComputeDispatch`, `CudaSession`, generated 2D launch plans | Probe-backed dispatch exists; full hardware throughput not measured on this host |
| HIP/ROCm | 1920x1080 fill/blit/scroll throughput | `RocmSession`, fail-closed `RocmFfi`, generated HIP launch plans | Session contract exists; no HIP runtime measurement on this host |
| OpenCL | 1920x1080 fill/blit/scroll throughput | `OpenClSession`, ICD probe, generated OpenCL launch plans | ICD probe/session contract exist; full device throughput not measured here |
| CPU-SIMD AVX2 | 1920x1080 fill/blit/scroll throughput | CPU SIMD kernels and hit counters | Runtime evidence exists; full native runner blocked by mutable framebuffer lowering |
| CPU-SIMD NEON | 1920x1080 fill/blit/scroll throughput | CPU SIMD architecture probe | Not available on this x86_64 host |
| Scalar CPU | 1920x1080 fill/blit/scroll throughput | `simple_runner.spl`, C reference harness | Smoke measured; full native mode blocked by mutable framebuffer lowering |

## Full-Mode Gate

Full throughput evidence requires:

1. Fix or route around the native/JIT mutable framebuffer lowering failure in
   `test/perf/graphics_2d/simple_runner.spl`.
2. Run `test/perf/graphics_2d/c_reference/bench_2d` for C scalar reference.
3. Run `simple_runner.spl` in full mode: 1920x1080, 10 warmup frames, 100 timed
   frames, native/SMF execution.
4. For GPU rows, run equivalent generated-kernel dispatch paths only when the
   corresponding runtime probe initializes a real backend.
5. Compare per-scene pixel hashes before accepting throughput numbers.

## Verification

- `bin/simple test/perf/graphics_2d/simple_runner.spl`: smoke data produced.
- `bin/simple test test/perf/graphics_2d/report_spec.spl --mode=interpreter`:
  PASS, 18/18.
