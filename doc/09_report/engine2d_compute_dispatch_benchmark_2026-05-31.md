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
- Smoke command: `SIMPLE_NO_STUB_FALLBACK=1 bin/simple test/perf/graphics_2d/simple_runner.spl`
- Structural command: `bin/simple test test/perf/graphics_2d/report_spec.spl --mode=interpreter`

## Current Smoke Results

`simple_runner.spl` is currently in smoke mode: 16x16 framebuffer, 1 warmup
frame, 3 timed frames. The runner now executes through the native/JIT path
without the prior mutable-framebuffer fallback.

| Scene | Backend | Mode | p50 ns | p50 ms | p95 ms | Pixels/sec | Draws/sec | Pixel hash |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| fill_1080p | simple_cpu_scalar | smoke | 47621 | 0 | 0 | 5375779 | 2120913 | 1040849520215971606 |
| blit_tiles | simple_cpu_scalar | smoke | 14899 | 0 | 0 | 17182361 | 134237 | -805468139504032475 |
| clipped_scroll | simple_cpu_scalar | smoke | 3888 | 0 | 0 | 65843621 | 2829218 | 1031880903379479513 |

`report_spec.spl` passed 18/18 structural checks. It emitted a non-fatal
artifact-manifest warning because one generated scenario artifact directory name
exceeded the filesystem filename limit.

## Backend Matrix Status

| Backend | Phase 6 target | Current evidence path | Current status |
|---|---|---|---|
| CUDA | 1920x1080 fill/blit/scroll throughput | `ComputeDispatch`, `CudaSession`, generated 2D launch plans | Probe-backed dispatch exists; full hardware throughput not measured on this host |
| HIP/ROCm | 1920x1080 fill/blit/scroll throughput | `RocmSession`, fail-closed `RocmFfi`, generated HIP launch plans | Session contract exists; no HIP runtime measurement on this host |
| OpenCL | 1920x1080 fill/blit/scroll throughput | `OpenClSession`, ICD probe, generated OpenCL launch plans | ICD probe/session contract exist; full device throughput not measured here |
| CPU-SIMD AVX2 | 1920x1080 fill/blit/scroll throughput | CPU SIMD kernels and hit counters | Runtime evidence exists; full 1920x1080 runner still pending |
| CPU-SIMD NEON | 1920x1080 fill/blit/scroll throughput | CPU SIMD architecture probe | Not available on this x86_64 host |
| Scalar CPU | 1920x1080 fill/blit/scroll throughput | `simple_runner.spl`, C reference harness | Native/JIT smoke measured; full 1920x1080 mode still pending |

## Full-Mode Gate

Full throughput evidence requires:

1. Run `test/perf/graphics_2d/c_reference/bench_2d` for C scalar reference.
2. Run `simple_runner.spl` in full mode: 1920x1080, 10 warmup frames, 100 timed
   frames, native/SMF execution.
3. For GPU rows, run equivalent generated-kernel dispatch paths only when the
   corresponding runtime probe initializes a real backend.
4. Compare per-scene pixel hashes before accepting throughput numbers.

## Verification

- `SIMPLE_NO_STUB_FALLBACK=1 bin/simple test/perf/graphics_2d/simple_runner.spl`:
  native/JIT smoke data produced.
- `bin/simple test test/perf/graphics_2d/report_spec.spl --mode=interpreter`:
  PASS, 18/18.
