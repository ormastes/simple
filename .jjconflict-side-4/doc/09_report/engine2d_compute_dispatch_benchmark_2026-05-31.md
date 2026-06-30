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
- Smoke command: `SIMPLE_NO_STUB_FALLBACK=1 bin/simple test/05_perf/graphics_2d/simple_runner.spl`
- Full Simple command: `SIMPLE_ENGINE2D_RUNNER_MODE=full bin/simple test/05_perf/graphics_2d/simple_runner.spl`
- Full C command: `./test/05_perf/graphics_2d/c_reference/bench_2d`
- Structural command: `bin/simple test test/05_perf/graphics_2d/report_spec.spl --mode=interpreter`

## Current Full-Mode Results

`simple_runner.spl` now keeps interpreter-safe smoke mode as the default and
enables the 1920x1080 full gate with `SIMPLE_ENGINE2D_RUNNER_MODE=full`.
The full runner uses 10 warmup frames and 100 timed frames.

| Scene | Backend | Mode | p50 ns | p50 ms | p95 ms | Pixels/sec | Draws/sec | Pixel hash |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| fill_1080p | c_cpu_scalar | full | 4524903 | 4 | 5 | 458263967 | 22320 | 3453644792 |
| fill_1080p | simple_cpu_scalar | full | 140777664 | 140 | 144 | 14729609 | 717 | 3453644792 |
| blit_tiles | c_cpu_scalar | full | 4781594 | 4 | 5 | 433662916 | 106868 | 1245774277 |
| blit_tiles | simple_cpu_scalar | full | 43310089 | 43 | 47 | 47877989 | 11798 | 1245774277 |
| clipped_scroll | c_cpu_scalar | full | 2308940 | 2 | 3 | 898074441 | 4764 | 35205929 |
| clipped_scroll | simple_cpu_scalar | full | 23273378 | 23 | 25 | 89097508 | 472 | 35205929 |

## Hash Gate Status

| Scene | C hash | Simple hash | Status |
|---|---:|---:|---|
| fill_1080p | 3453644792 | 3453644792 | pass |
| blit_tiles | 1245774277 | 1245774277 | pass |
| clipped_scroll | 35205929 | 35205929 | pass |

Full throughput now runs locally and the per-scene byte hashes match exactly.
The benchmark uses FNV-1a 32-bit for the cross-runtime pixel hash because the
current direct Simple runner does not produce C-compatible FNV-1a 64-bit values
for signed 64-bit hash state.

## Backend Matrix Status

| Backend | Phase 6 target | Current evidence path | Current status |
|---|---|---|---|
| CUDA | 1920x1080 fill/blit/scroll throughput | `ComputeDispatch`, `CudaSession`, generated 2D launch plans | Probe-backed dispatch exists; full hardware throughput not measured on this host |
| HIP/ROCm | 1920x1080 fill/blit/scroll throughput | `RocmSession`, fail-closed `RocmFfi`, generated HIP launch plans | Session contract exists; no HIP runtime measurement on this host |
| OpenCL | 1920x1080 fill/blit/scroll throughput | `OpenClSession`, ICD probe, generated OpenCL launch plans | ICD probe/session contract exist; full device throughput not measured here |
| CPU-SIMD AVX2 | 1920x1080 fill/blit/scroll throughput | CPU SIMD kernels and hit counters | Runtime evidence exists; full 1920x1080 runner still pending |
| CPU-SIMD NEON | 1920x1080 fill/blit/scroll throughput | CPU SIMD architecture probe | Not available on this x86_64 host |
| Scalar CPU | 1920x1080 fill/blit/scroll throughput | `simple_runner.spl`, C reference harness | Full 1920x1080 mode runs; hash gate passes for fill, blit, and scroll |

## Full-Mode Gate

Full accepted throughput evidence still requires:

1. Keep running `test/05_perf/graphics_2d/c_reference/bench_2d` for C scalar reference.
2. Keep running `simple_runner.spl` in full mode: 1920x1080, 10 warmup frames,
   100 timed frames.
3. For GPU rows, run equivalent generated-kernel dispatch paths only when the
   corresponding runtime probe initializes a real backend.
4. Compare per-scene pixel hashes before accepting throughput numbers.

## Verification

- `SIMPLE_NO_STUB_FALLBACK=1 bin/simple test/05_perf/graphics_2d/simple_runner.spl`:
  smoke data produced.
- `SIMPLE_ENGINE2D_RUNNER_MODE=full bin/simple test/05_perf/graphics_2d/simple_runner.spl`:
  full 1920x1080 data produced.
- `./test/05_perf/graphics_2d/c_reference/bench_2d`: full 1920x1080 C scalar data
  produced.
- `bin/simple test test/05_perf/graphics_2d/report_spec.spl --mode=interpreter`:
  PASS, 18/18.
