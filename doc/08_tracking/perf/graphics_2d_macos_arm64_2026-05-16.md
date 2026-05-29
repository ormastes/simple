# 2D Graphics Benchmark — macOS ARM64 — 2026-05-16

## System

- **Platform:** Darwin 25.3.0 (macOS Sequoia) ARM64
- **CPU:** Apple M4
- **GPU:** Apple Silicon integrated GPU (Metal available in hardware)
- **CUDA:** Not present
- **Simple version:** v0.9.8

---

## 1. C Reference Benchmark

The pre-built binary at `test/perf/graphics_2d/c_reference/bench_2d` is an
**x86-64 Linux ELF** (built on a Linux CI host). It is not executable on ARM64
macOS (exit 126, "cannot execute binary file").

Recompiled from source on the host:
```
clang -O2 -o /tmp/bench_2d_arm64 test/perf/graphics_2d/c_reference/bench_2d.c
```

### Raw output (ARM64 native, `-O2`)

```
SCENE_RESULT scene=fill_1080p backend=c_cpu_scalar frame_count=100 p50_ms=1 p95_ms=1 pixels_per_sec=1954382657 draws_per_sec=95193 rss_kb=0 pixel_hash=4834704270759959608 p50_ns=1061000 mode=full
SCENE_RESULT scene=blit_tiles backend=c_cpu_scalar frame_count=100 p50_ms=1 p95_ms=2 pixels_per_sec=1041486690 draws_per_sec=256654 rss_kb=0 pixel_hash=-1036025823807617243 p50_ns=1991000 mode=full
SCENE_RESULT scene=clipped_scroll backend=c_cpu_scalar frame_count=100 p50_ms=0 p95_ms=0 pixels_per_sec=11715254237 draws_per_sec=62146 rss_kb=0 pixel_hash=1541462802529360585 p50_ns=177000 mode=full
```

### Per-scene summary (p50)

| Scene           | p50_ns  | p50_ms | pixels/sec      | draws/sec |
|-----------------|---------|--------|-----------------|-----------|
| fill_1080p      | 1061000 | 1 ms   | 1,954,382,657   | 95,193    |
| blit_tiles      | 1991000 | 2 ms   | 1,041,486,690   | 256,654   |
| clipped_scroll  |  177000 | <1 ms  | 11,715,254,237  | 62,146    |

Notes:
- `rss_kb=0` on all three — macOS does not expose `/proc/self/status`, so the
  RSS read function returns 0. This is expected; the C source uses Linux procfs.
- Framebuffer is 1920×1080 RGBA8888 (full mode).
- 10 warmup + 100 timed frames per scene.

---

## 2. Simple Benchmarks

### 2a. `bench_2d_gpu.spl` (SFFI dlopen path)

Command: `bin/simple run test/perf/graphics_2d/bench_2d_gpu.spl`

**Result: runtime failure — libcuda.so not found**

```
========================================
2D GPU Benchmark — Simple + CUDA (SFFI)
========================================

FAIL: Cannot load libcuda.so
```

Stderr (interpreter wffi warning):
```
spl_dlopen failed for 'libcuda.so.1': dlopen(libcuda.so.1, 0x0005): tried:
  'libcuda.so.1' (no such file),
  '/System/Volumes/Preboot/Cryptexes/OSlibcuda.so.1' (no such file),
  '/usr/lib/libcuda.so.1' (no such file, not in dyld cache),
  'libcuda.so.1' (no such file)
spl_dlopen failed for 'libcuda.so': (same pattern)
```

Exit code: 0 (benchmark handled the failure gracefully, printed FAIL message).

**Root cause:** The benchmark calls `spl_dlopen("libcuda.so.1")` / `spl_dlopen("libcuda.so")` at runtime. CUDA is not present on Apple Silicon; dlopen fails. There is no Metal code path in this file.

### 2b. `bench_2d_gpu_batch.spl` (batched extern path)

Command: `bin/simple run test/perf/graphics_2d/bench_2d_gpu_batch.spl`

**Result: parse error before execution**

```
error: parse error: Unexpected token: expected expression, found Parallel
```

Exit code: 8.

**Root cause:** The file uses C-style brace syntax (`fn main() { ... }`, `while x { }`, `if x { }`) rather than Simple's indentation-based syntax. The Simple parser rejects `{` as an unexpected token. This file cannot be run by the Simple interpreter as-is; it appears to have been authored with the wrong syntax.

Additionally, even if syntax were fixed, all extern calls (`rt_cuda_available`, `rt_cuda_memset`, `rt_cuda_rect_fill`, etc.) target CUDA, which is unavailable on this machine.

---

## 3. Metal-targeting Benchmark Files in `test/perf/`

Three files reference Metal:

| File | Role |
|------|------|
| `test/perf/graphics_2d/metal_smoke_spec.spl` | Spec (Phase 5 pending) — correctness via sync_readback pixel hash |
| `test/perf/graphics_2d/backend_probe_spec.spl` | Probe result spec — includes Metal probe expectations |
| `test/perf/graphics_2d/no_duplication_spec.spl` | Structural test — checks backend name constant uniqueness |

None of these are standalone performance benchmarks. `metal_smoke_spec.spl` is
annotated "Pending implementation (Phase 5)".

---

## 4. Metal Backend Probe

Test file written to `/tmp/metal_probe_test.spl`. Calls `rt_metal_is_available()`
directly via `extern fn`.

Command: `bin/simple run /tmp/metal_probe_test.spl`

**Output:**
```
=== Metal Backend Probe ===
rt_metal_is_available: false
probe_result: status=Failed reason=Metal not available on this platform
=== End Metal Probe ===
```

Exit code: 0.

**Conclusion:** `rt_metal_is_available()` returns `false` on this Apple M4 machine.
The runtime function is compiled in (the call returns gracefully), but it reports
Metal as unavailable. This is a runtime stub or the native runtime linked into
the interpreter does not include a working Metal implementation (even though the
hardware supports Metal). `rt_metal_init()` was not reached.

---

## 5. Gaps Before Perf Parity is Measurable

- **The pre-built C reference binary must be rebuilt for ARM64 macOS.** The
  committed ELF is x86-64 Linux-only; a macOS `Makefile` target or CI job is
  needed to produce a comparable native artifact.

- **The Metal runtime stubs are not implemented.** `rt_metal_is_available()`
  returns `false` on Apple M4 hardware that physically supports Metal. The
  `backend_metal.spl` layer and MSL shader code exist in source, but the
  underlying `rt_metal_*` C runtime functions are either unimplemented or not
  compiled into the interpreter binary. Until `rt_metal_is_available()` returns
  `true` and `rt_metal_init()` succeeds, no GPU-accelerated path can execute
  and no Metal vs C comparison is possible.

- **`bench_2d_gpu_batch.spl` uses invalid Simple syntax (C braces).** It must
  be rewritten in proper Simple indentation syntax before it can be parsed, and
  its CUDA `extern fn` calls replaced with Metal equivalents before it is useful
  on macOS.

---

## 6. Remaining Plan — 2026-05-29

Current state:

- The current working line is based on the remote refactor around
  `docs(editor): feature request for TUI render completion + ctrl *2 module
  consolidation`.
- `simd_kernels_spec.spl` passes again after keeping the existing
  `simd_kernels.spl` row/span API stable.
- `backend_software_primitives_spec.spl` passes with the current software
  backend changes.
- `backend_software_simd_spec.spl` still times out. A direct probe confirmed
  `SoftwareBackend.clear()` completes quickly and increments `fill_hits`; a
  combined probe timed out, so the next pass should isolate blit, alpha blend,
  and tile/present cases separately before changing more code.
- A stale backend SIMD test process was observed and killed during this stop
  point. Check for stale `backend_software_simd_spec` or `bin/simple test`
  processes before restarting verification.

Remaining work:

- Keep the first implementation pass in pure Simple. Do not move the remaining
  2D engine work into Rust until the Simple engine paths are complete enough to
  verify correctness and renderer parity.
- Finish CPU software backend acceleration accounting on the current refactored
  line: direct buffer mutation remains inside `SoftwareBackend` methods, while
  SIMD provider hit counters record fill, copy, and alpha hot-path usage.
- Keep the existing `simd_kernels.spl` row/span API stable for current tests and
  consumers. Use it as the scalar/SIMD parity surface, not as the mutation path
  for `SoftwareBackend` fields when that causes interpreter fallback or stalls.
- Continue the Metal path after the pure Simple CPU path is verified: ensure
  Metal availability, init, readback, and browser bridge routing all remain
  consistent with current remote refactors.
- Re-run focused verification before each push: SIMD kernels, software SIMD
  integration, software primitives, Metal sync where present, browser bridge,
  and the GUI parity smoke.
