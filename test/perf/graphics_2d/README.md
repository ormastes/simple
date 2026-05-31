# Graphics 2D CPU Benchmark — C vs Simple Scalar

Direct CPU scalar performance comparison for NFR-GRAPHICS-2B.

## Files

| File | Description |
|---|---|
| `scene_format.spl` | Canonical scene names and NFR threshold constants |
| `simple_runner.spl` | Pure-Simple CPU framebuffer runner (no Engine2D) |
| `report_spec.spl` | spipe spec: field validation, hash stability, ratio structure |
| `c_reference/bench_2d.c` | C scalar reference — raw memset/memcpy paths |
| `c_reference/Makefile` | Build C reference with `-O2` |

## Scenes

| Scene | Description |
|---|---|
| `fill_1080p` | Clear 1920x1080 + 100 filled rects |
| `blit_tiles` | 1920x1080 tiled 64x64 sprite blits |
| `clipped_scroll` | Clipped viewport with scrolling rows |

## Report Fields

Every `SCENE_RESULT` line contains:
`scene_name backend frame_count p50_ms p95_ms pixels_per_sec draws_per_sec rss_kb pixel_hash p50_ns mode`

`simple_vs_c_ratio` (ratio x1000) is computed post-hoc: `(simple_p50_ns * 1000) / c_p50_ns`.

## Running

```sh
# Spec (interpreter-mode, structural validation only)
bin/simple test test/perf/graphics_2d/report_spec.spl

# C reference (full 1920x1080)
cd test/perf/graphics_2d/c_reference && make && ./bench_2d

# Simple runner (smoke mode by default — interpreter-safe 16x16)
bin/simple test/perf/graphics_2d/simple_runner.spl

# Simple runner full mode (1920x1080, 10 warmup, 100 timed frames)
SIMPLE_ENGINE2D_RUNNER_MODE=full bin/simple test/perf/graphics_2d/simple_runner.spl
```

## NFR-2B Requirements

- Simple CPU scalar: p50 frame time within **1.25x** of C reference
- Simple CPU SIMD: equal-or-better for fill, blit, clipped-scroll
- Pixel hash must match between C and Simple per scene (correctness gate)
- All claims must record: hardware, OS, backend, compiler mode, feature flags, sample count

## Pixel Format

RGBA8888, byte order R,G,B,A per pixel, row-major. FNV-1a 64-bit hash over full framebuffer.

## Warmup / Timing

Full mode: 10 warmup frames (allocation outside timed window), 100 timed frames.
Percentiles from per-frame nanosecond timestamps (`clock_gettime(CLOCK_MONOTONIC)` / `rt_time_now_nanos()`).

## Hardware Metadata Template

```
BENCH_META date=YYYY-MM-DD host=$(uname -srm) compiler=<version> mode=<native|smf> features=<none|sse2|avx2> warmup=10 samples=100
```
