# Engine2D x86 span refresh — 2026-08-12

Status: PASS for operation correctness; FAIL for full-frame 8K/80 admission.

This receipt measures the production `runtime_simd_dispatch.c` ABI on the
current x86-64 host with `cc -O3 -march=native`. It uses 500 samples of one
7,680-pixel row. It is operation evidence, not presentation or full-frame
evidence.

| Operation | Native p50 | Native p95 | Scalar p50 | Native/scalar |
|---|---:|---:|---:|---:|
| Opaque image blend | 14,237 ns | 20,960 ns | 22,524 ns | 1.582x |
| Opaque constant blend | 2,635 ns | 3,747 ns | 14,077 ns | 5.342x |
| Fill | 4,478 ns | 8,236 ns | 4,128 ns | 0.921x |
| Copy | 4,518 ns | 8,035 ns | 4,609 ns | 1.020x |
| Mixed-alpha image blend | 193,310 ns | 240,701 ns | 135,229 ns | 0.699x |

Receipts: `width=7680`, `frames=500`, `simd_hits=961500`, `mismatches=0`,
`checksum=263195865354240`, `scalar_checksum=263366992267264`,
`max_rss_kb=2048`, `elapsed_s=0.22`.

Multiplying the mixed-alpha p95 by 4,320 rows gives about 1.040 seconds and is
only a projection. It excludes command generation, clipping, scheduling,
presentation, and readback. Mixed-alpha full repaint therefore cannot satisfy
the 12.5 ms 8K/80 frame budget. Retained frame switching/damage and genuine
mixed-alpha vectorization remain required.

Reproduction:

```sh
mkdir -p /dev/shm/engine2d-span-refresh
cc -O3 -march=native -ffunction-sections -fdata-sections -Isrc/runtime -c \
  src/runtime/runtime_simd_dispatch.c \
  -o /dev/shm/engine2d-span-refresh/runtime_simd_dispatch.o
cc -O3 -march=native -ffunction-sections -fdata-sections -Isrc/runtime -c \
  test/09_baselines/engine2d_simd/engine2d_simd_opaque_span_bench.c \
  -o /dev/shm/engine2d-span-refresh/bench.o
cc -O3 -march=native -Wl,--gc-sections \
  /dev/shm/engine2d-span-refresh/runtime_simd_dispatch.o \
  /dev/shm/engine2d-span-refresh/bench.o \
  -o /dev/shm/engine2d-span-refresh/bench
/usr/bin/time -f 'max_rss_kb=%M elapsed_s=%e' \
  timeout 60s /dev/shm/engine2d-span-refresh/bench
```
