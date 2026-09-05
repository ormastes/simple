# Engine2D x86 span refresh — 2026-08-12

Status: PASS for operation correctness; FAIL for full-frame 8K/80 admission.

This receipt measures the production `runtime_simd_dispatch.c` ABI on the
current x86-64 host with `cc -O3 -march=native`. The authoritative row below
was compiled from a detached clean `HEAD`; it uses 500 samples of one
7,680-pixel row. It is operation evidence, not presentation or full-frame
evidence.

| Operation | Native p50 | Native p95 | Scalar p50 | Native/scalar |
|---|---:|---:|---:|---:|
| Opaque image blend | 11,993 ns | 12,705 ns | 14,588 ns | 1.216x |
| Opaque constant blend | 1,282 ns | 1,873 ns | 10,430 ns | 8.135x |
| Fill | 1,413 ns | 2,164 ns | 1,232 ns | 0.871x |
| Copy | 1,563 ns | 2,605 ns | 1,613 ns | 1.031x |
| Mixed-alpha image blend | 107,265 ns | 123,566 ns | 107,095 ns | 0.998x |

Receipts: `width=7680`, `frames=500`, `simd_hits=961000`, `mismatches=0`,
`checksum=263195865354240`, `scalar_checksum=263366992267264`,
`max_rss_kb=2048`, `elapsed_s=0.13`.

Multiplying the mixed-alpha p95 by 4,320 rows gives about 534 ms and is
only a projection. It excludes command generation, clipping, scheduling,
presentation, and readback. Mixed-alpha full repaint therefore cannot satisfy
the 12.5 ms 8K/80 frame budget. Retained frame switching/damage and genuine
mixed-alpha vectorization remain required.

An initial run against the shared dirty worktree measured mixed-alpha at
193,310/240,701 ns p50/p95 (0.699x scalar). Inspection showed that the dirty
runtime had reintroduced a four-pixel stack scratch bridge which clean `HEAD`
explicitly excludes because it is slower than the exact scalar body. That row
is diagnostic evidence for rejecting the experiment, not production evidence.

Reproduction:

```sh
mkdir -p /dev/shm/engine2d-span-refresh
cc -O3 -march=native -ffunction-sections -fdata-sections -Isrc/runtime -c \
  /path/to/clean-head/src/runtime/runtime_simd_dispatch.c \
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
