# Simple 2D Vector Fonts Performance — 2026-07-11

Status: **PENDING PURE-SIMPLE EVIDENCE**

The executable evidence is
`test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl`. It measures 31
paired public `Engine2D.load_font`/`draw_text` cold and warm CPU samples at
128x72, with load, clear, framebuffer readback, and reporting outside timing.
It requires real glyph-cache hits, zero warm misses/rasterizations, stable
framebuffer checksum, warm p50 at least 25% faster, and the 512-entry/32 MiB
bounds.

NFR-003 uses the unchanged bitmap-only probe at
`test/05_perf/graphics_2d/simple_2d_bitmap_text_baseline_probe.spl` in both a
detached pre-feature tree (`126bfa06081d`) and the current tree. The perf spec
requires retained `SIMPLE_2D_BITMAP_BASELINE_NS` and
`SIMPLE_2D_BITMAP_BASELINE_CHECKSUM`; missing values fail instead of skipping
the gate. Current p50 must be within 5% and checksums must match.

## Required retained run

```text
binary: pending restored pure-Simple self-hosted executable
source revision/dirty identity: 126bfa06081d + isolated vector-font lane
host/CPU: x86_64, AMD Ryzen Threadripper 1950X 16-Core Processor
fixture SHA-256: cb40a3b0aed56dbd2465355ff5ac53ea5e6b567877132844d8f780fd600bdade
raw public-facade pairs (31): pending
cold p50/p95: pending
warm p50/p95: pending
warm hit rate/misses/rasterizations: pending
bitmap baseline/current p50/p95/checksum: pending
cache entries/bytes/evictions: pending
framebuffer checksum: pending
max RSS from /usr/bin/time -v: pending
```

## Blocked attempts

- Canonical `bin/simple --version` identifies itself as the Rust bootstrap seed,
  so its earlier results are diagnostic only and were removed after they were
  found to measure a deleted whole-payload memo rather than glyph-cache reuse.
- `build/bootstrap/stage3/.../simple` is not usable evidence: docgen timed out,
  native-build segfaulted, and a direct run produced no output.
- `build/bootstrap/full/.../simple` passes a trivial `-c` smoke but exits by
  signal 11 in both vector-font docgen and the detached bitmap probe.
- The Rust seed could build the first detached-tree probe, but that binary
  omitted loop output/string interpolation; a corrected build then failed in
  LLVM with an undefined `%l10`. These are compiler diagnostics, not retained
  performance numbers.

The report remains pending until one restored pure-Simple binary runs both
detached-tree/current bitmap probes and the public-facade perf spec once.
The owner-path blocker is tracked at
`doc/08_tracking/bug/pure_simple_spipe_docgen_vector_font_spec_crash_2026-07-11.md`.
