# Shared Multilingual GPU Font Performance Evidence

**Status:** release-blocking and currently unavailable
**Traceability:** NFR-002, NFR-004, NFR-005, NFR-006, NFR-007, NFR-008
**Executable:** `test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl`

The sole visible scenario shapes the ten selected language witnesses through
three pinned faces, warms one shared `FontRenderer`, then records eleven
samples for 1,024-glyph 1080p/4K routes and equal-semantics 4,096-glyph
CPU/Vulkan routes.

## Operator flow

1. Validate all three font hashes and construct exact-face shaping runs.
2. Discard one warm frame, reset counters, and collect eleven samples.
3. Require at least 95% warm hits, p95 ≤4 ms at 1080p and ≤8 ms at 4K, and
   Vulkan p95 at least 1.25× faster than CPU.
4. Require unchanged warm atlas upload, paired isolated 2D/3D RSS growth ≤10%,
   and GPU high-water in `(0, 128 MiB]`.
5. Overwrite `build/shared_multilingual_gpu_fonts_perf/evidence.env` using
   strict schema v5. The record pins viewports, byte-domain packed-ARGB,
   straight-alpha/rounding semantics, one warmup frame per route, the exact
   percentile formula, exact packed-ARGB CPU-oracle comparator, same-host
   OS/architecture, fonts/source hashes, device/driver, raw
   samples, RSS, upload stability, and GPU resource high-water.
6. Retain one emission/compile-install scalar and seven 11-sample stage arrays
   for shaping, material, unchanged dirty upload, fused queue/device completion,
   later fence observation, offscreen device readback, and CPU oracle. Require
   stable artifact/batch/payload identity, nonzero observed handles, completed
   fence, changed device pixels, and exact parity. The fused queue/device and
   fence-observation intervals overlap and are not summed; present is
   `not-applicable-offscreen`, while readback remains mandatory.

Missing hardware, malformed records, stale hashes, or failed thresholds remain
`unavailable`/failed and cannot promote a backend.
The same-host check intentionally rejects records replayed on another OS or
architecture. FNV64 checksums remain runtime diagnostics rather than acceptance.
It also retains controlled Vulkan-poison CPU fallback, equal prepared-batch
identity before/after poison, and eleven post-loss CPU samples whose recomputed
p95 must not exceed the baseline CPU fixture.
