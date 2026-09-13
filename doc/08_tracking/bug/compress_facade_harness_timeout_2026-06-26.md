# Bug: compress_facade_harness_spec times out (>120s)

## Closed 2026-09-13 — stated root cause gone: compress modules are real .spl, no hang
- **measured** (Windows Rust seed v1.0.0-rc.1, `bin/simple run`): a probe importing `std.common.compress.{lz4,zstd,lzma2,utilities}` loads and returns in `real 0m3.7s` — no hang, no 120s timeout.
- **measured**: `find src/lib -name '*.smf'` returns nothing; `ls src/lib/common/compress/` shows 23 real `.spl` sources (lz4, zstd*, lzma2*, brotli, deflate, gzip, snappy...).
- **measured** (added after review): a real lz4 round trip completes — `lz4_compress_frame_for_tier(10 bytes, opts, CompressionSimdTier.scalar)` -> 33 bytes, `lz4_decompress_frame_for_tier(...).unwrap().len()` -> 10, in `real 0m0.34s`. So the round-trip path itself does not hang, not merely module load.
- **inferred**: the spec itself could not be re-run — `bin/simple test` is broken on this Windows host (a 1-assertion trivial spec also reports `reason=outer-bound-timeout budget_ms=930000` in under a second).

**Date:** 2026-06-26
**Spec:** `test/01_unit/lib/common/compress_facade_harness_spec.spl`

## Symptoms

`bin/simple test test/01_unit/lib/common/compress_facade_harness_spec.spl` never
completes — hangs indefinitely (no output within 120s timeout).

## Likely cause

`std.common.compress.*` modules (lz4, zstd, lzma2) are compiled stubs (.smf files)
with no real implementation. The spec calls compression/decompression round-trip
functions that likely spin in an infinite loop or block waiting on unimplemented
native FFI in the stub layer.

## Fix needed

Either implement the compress modules (src/lib/common/compress/) or guard the spec
with a check that the compress backend is available before running round-trip tests.
