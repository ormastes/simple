# Bug: compress_facade_harness_spec times out (>120s)

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
