# Architecture — `common_compression_framework`

## Public structure

- `src/lib/common/compress/mod.spl`
  - shared façade
  - codec dispatch
  - streaming finish operations
- `src/lib/common/compress/types.spl`
  - shared enums, wrappers, state
- `src/lib/common/compress/utilities.spl`
  - framing/checksum helpers
- `src/lib/common/compress/lz4.spl`
  - LZ4 block/frame logic
- `src/lib/common/compress/zstd.spl`
  - Zstd frame subset
- `src/lib/common/compress/lzma2.spl`
  - XZ/LZMA2 subset

## Startup path

- Importing `std.common.compress` loads only pure helper code and codec modules.
- No runtime index build or background initialization is required.
- There is no new global cache or detector stack.

## Dispatch path

- Caller provides `CompressionOptions` to `compress_bytes`, which dispatches on `CompressionCodec`.
- `decompress_bytes` first auto-detects from frame magic when no hint is supplied.
- Raw LZ4 blocks still require an explicit hint because raw blocks have no magic.

## State and invalidation

- `CompressionEncoderState` and `CompressionDecoderState` are append-and-finish state objects.
- Reset is structural: callers create a fresh state for each stream; no hidden global cache is retained.
- This first delivery favors correctness and standard framing over incremental output buffering sophistication.

## Cache / table strategy

- No persistent codec tables are cached globally in this first phase.
- LZ4 uses direct greedy search.
- Zstd subset avoids entropy tables by supporting raw and RLE blocks only.
- XZ/LZMA2 subset avoids range-coder tables by using uncompressed LZMA2 chunks.

## SIMD strategy

- The existing runtime SIMD tier API remains the only detector path.
- This landing does not add fast-path kernels yet; later phases can hang optimized helpers off the existing tiers without changing the public API.

## Latency / RSS targets

- Unit-test sized payloads should stay within normal interpreter budgets.
- No per-request full-tree scans, subprocess launch in hot paths, or persistent large tables are introduced by the library itself.
