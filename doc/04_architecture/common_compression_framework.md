# Architecture — `common_compression_framework`
<!-- codex-design -->

## Public structure

- `src/lib/common/compress/mod.spl`
  - shared public facade
  - codec dispatch
  - whole-buffer streaming finish path
- `src/lib/common/compress/types.spl`
  - `CompressionCodec`
  - `CompressionLevel`
  - `CompressionOptions`
  - `CompressionError`
  - `CompressionEncoderState` / `CompressionDecoderState`
- `src/lib/common/compress/utilities.spl`
  - level validation
  - byte-order helpers
  - CRC32 / XXH32 helpers
  - codec auto-detect
  - state append helpers
- `src/lib/common/compress/lz4.spl`
  - LZ4 raw block encode/decode
  - LZ4 frame encode/decode
- `src/lib/common/compress/zstd.spl`
  - phased Zstd frame subset
- `src/lib/common/compress/lzma2.spl`
  - phased XZ/LZMA2 subset

## Delivered scope versus umbrella scope

This umbrella feature is intentionally landing as a phased shared API, not as full entropy-coded coverage for all three ecosystems.

- LZ4 current scope:
  - standard raw block encode/decode
  - standard frame encode/decode
  - raw block decode requires an explicit codec hint because raw blocks have no magic
- Zstd current scope:
  - emits standard frames using raw or RLE blocks
  - decodes raw and RLE blocks
  - rejects window descriptors, dictionary ids, compressed blocks, and content checksum verification with `UnsupportedFeature`
- XZ/LZMA2 current scope:
  - emits a standard single-block XZ stream with one LZMA2 filter and uncompressed LZMA2 chunks
  - validates XZ structure and CRC32 checks
  - rejects compressed LZMA2 chunks, non-CRC32 check types, and multi-block XZ streams with `UnsupportedFeature`

The public API already matches the broader umbrella, but the implementation underneath it is still the bounded first slice above.

## Startup path

- Importing `std.common.compress` loads pure Simple modules only.
- There is no background initialization, no on-disk table generation, no worker startup, and no new runtime detector stack.
- The design continues to reserve SIMD integration for the existing runtime tier mechanism instead of introducing a second dispatch subsystem.

## Hot request paths

- `compress_bytes(input, options)`:
  - dispatches immediately on `options.codec`
  - LZ4 chooses raw block or frame mode
  - Zstd always emits a standard frame, with checksum requests normalized away because checksum emission is not implemented yet
  - LZMA2 normalizes raw requests back to framed XZ output
- `decompress_bytes(input, codec_hint?)`:
  - uses `detect_codec` when no hint is supplied
  - probes LZ4, Zstd, and XZ magics only
  - falls back to explicit-hint raw LZ4 decode for headerless blocks
- Streaming state:
  - `encoder_write` and `decoder_write` append into `pending`
  - `encoder_finish` and `decoder_finish` route through the same whole-buffer codec entrypoints as the single-shot API
  - current streaming semantics are buffered, not incremental block-by-block emission or decode

## Cache and table strategy

- No persistent codec cache exists in this phase.
- No global entropy tables, dictionary caches, window caches, or reusable match-finder indexes are retained between calls.
- Per-call work is limited to local descriptor parsing, rolling byte copies, and checksum calculation.
- This keeps startup cost flat and avoids invalidation complexity during the first umbrella landing.

## Reset and invalidation rules

- Reset is structural rather than imperative.
- Callers start a new stream by allocating a fresh `CompressionEncoderState` or `CompressionDecoderState`.
- `pending` is owned by the state value; discarding the old state discards buffered data.
- Because there are no global caches or cross-stream tables, there is no separate invalidation hook.

## SIMD and tier dispatch

- The umbrella requirement to reuse the existing SIMD tier API is preserved architecturally.
- The current code path is still scalar-only.
- No AVX2, NEON, or RVV kernels are wired in this slice, and there is no forced-tier parity evidence yet.
- Future SIMD work can attach under the existing runtime tier selection without changing the shared API or state model.

## Latency and RSS shape

- Startup cost should remain near-zero beyond normal module loading because the library builds no persistent tables.
- Single-shot encode/decode is linear in input size for the delivered subsets.
- Current streaming state buffers the full payload in memory before finish, so RSS scales with accumulated input size rather than with a bounded chunk window.
- The library hot path itself performs no subprocess launches, file IO, or full-tree scans.
