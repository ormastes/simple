# Detail Design — `common_compression_framework`
<!-- codex-design -->

## Shared API

- `CompressionCodec`
  - `lz4`
  - `zstd`
  - `lzma2`
- `CompressionLevel`
  - validated wrapper around codec-specific numeric ranges
  - current validation:
    - LZ4 `0..16`
    - Zstd `1..22`
    - LZMA2 `0..9`
- `CompressionOptions`
  - shared shape for codec, level, checksum, block mode, optional dictionary bytes, and optional content size
- `CompressionError`
  - shared failure surface for malformed framing, truncation, checksum mismatches, corruption, and unsupported standard features
- `CompressionEncoderState` / `CompressionDecoderState`
  - append-and-finish state wrappers over buffered `pending` bytes

## Current phased behavior

The module shape is umbrella-ready, but the implementation is deliberately narrower than the long-term API contract.

- Delivered now:
  - LZ4 raw block and frame interoperability
  - Zstd frame interoperability for raw and RLE blocks
  - XZ/LZMA2 interoperability for single-filter, uncompressed-chunk streams
- Deferred explicitly:
  - Zstd compressed blocks
  - Zstd dictionary ids and window descriptors
  - Zstd content checksum verification
  - compressed LZMA2 chunks
  - multi-block XZ streams
  - non-CRC32 XZ check types
  - SIMD fast paths and forced-tier parity
  - truly incremental streaming encode/decode

## Shared control flow

- `default_compression_options(codec)` provides the stable default entrypoint shape.
- `compress_bytes` dispatches by codec and normalizes unsupported option combinations into the supported framed subset where needed.
- `decompress_bytes` resolves codec either from magic bytes or from an explicit hint, then delegates to the codec parser.
- Raw LZ4 decode is the only headerless path and therefore depends on an explicit hint.

## Streaming state design

- `new_encoder_state` and `new_decoder_state` allocate empty buffered state.
- `encoder_write` and `decoder_write` append each incoming byte into `pending`.
- `encoder_finish` and `decoder_finish` call the same whole-buffer compression and decompression functions as the single-shot API.
- Consequence:
  - streaming currently preserves API shape and chunk-boundary tests
  - streaming does not yet preserve bounded-memory behavior for large payloads
  - reset is achieved by creating a fresh state rather than mutating the existing one back to empty

## Codec-specific design

### LZ4

- Raw block format is implemented directly.
- Frame writer emits standard LZ4 framing, descriptor checksum, end marker, and optional content checksum.
- Frame reader distinguishes raw blocks from compressed blocks using the block-size flag and validates the standard frame prologue.
- Match search remains scalar and greedy, bounded by the LZ4 64 KiB offset window.

### Zstd

- Writer emits a valid standard frame for the implemented subset.
- Current emission strategy uses raw or RLE blocks only.
- Reader accepts raw and RLE block types and rejects compressed blocks explicitly.
- Reader also rejects:
  - window descriptors
  - dictionary ids
  - content checksum verification requests
- This keeps the first phase externally interoperable for emitted streams while avoiding a partial entropy decoder hidden behind the shared API.

### XZ/LZMA2

- Writer emits one XZ stream with:
  - one block
  - one LZMA2 filter
  - CRC32-based integrity checks
  - uncompressed LZMA2 chunks
- Reader validates:
  - XZ header magic
  - stream flags
  - block structure
  - CRC32-based integrity fields
  - LZMA2 uncompressed chunk boundaries
- Reader rejects:
  - compressed LZMA2 chunks
  - unsupported XZ check kinds
  - more than one XZ block

## Cache, tables, and invalidation

- No global cache is retained.
- No dictionary table or entropy table survives past a single call.
- Checksum helpers are computed on demand from bytes already in memory.
- There is no cache invalidation protocol because the current implementation keeps no persistent cacheable state.

## Hot-path constraints

- Library hot paths remain pure in-process byte transforms.
- The implementation performs no subprocess launches, no external tool calls, and no file IO during compression or decompression.
- External `zstd` and `xz` usage exists only in tests to prove emitted-stream interoperability.
- Because current streaming buffers the full payload, memory growth is proportional to accumulated input until `finish`.

## Error handling

- `InvalidHeader`
  - bad magic
  - impossible descriptor layout
  - codec auto-detect failure
- `TruncatedInput`
  - insufficient bytes for frame fields or block payloads
- `ChecksumMismatch`
  - reserved for implemented checksum mismatches
- `CorruptStream`
  - malformed but recognized framing
- `UnsupportedFeature`
  - any standard feature intentionally left outside the delivered subset

## Observability and verification hooks

- There are no runtime counters or profiling hooks inside the library yet.
- Verification currently relies on focused unit/spec coverage plus smoke checks around the surrounding runtime/tooling environment.
- Since this is `src/lib/**` work, the design expects core runtime and MCP smoke evidence to be tracked alongside the feature report.
