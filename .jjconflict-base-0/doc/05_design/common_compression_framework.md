# Detail Design — `common_compression_framework`
<!-- codex-design -->

## Design goal

This document records the current landed design for `std.common.compress` as verified on 2026-05-01. It intentionally distinguishes stable API shape from still-unsupported codec behavior.

## Stable public API

- `CompressionCodec`
  - `lz4`
  - `zstd`
  - `lzma2`
- `CompressionLevel`
  - validated against codec-specific numeric ranges
  - the facade still narrows accepted encode levels further for some codecs
- `CompressionOptions`
  - `codec`
  - `level`
  - `checksum`
  - `block_mode`
  - `dictionary_bytes`
  - `dictionary_id`
  - `content_size`
- `CompressionError`
  - `InvalidHeader`
  - `UnsupportedFeature`
  - `TruncatedInput`
  - `ChecksumMismatch`
  - `CorruptStream`
  - `SizeLimitExceeded`
- buffered state types
  - `CompressionEncoderState`
  - `CompressionDecoderState`

## Current API semantics

- `try_compress_bytes(input, options) -> Result<[u8], CompressionError>`
  - validates the shared contract before codec-local encode begins
  - rejects unsupported option combinations instead of rewriting them
- `compress_bytes(input, options) -> [u8]`
  - unwraps the checked path
- `encoder_finish_checked(state) -> Result<[u8], CompressionError>`
  - routes buffered encode through the same checked validation path
- `encoder_finish(state) -> [u8]`
  - unwraps `encoder_finish_checked`
- `decompress_bytes(input, codec_hint?)`
  - auto-detects framed LZ4, Zstd, and XZ/LZMA2 payloads
  - still requires an explicit LZ4 hint for raw blocks

## Current option behavior

- `level`
  - LZ4 levels validate in `0..16`, but the facade currently accepts only encode level `1`.
  - Zstd levels validate in `1..22`, but the facade currently accepts only encode level `3`.
  - LZMA2 levels validate in `0..9`; the current facade does not reject non-default levels, but current verification only proves the default emitted stream shape.
- `checksum`
  - LZ4 frame mode can emit and verify block/content checksums.
  - Zstd frame mode can emit and verify frame content checksums.
  - LZMA2/XZ encode currently requires `checksum=true` because the encoder always emits CRC32-backed XZ checks.
- `content_size`
  - the checked path requires any declared content size to match the input length
  - LZ4 block mode rejects `content_size`
- `dictionary_bytes` and `dictionary_id`
  - all current codecs reject dictionary-backed encode requests
  - Zstd decode also rejects non-zero dictionary-backed frames
  - `dictionary_id` without `dictionary_bytes` is rejected before codec dispatch
- `block_mode`
  - `lz4`: `block` or `frame`
  - `zstd`: `frame` only
  - `lzma2`: `frame` only

## Internal module layout

- [src/lib/common/compress/mod.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/mod.spl:1)
  - shared validation and dispatch
- [src/lib/common/compress/types.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/types.spl:1)
  - public data model
- [src/lib/common/compress/utilities.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/utilities.spl:1)
  - default options, checksum helpers, codec detection, and tier helpers
- [src/lib/common/compress/lz4.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lz4.spl:1)
  - LZ4 block and frame logic
- [src/lib/common/compress/zstd.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd.spl:1)
  - current Zstd frame parser and emitter subset
- [src/lib/common/compress/zstd_bits.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_bits.spl:1)
  - bit-reader/writer primitives
- [src/lib/common/compress/zstd_fse.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_fse.spl:1)
  - FSE table helpers
- [src/lib/common/compress/zstd_huf.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_huf.spl:1)
  - Huffman table helpers
- [src/lib/common/compress/lzma2.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lzma2.spl:1)
  - XZ container handling plus the current LZMA2 subset

## Codec-specific design notes

### LZ4

- Encode supports raw blocks and independent-block frames.
- Decode validates descriptor checksum, optional content size, optional block/content checksums, and block boundaries.
- Tier-forced encode/decode entrypoints are already present for scalar, AVX2, and NEON parity tests.
- The facade intentionally rejects unsupported dictionary requests and non-level-1 encode selection.

### Zstd

- Encode emits the current framed subset and can set the frame checksum bit.
- Decode covers the currently tested header forms, concatenated frames, raw blocks, and the emitted checksum mode.
- The implementation still rejects:
  - non-RLE sequence tables in compressed blocks
  - dictionary-backed frames
  - the missing compressed-Huffman-weight cases called out by verification
- Tier-forced encode/decode entrypoints already exist for scalar, AVX2, and NEON parity tests.

### XZ/LZMA2

- Encode emits XZ streams that host `xz` can decode.
- Decode validates XZ structure, CRCs, aligned stream padding, and concatenated streams.
- The implementation explicitly does not decode range-coded compressed LZMA2 chunks yet.
- Non-LZMA2 filter chains remain typed `UnsupportedFeature`.
- Tier-forced encode/decode entrypoints already exist for scalar, AVX2, and NEON parity tests.

## Streaming state design

- Public streaming remains buffered:
  - `encoder_write` and `decoder_write` append to `pending`
  - `encoder_finish_checked` and `decoder_finish` route through the same single-shot codec paths
- This means streaming behavior is currently correctness-oriented rather than truly incremental.

## Verification-oriented invariants

- Checked APIs must reject unsupported combinations before encode dispatch.
- Raw LZ4 blocks must remain explicitly hinted.
- LZ4 frame corruption must fail with typed errors.
- Zstd support claims must stay limited to the landed framed subset.
- XZ/LZMA2 support claims must stay limited to emitted streams plus explicit unsupported-feature handling for compressed chunks.

## Still-open design gaps

- The docs can no longer claim full Zstd compressed-block coverage.
- The docs can no longer claim general compressed-chunk LZMA2 decode.
- The docs can no longer claim forced-tier scalar/AVX2/NEON requirement closure for the whole feature; focused parity tests exist, but requirement-level closure is still broader than the verified surface.
- The docs should not claim repository `verify` PASS for this feature until the requirement docs are narrowed or the missing codec behavior lands.
