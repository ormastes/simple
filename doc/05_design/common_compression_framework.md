# Detail Design — `common_compression_framework`
<!-- codex-design -->

## Design goal

The implementation target is the full pure-Simple compression library promised by the current feature intent, not the currently landed subset. This document defines the concrete module interactions, helper seams, option semantics, and verification-oriented work partition for that target.

## Stable public API

- `CompressionCodec`
  - `lz4`
  - `zstd`
  - `lzma2`
- `CompressionLevel`
  - validated wrapper over codec-specific numeric ranges
  - implementation must make `level` affect real compression behavior instead of accepting-but-ignoring it
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

## API semantics

- `try_compress_bytes(input, options) -> Result<[u8], CompressionError>`
  - canonical checked encode path
  - rejects unsupported or non-representable option combinations before codec-local emission begins
- `compress_bytes(input, options) -> [u8]`
  - thin fail-fast wrapper over `try_compress_bytes(...).unwrap()`
- `encoder_finish_checked(state) -> Result<[u8], CompressionError>`
  - canonical checked finish path for buffered encode state
- `encoder_finish(state) -> [u8]`
  - thin fail-fast wrapper over `encoder_finish_checked(...).unwrap()`
- `decompress_bytes(input, codec_hint?)`
  - detects framed codecs by magic when possible
  - preserves explicit raw-LZ4 hinting for headerless blocks

## Required option behavior

- `level`
  - LZ4 must map level to match-search effort / parser behavior.
  - Zstd must map level to real block-splitting and entropy/compression choices.
  - LZMA2 must map level to dictionary/match-finder/preset behavior within the supported XZ+LZMA2 configuration.
- `checksum`
  - LZ4 frame: emit and verify standard block/content checksum fields when selected.
  - Zstd: emit and verify the standard frame content checksum mode.
  - XZ/LZMA2: emit and verify the selected supported XZ integrity mode; within current scope this stays bounded by the XZ/LZMA2 design decisions documented by the owning workers.
- `content_size`
  - emitted where the format supports it
  - validated on decode where the format supplies it
  - mismatches are errors, not normalization points
- `dictionary_bytes` + `dictionary_id`
  - Zstd framed dictionary handling must honor both fields together.
  - If only one field is present when both are required for interoperable framing, the checked path must fail.
  - LZ4 and LZMA2 must return `UnsupportedFeature` until the public option surface can express their interoperable dictionary requirements.
- `block_mode`
  - `lz4`: `block` or `frame`
  - `zstd`: `frame` only
  - `lzma2`: `frame` only

## Internal module layout

- [src/lib/common/compress/mod.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/mod.spl:1)
  - facade entrypoints
  - top-level option enforcement
  - dispatch to codec modules
- [src/lib/common/compress/types.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/types.spl:1)
  - stable public data model
- [src/lib/common/compress/utilities.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/utilities.spl:1)
  - shared validation
  - byte-order reads/writes
  - codec detect helpers
  - streaming append/reset helpers
  - checksum entrypoints
- `shared-kernel seam` within `common.compress`
  - scalar helpers
  - AVX2 helpers
  - NEON helpers
  - direct-call test hooks for each tier
- [src/lib/common/compress/lz4.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lz4.spl:1)
  - LZ4 framing/parser/token logic
- [src/lib/common/compress/zstd.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd.spl:1)
  - Zstd frame orchestration
- [src/lib/common/compress/zstd_bits.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_bits.spl:1)
  - bit-reader/writer primitives
- [src/lib/common/compress/zstd_fse.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_fse.spl:1)
  - FSE table build/use
- [src/lib/common/compress/zstd_huf.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_huf.spl:1)
  - Huffman table build/use
- [src/lib/common/compress/lzma2.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lzma2.spl:1)
  - XZ framing/index/footer plus LZMA2 coder/parser

## Shared-kernel seam

The implementation should extract duplicated byte work into a shared helper seam instead of keeping codec-local copies.

- Required helpers:
  - `match_extend_*`
  - `copy_literals_*`
  - `copy_match_overlap_*`
  - `crc32_*`
  - `xxh32_*`
  - bounded chunk/sequence staging helpers needed by LZ4 and Zstd
- Dispatch model:
  - scalar helper functions are always available
  - AVX2/NEON helpers are optional at runtime but directly invocable in tests
  - one selector chooses the active tier for production calls
- Correctness model:
  - scalar result is the oracle
  - SIMD helpers must preserve exact bytes, lengths, and checksum results

## LZ4 design

- Decode path:
  - parse raw-block tokens and frame envelopes
  - validate frame descriptor checksum, block sizes, end marker, optional content size, optional block checksum, optional content checksum
  - support multi-block frames
- Encode path:
  - block mode emits standard raw block
  - frame mode emits standard descriptor, blocks, end marker, and requested checksums
  - match finding uses shared LZ77-style helper utilities where they reduce duplication
  - overlap-safe match copy flows through the shared copy kernel seam
- Error model:
  - malformed token or impossible back-reference: `CorruptStream`
  - short descriptor/block/checksum tail: `TruncatedInput`
  - unsupported dictionary request: `UnsupportedFeature`

## Zstd design

- Decode path:
  - parse all normal frame header variants
  - validate declared window and content size against safe limits
  - parse and validate dictionary ID metadata
  - handle raw, RLE, and compressed blocks
  - support repeated FSE tables
  - support compressed Huffman weights
  - support raw/RLE/compressed literals, including treeless and 4-stream forms
  - support checksum verification
  - support multi-block and multi-frame payloads
- Encode path:
  - split input into standards-compliant blocks
  - generate sequences and literal sections
  - emit FSE/HUF tables and payloads
  - choose compression strategy from `level`
  - emit checksum and content-size metadata when requested/supported
  - support framed dictionary encode using both `dictionary_bytes` and `dictionary_id`
- Shared helpers:
  - bitstream helpers stay in `zstd_bits`
  - entropy helpers stay in `zstd_fse` and `zstd_huf`
  - byte-copy and checksum work flows through shared kernels
- Consumer unification:
  - [src/os/kernel/loader/zstd_decompress.spl](/home/ormastes/dev/pub/simple/src/os/kernel/loader/zstd_decompress.spl:1) becomes a thin adapter translating `CompressionError` to `Result<[u8], text>`

## XZ/LZMA2 design

- Container scope:
  - `.xz` stream parsing and emission
  - block header/index/footer validation
  - stream and block CRC verification
  - multi-block streams
  - concatenated streams
- Filter scope:
  - LZMA2-only filter chain supported
  - any alternate filter chain fails explicitly with `UnsupportedFeature`
- LZMA2 coder/parser:
  - support compressed and uncompressed chunks
  - maintain dictionary/reset-state semantics across chunk boundaries
  - map `level` to the actual LZMA2 encoder preset behavior
- Canonical encode format:
  - emit XZ container with LZMA2 payload for `CompressionCodec.lzma2`

## Streaming state design

- Public streaming state remains buffered in the current facade shape unless a coordinated API change happens elsewhere.
- `encoder_write` and `decoder_write` append to `pending`.
- `encoder_finish_checked` and `decoder_finish` route through the same codec implementations as single-shot APIs.
- Internal codec helpers may still use chunk/block incremental processing to avoid repeated rescans and duplicate allocation inside the finish path.
- State-local reusable structures are allowed:
  - LZ4 match tables
  - Zstd entropy tables and sequence scratch buffers
  - LZMA2 dictionary/match-finder scratch

## Startup, hot path, and cache considerations

- Startup must remain near-zero:
  - no subprocesses
  - no file IO
  - no precomputed on-disk tables
  - no second SIMD detector
- Hot paths must stay fully in-process:
  - block parsers and emitters
  - entropy decoders/encoders
  - shared byte kernels
- Allowed reusable caches are state-local or frame-local only.
- Invalidation rules:
  - drop encoder/decoder state to drop its scratch tables
  - reset entropy/dictionary-derived state at frame boundaries or dictionary changes
  - no global cache invalidation protocol is needed because there is no process-global codec cache

## Verification hooks built into the design

- Tier-specific helper entrypoints must be callable directly by tests for scalar/AVX2/NEON parity.
- Each codec must expose enough internal determinism for fixture-based corruption and truncation testing.
- Checked APIs must fail before emission for invalid option combinations.
- Duplicate-consumer adapters must be verifiable against the shared codec outputs instead of preserving divergent logic.

## Worker lane breakdown for spawned agents

This section is the intended task split for parallel workers consuming this design. It does not create new ownership roots; every lane still lands under `common.compress` or its direct adapter.

- Worker 1: shared helper extraction and scalar oracle seam
  - extract match/copy/checksum helpers from codec-local code
  - define direct-call scalar helper test surface
- Worker 2: SIMD specialization lane
  - add AVX2/NEON helper implementations using existing Simple-visible SIMD facilities
  - add forced-tier parity tests against scalar
- Worker 3: LZ4 completion lane
  - finish full frame/block semantics
  - adopt shared kernels in match/copy/checksum hot spots
- Worker 4: Zstd completion lane
  - finish full decode coverage and real encoder
  - replace kernel-local decoder with thin adapter
- Worker 5: XZ/LZMA2 completion lane
  - finish compressed chunks, block/index/footer validation, and concatenated-stream handling
- Worker 6: verification/fixtures lane
  - host-generated fixtures
  - corruption/truncation matrices
  - adapter parity and checked-API failure coverage

## Design invariants

- No new Rust/C/runtime codec engine is allowed.
- No second dispatch stack is allowed for SIMD.
- No silent normalization of unsupported options is allowed.
- `common.compress` remains the single ownership root for shared compression behavior.
