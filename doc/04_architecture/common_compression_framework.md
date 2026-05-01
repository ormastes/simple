# Architecture — `common_compression_framework`
<!-- codex-architecture -->
<!-- codex-design -->

## Status

This document defines the intended end-state architecture for `std.common.compress`. It replaces the prior subset/phased architecture. The target delivery is full pure-Simple compression support for LZ4, Zstd, and XZ/LZMA2 within the declared scope boundaries, with no new Rust/runtime codec bridge work.

## Architectural intent

- `src/lib/common/compress/` is the single owned compression implementation surface.
- Public callers depend on `std.common.compress`; duplicate codec engines are reduced to thin adapters or removed.
- All codec logic, byte kernels, checksums, entropy helpers, and SIMD-specialized hot paths remain in `.spl`.
- SIMD specialization uses existing Simple-visible SIMD detection/intrinsics only, centered on the existing tier/platform facilities in [src/compiler/30.types/simd_platform.spl](/home/ormastes/dev/pub/simple/src/compiler/30.types/simd_platform.spl:1) and [src/compiler/30.types/simd.spl](/home/ormastes/dev/pub/simple/src/compiler/30.types/simd.spl:1). No second runtime dispatch stack is introduced.

## Public structure

- [src/lib/common/compress/mod.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/mod.spl:1)
  Defines the stable facade, checked/fail-fast encode entrypoints, decode dispatch, and buffered streaming finish wrappers.
- [src/lib/common/compress/types.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/types.spl:1)
  Owns `CompressionCodec`, `CompressionLevel`, `CompressionOptions`, `CompressionError`, and buffered state types.
- [src/lib/common/compress/utilities.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/utilities.spl:1)
  Owns shared validation, byte-order helpers, codec detection, streaming-state helpers, checksum entrypoints, and target-independent utility kernels.
- [src/lib/common/compress/lz4.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lz4.spl:1)
  Owns full LZ4 raw block and framed encode/decode.
- [src/lib/common/compress/zstd.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd.spl:1)
  Owns full framed Zstd encode/decode orchestration.
- [src/lib/common/compress/zstd_bits.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_bits.spl:1), [zstd_fse.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_fse.spl:1), [zstd_huf.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/zstd_huf.spl:1)
  Own bitstream, FSE, and Huffman support used by the shared Zstd implementation.
- [src/lib/common/compress/lzma2.spl](/home/ormastes/dev/pub/simple/src/lib/common/compress/lzma2.spl:1)
  Owns XZ container handling plus full LZMA2 chunk encode/decode for the supported XZ filter-chain subset.

## Scope boundaries

- Included:
  - Full LZ4 support for raw block and frame modes.
  - Full Zstd framed encode/decode for normal host-generated frames through `CompressionCodec.zstd`.
  - Full XZ container support for streams whose filter chain is LZMA2-only.
  - Shared byte-kernel refactor across codecs.
  - Pure-Simple SIMD specialization for checksum, match-extension, and copy-heavy hot paths.
  - Replacement of duplicate consumers such as [src/os/kernel/loader/zstd_decompress.spl](/home/ormastes/dev/pub/simple/src/os/kernel/loader/zstd_decompress.spl:1) with thin adapters over `common.compress`.
- Excluded:
  - New Rust, C, or runtime codec helpers.
  - New runtime-level SIMD detection layers.
  - Non-LZMA2 XZ filter chains.

## Contract architecture

- `CompressionCodec` remains stable: `lz4`, `zstd`, `lzma2`.
- `CompressionOptions` remains the shared option carrier and includes `dictionary_id: i64?` because interoperable framed dictionary handling for Zstd cannot be expressed by `dictionary_bytes` alone.
- `try_compress_bytes(input, options)` and `encoder_finish_checked(state)` are the canonical checked encode surfaces.
- `compress_bytes` and `encoder_finish` remain fail-fast wrappers over the checked paths.
- `block_mode` is enforced, not normalized:
  - `lz4` accepts `block` and `frame`.
  - `zstd` requires `frame`.
  - `lzma2` requires `frame` because the emitted container is XZ.
- Unsupported option combinations fail closed with `CompressionError.UnsupportedFeature`; they are not silently rewritten.

## Shared-kernel architecture

The implementation is reorganized around reusable byte kernels instead of codec-local copies of the same logic.

- Shared scalar kernels are the oracle implementation for:
  - match extension
  - literal copy
  - overlap-safe match copy
  - CRC32
  - XXH32
  - bounded sequence/literal staging helpers
- Codec modules call these kernels through a narrow dispatch seam instead of embedding their own copy loops and checksum walkers.
- LZ4, Zstd, and LZMA2 remain codec owners for framing, grammar, and entropy semantics, but delegate common byte movement and checksum work downward.

This separation keeps `common` as the owner of stable data movement contracts while allowing per-codec logic to stay cohesive.

## SIMD seam

SIMD is an implementation detail under `common.compress`, not a parallel subsystem.

- The shared-kernel layer exposes tier-selectable entrypoints for scalar, AVX2, and NEON behavior.
- Runtime selection uses the existing Simple-visible SIMD/platform facilities only.
- Tests can call scalar/AVX2/NEON helper paths directly so parity does not depend on host capability.
- Scalar remains the correctness oracle; SIMD paths must be byte-for-byte identical.
- Initial SIMD ownership is limited to hot kernels:
  - CRC32 and XXH32 lanes/chunk walkers
  - LZ4/LZ77 match-extension probes
  - overlap-safe literal/match copy helpers
  - Zstd literal and sequence copy hot paths

## Codec architecture

### LZ4

- One codec module owns both raw block and frame semantics.
- Frame support includes descriptor flags, block-mode enforcement, block checksums, content checksum, content size emission/validation, and multi-block framing.
- Encode-side match finding shares the common LZ77-style helper seam where that reduces duplicated search/copy logic without obscuring LZ4 token rules.

### Zstd

- One pure-Simple implementation owns both framed decode and framed encode.
- Decoder architecture covers:
  - full frame header parsing
  - window and content-size validation
  - dictionary ID parsing/validation
  - raw, RLE, and compressed blocks
  - repeated FSE tables
  - compressed Huffman weights
  - treeless literals and 4-stream literals
  - checksum verification
  - multi-block and multi-frame inputs
- Encoder architecture covers:
  - block splitting
  - sequence generation
  - literal compression
  - FSE/HUF emission
  - checksum/content-size emission
  - framed dictionary support via `dictionary_bytes` plus `dictionary_id`
  - standards-compliant size/window constraints

### XZ/LZMA2

- `CompressionCodec.lzma2` means XZ container plus LZMA2 payload, not raw `.lzma`.
- The codec module owns:
  - XZ stream header/block/index/footer parsing and validation
  - CRC verification
  - multi-block streams
  - concatenated streams
  - full LZMA2 chunk encode/decode, including compressed chunks
- Non-LZMA2 XZ filter chains remain explicit `UnsupportedFeature`.

## Duplicate-consumer adapter model

- Shared library ownership sits in `src/lib/common/compress/`.
- Consumers with legacy signatures keep thin translation adapters only.
- The kernel Zstd loader adapter keeps its `Result<[u8], text>` shape and translates `CompressionError` rather than preserving a second parser.
- New codec consumers must depend on `common.compress` directly unless they need a legacy compatibility surface.

## Startup path

- Importing `std.common.compress` must not trigger background indexing, file IO, subprocesses, or runtime-generated table files.
- Startup work is limited to module load, constant initialization, and access to the existing SIMD capability surface when requested.
- Entropy tables, match structures, and checksum scratch storage are created lazily per call or per encoder/decoder state, not at process boot.

## Hot-path design

- Single-shot encode/decode must stay in-process and linear with the active codec grammar.
- Buffered streaming remains API-compatible, but the architectural target is to reduce codec-internal repeated rescans and duplicate copies even if the public state shape continues to accumulate `pending`.
- Hot handlers must not perform:
  - subprocess execution
  - file-system probing
  - full-tree scans
  - repeated rereads of immutable tables
- Shared kernels are the only sanctioned location for SIMD branching and copy/checksum specialization.

## Cache and invalidation strategy

- No persistent on-disk cache exists.
- No cross-process cache exists.
- Per-state reusable structures are allowed:
  - rolling checksum state
  - match-finder tables
  - decoded entropy tables that are valid only for the current frame/block progression
- Invalidation is ownership-based:
  - discarding `CompressionEncoderState` or `CompressionDecoderState` discards its reusable tables and scratch buffers
  - frame-local tables reset at frame boundaries
  - dictionary-derived tables reset when the dictionary identity or bytes change

## Performance targets

- Startup overhead: effectively flat beyond module load and existing SIMD capability queries.
- Hot-path latency target:
  - no avoidable repeated full-input rescans in frame/block handlers
  - no duplicate scalar and SIMD dispatch stacks
  - no per-request allocation storms for reusable codec tables
- RSS target:
  - bounded by active input, output, and codec working tables
  - no permanent global codec cache

These are design constraints to be checked by focused tests and smoke runs, not best-effort aspirations.

## Verification hooks

- Verification must prove round-trip correctness, host-tool interoperability, corruption typing, and checked-API enforcement.
- SIMD verification must prove scalar/AVX2/NEON parity by calling tier-specific helper paths directly.
- Because this feature lives under `src/lib/**`, verification closes with:
  - focused compression tests
  - full `bin/simple test`
  - `bin/simple build lint`
  - `sh scripts/check-core-runtime-smoke.shs bin/simple`
  - `SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs`
  - repository verify report showing PASS

## Worker-facing implementation lanes

This architecture intentionally exposes separable work lanes for parallel implementation without splitting ownership away from `common.compress`.

- Lane A: shared kernels and SIMD seam
- Lane B: LZ4 completion and helper adoption
- Lane C: Zstd full-frame completion plus adapter replacement
- Lane D: XZ/LZMA2 full-stream completion
- Lane E: verification fixtures, corruption matrix, and forced-tier parity

Each lane depends on the same facade contract and error taxonomy; none should introduce a new public compression API or a second codec ownership root.
