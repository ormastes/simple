# System Test Plan — `common_compression_framework`

## Purpose

This plan replaces the current subset-oriented coverage with the full pure-Simple target for `std.common.compress`. The goal is executable system-spec coverage for complete LZ4, Zstd, and XZ/LZMA2 behavior, typed failure handling, duplicate-path unification, and forced SIMD-tier parity.

## Scope

- Public façade behavior under `std.common.compress`
- Checked and fail-fast encode entrypoints
- Streaming encoder/decoder parity with single-shot APIs
- Full LZ4 block and frame encode/decode behavior
- Full Zstd framed encode/decode behavior required for normal host-generated frames
- Full XZ container handling for the LZMA2-only filter chain
- Kernel Zstd adapter parity against `common.compress`
- Shared scalar/SIMD helper parity for scalar, AVX2, and NEON paths
- Typed corruption handling across all supported codecs

## Out of Scope

- Non-LZMA2 XZ filter chains beyond explicit failure coverage
- New Rust/runtime/compiler SIMD or codec implementation work
- Legacy duplicate codec implementations remaining as independent engines

## Requirement Traceability

| Requirement | Planned coverage |
|-------------|------------------|
| REQ-001 | Façade import, namespace stability, shared entrypoints |
| REQ-002 | Codec enum coverage for `lz4`, `zstd`, `lzma2` |
| REQ-003 | Validated level ranges affect real encode behavior |
| REQ-004 | `CompressionOptions` fields honored or rejected with typed failures |
| REQ-005 | Typed `CompressionError` categories asserted for malformed inputs |
| REQ-006 | `compress_bytes` fail-fast wrapper parity with checked API success paths |
| REQ-006A | `try_compress_bytes` typed option-failure and success coverage |
| REQ-007 | `decompress_bytes` auto-detect and explicit hint coverage |
| REQ-008 | Streaming encoder/decoder state parity and multi-write coverage |
| REQ-008A | `encoder_finish_checked` typed option-failure coverage |
| REQ-009 | Complete LZ4 block/frame interoperability and corruption matrix |
| REQ-010 | Complete Zstd frame interoperability, dictionaries, entropy paths, corruption matrix |
| REQ-011 | Complete XZ/LZMA2 interoperability, concatenation, block/index/footer validation |
| REQ-012 | Unsupported option combinations fail explicitly without silent normalization |
| REQ-013 | Kernel loader adapter parity with `common.compress` Zstd decode |
| REQ-014 | Shared helper reuse and forced scalar/AVX2/NEON parity coverage |

## Test Fixtures

### Payload classes

- Empty payload
- 1-byte and short literals
- Small payloads under one frame/block
- Medium payloads spanning multiple codec blocks
- Large payloads that exercise window/block splitting
- Highly repetitive payloads
- Incompressible payloads
- Mixed literal/match payloads
- Overlap-heavy payloads for match-copy edge cases

### External fixture sources

- Host-generated LZ4 frames with and without block/content checksum
- Host-generated Zstd frames covering raw, RLE, and compressed blocks
- Host-generated Zstd frames with repeated FSE tables, compressed Huffman weights, treeless literals, and 4-stream literals
- Host-generated Zstd dictionary-backed frames carrying both dictionary bytes and dictionary id
- Host-generated XZ streams with multi-block and concatenated-stream layouts using the LZMA2-only filter chain

## Executable Coverage Matrix

### Façade and API semantics

- ST-API-001: `compress_bytes` round-trips each supported codec through `decompress_bytes`
- ST-API-002: `try_compress_bytes` succeeds for supported option combinations and matches `compress_bytes`
- ST-API-003: `compress_bytes` traps on the same invalid requests that `try_compress_bytes` reports as typed errors
- ST-API-004: `encoder_finish_checked` matches `try_compress_bytes` output for buffered input
- ST-API-005: streaming encode/decode state across multiple writes matches single-shot behavior
- ST-API-006: auto-detect selects LZ4, Zstd, and XZ/LZMA2 from framed bytes
- ST-API-007: explicit LZ4 block hint is required for raw block decode and succeeds when supplied
- ST-API-008: `level` changes actual emitted output or codec parameters rather than being ignored
- ST-API-009: `content_size` is emitted and verified where supported
- ST-API-010: `checksum` emits and validates normal framed checksum modes where supported
- ST-API-011: `dictionary_bytes` plus `dictionary_id` are honored for Zstd framed dictionary use
- ST-API-012: unsupported dictionary combinations for LZ4 and LZMA2 return `UnsupportedFeature`
- ST-API-013: `block_mode` is enforced, with LZ4 supporting `block` and `frame`, while Zstd and LZMA2 reject `block`

### LZ4

- ST-LZ4-001: raw block round-trip for empty, short, medium, and large payloads
- ST-LZ4-002: frame round-trip with content size enabled
- ST-LZ4-003: frame round-trip with block checksum enabled
- ST-LZ4-004: frame round-trip with content checksum enabled
- ST-LZ4-005: multi-block framing preserves payload across block boundaries
- ST-LZ4-006: host-generated standard frames decode successfully
- ST-LZ4-007: Simple-generated frames decode with host LZ4 tools
- ST-LZ4-008: overlap-heavy matches decode identically across scalar and SIMD helper tiers

### Zstd

- ST-ZSTD-001: host-generated normal frames decode across frame-header variants and window/content-size combinations
- ST-ZSTD-002: raw, RLE, and compressed block decoding succeeds
- ST-ZSTD-003: repeated FSE tables are accepted and reused correctly
- ST-ZSTD-004: compressed Huffman weights decode correctly
- ST-ZSTD-005: treeless literals decode correctly
- ST-ZSTD-006: 4-stream literals decode correctly
- ST-ZSTD-007: multi-block and multi-frame decode succeeds
- ST-ZSTD-008: Simple-generated frames decode with host `zstd`
- ST-ZSTD-009: encoder emits standards-compliant frames for small, medium, and large payloads
- ST-ZSTD-010: dictionary-backed framed encode/decode succeeds only when `dictionary_bytes` and `dictionary_id` align
- ST-ZSTD-011: content checksum emission and validation succeed
- ST-ZSTD-012: content-size emission and validation succeed

### XZ/LZMA2

- ST-XZ-001: Simple-generated `.xz` streams decode with host `xz`
- ST-XZ-002: host-generated LZMA2-only `.xz` streams decode successfully
- ST-XZ-003: compressed LZMA2 chunks decode successfully, not only uncompressed chunks
- ST-XZ-004: multi-block `.xz` streams decode successfully
- ST-XZ-005: concatenated `.xz` streams decode successfully
- ST-XZ-006: block header, index, and footer validation are enforced
- ST-XZ-007: CRC32 verification is enforced for block and stream structures
- ST-XZ-008: non-LZMA2 filter chains fail explicitly with `UnsupportedFeature`

### Corruption and truncation matrices

- ST-CORR-001: bad magic/header per codec returns `InvalidHeader` or equivalent typed failure
- ST-CORR-002: truncated frame/block payload per codec returns `TruncatedInput`
- ST-CORR-003: checksum corruption per codec returns `ChecksumMismatch`
- ST-CORR-004: malformed LZ4 lengths/tokens fail closed with `CorruptStream`
- ST-CORR-005: malformed Zstd entropy tables fail closed with `CorruptStream`
- ST-CORR-006: invalid Zstd dictionary metadata fails explicitly
- ST-CORR-007: invalid XZ index/footer tails fail closed
- ST-CORR-008: unsupported XZ filter chain metadata fails explicitly
- ST-CORR-009: size-limit and impossible-content-size cases fail with typed size errors

### Kernel-adapter parity

- ST-KERNEL-001: kernel `zstd_decompress` output matches `common.compress.decompress_bytes(..., CompressionCodec.zstd)` byte-for-byte
- ST-KERNEL-002: kernel adapter translates each relevant `CompressionError` into its legacy `Result<[u8], text>` error contract deterministically

### Forced-tier parity

- ST-SIMD-001: scalar, AVX2, and NEON CRC32 helpers produce identical outputs on the same inputs
- ST-SIMD-002: scalar, AVX2, and NEON XXH32 helpers produce identical outputs on the same inputs
- ST-SIMD-003: scalar, AVX2, and NEON match-extension helpers produce identical match lengths
- ST-SIMD-004: scalar, AVX2, and NEON literal-copy helpers produce identical copies
- ST-SIMD-005: scalar, AVX2, and NEON overlap-safe match-copy helpers produce identical buffers
- ST-SIMD-006: codec outputs forced through scalar, AVX2, and NEON helper seams remain byte-for-byte identical

## Execution Plan

1. Run façade and checked-API specs first to lock option semantics.
2. Run codec-focused round-trip and interoperability suites for LZ4, Zstd, and XZ/LZMA2.
3. Run corruption matrices per codec after happy-path suites.
4. Run forced-tier helper parity and codec parity suites in compiled mode.
5. Run kernel-adapter parity after Zstd decode integration lands.
6. Finish with focused compression specs, full `bin/simple test`, `bin/simple build lint`, core runtime smoke, MCP native smoke, and `$verify`.

## Environment Requirements

- Compiled-mode spec execution for real `it` body coverage
- Host `lz4`, `zstd`, and `xz` tools available for interoperability fixture generation or verification
- Fixture inputs checked into repo or generated deterministically by test helpers
- Ability to force scalar, AVX2, and NEON helper paths without host-dependent auto-selection

## Pass Criteria

- Every REQ-001 through REQ-014 has executable spec coverage
- No subset-only wording remains in the plan or spec
- All supported codecs pass round-trip, interoperability, corruption, and parity lanes
- Unsupported combinations fail with typed errors, not silent normalization
- Kernel adapter is proven equivalent to the shared Zstd decoder path
- Forced-tier parity shows no scalar/SIMD divergence
