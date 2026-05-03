# Feature Requirements — `common_compression_framework`

Updated on 2026-05-04 to align the requirements with the currently landed
pure-Simple compression subset and its verified surface.

## Scope

This feature standardizes `std.common.compress` as the shared pure-Simple
compression facade for the repository. The live supported subset remains
limited to codecs already exposed by the facade: `lz4`, `zstd`, and `lzma2`.
No new codecs, no Rust/C codec bridge, and no runtime-owned duplicate
implementation are in scope.

## Functional Requirements

- REQ-001: Provide and preserve the public facade under `std.common.compress`
  as the shared ownership point for repository compression behavior.
- REQ-002: Preserve `CompressionCodec` with exactly `lz4`, `zstd`, and
  `lzma2`.
- REQ-003: Preserve `CompressionOptions` with codec, level, checksum flag,
  block mode, `dictionary_bytes`, `dictionary_id`, and `content_size`.
- REQ-004: Preserve `CompressionError` with explicit typed failures for invalid
  header, unsupported feature, truncated input, checksum mismatch, corrupt
  stream, and size-limit failure cases.
- REQ-005: Expose `try_compress_bytes(input, options) ->
  Result<[u8], CompressionError>` as the checked single-shot encode API.
- REQ-006: Keep `compress_bytes(input, options) -> [u8]` as the fail-fast
  wrapper over `try_compress_bytes`.
- REQ-007: Expose streaming encoder state and preserve
  `encoder_finish_checked(state) -> Result<[u8], CompressionError>` as the
  checked finalize API.
- REQ-008: Keep `encoder_finish(state) -> [u8]` as the fail-fast wrapper over
  `encoder_finish_checked`.
- REQ-009: Expose single-shot and streaming decode through `common.compress`,
  including codec auto-detect plus explicit codec hints where already wired by
  the facade.
- REQ-010: Support LZ4 block and frame encode/decode in pure Simple.
- REQ-011: LZ4 frame support must validate frame descriptors, block stream
  structure, optional content checksum, optional content size, and corruption
  typing across the focused facade tests.
- REQ-012: Support the currently landed Zstd framed subset in pure Simple:
  level `3` encode, focused frame decode paths exercised by the live specs, and
  the dedicated FSE Huffman-weight encode/decode lane covered by
  `zstd_fse_huffman_weight_encode_spec.spl`.
- REQ-013: Support XZ/LZMA2 framed encode/decode in pure Simple for the live
  verified subset, including host-`xz` interoperability and range-coded decode
  at LCLPPB `3/0/2`.
- REQ-014: Enforce block-mode semantics without silent normalization:
  `lz4` supports `block` and `frame`; `zstd` rejects modes other than `frame`;
  `lzma2` rejects modes other than `frame`.
- REQ-015: Unsupported option combinations that are not implemented today must
  fail through the checked APIs with `CompressionError.UnsupportedFeature`
  rather than being silently ignored or normalized. This includes unsupported
  dictionaries, unsupported Zstd levels, and unsupported LZMA2 parameter
  tuples outside the verified subset.
- REQ-016: Keep all feature implementation files for this feature in Simple
  code; no Rust/C codec bridge, fallback codec dependency, or runtime-owned
  parallel implementation is allowed.

## Verification-Coupled Functional Expectations

- REQ-017: Provide executable spec coverage for facade round-trip behavior,
  checked-API option failures, and typed corruption failures on the supported
  subset.
- REQ-018: Keep these focused codec gates green in the current tree:
  `test/unit/lib/common/lz4_spec.spl`,
  `test/unit/lib/common/lzma2_range_coded_spec.spl`,
  `test/unit/lib/common/xz_lzma2_spec.spl`, and
  `test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl`.
- REQ-019: Preserve typed rejection behavior for malformed or unsupported
  payloads in the focused subset rather than widening behavior silently.
- REQ-020: Keep the kernel Zstd loader as a thin adapter over
  `std.common.compress`.
- REQ-021: Keep scalar behavior as the correctness oracle for the shared helper
  paths that compression depends on; any forced-tier parity claims must match
  live executable coverage rather than planned future SIMD scope.
