# Feature Requirements — `common_compression_framework`

Updated on 2026-05-01 to replace the earlier subset target with the full pure-Simple compression implementation target.

## Scope

This feature standardizes `std.common.compress` as the single shared pure-Simple compression library for the repository. The delivery target is full pure-Simple completion of LZ4, Zstd, and XZ/LZMA2 support behind that façade, including duplicate-path unification, checked encode APIs, interoperable dictionary metadata handling, shared helper extraction, and pure-Simple SIMD specialization. No new Rust/runtime compression bridge work is in scope.

## Functional Requirements

- REQ-001: Provide and preserve the public façade under `std.common.compress` as the shared ownership point for repository compression behavior.
- REQ-002: Preserve `CompressionCodec` with exactly `lz4`, `zstd`, and `lzma2`.
- REQ-003: Preserve `CompressionOptions` with codec, level, checksum flag, block mode, `dictionary_bytes`, `dictionary_id`, and `content_size`.
- REQ-004: Preserve `CompressionError` with explicit typed failures for invalid header, unsupported feature, truncated input, checksum mismatch, corrupt stream, and size-limit failure cases.
- REQ-005: Expose `try_compress_bytes(input, options) -> Result<[u8], CompressionError>` as the checked single-shot encode API.
- REQ-006: Keep `compress_bytes(input, options) -> [u8]` as the fail-fast wrapper over `try_compress_bytes`.
- REQ-007: Expose streaming encoder state and preserve `encoder_finish_checked(state) -> Result<[u8], CompressionError>` as the checked finalize API.
- REQ-008: Keep `encoder_finish(state) -> [u8]` as the fail-fast wrapper over `encoder_finish_checked`.
- REQ-009: Expose single-shot and streaming decode through `common.compress`, including codec auto-detect plus explicit codec hint support where already designed by the façade.
- REQ-010: Implement full pure-Simple LZ4 block encode/decode and frame encode/decode.
- REQ-011: LZ4 frame support must implement and validate descriptor flags, block stream structure, optional block checksums, optional content checksum, optional content size, and multi-block framing behavior.
- REQ-012: Implement full pure-Simple Zstd frame decode for normal host-generated frames, including frame-header variants, window/content-size validation, dictionary ID parsing, raw/RLE/compressed blocks, repeated FSE tables, compressed Huffman weights, treeless literals, 4-stream literals, checksum verification, and multi-block or multi-frame handling.
- REQ-013: Implement a real pure-Simple Zstd frame encoder with block splitting, sequence generation, literal compression, FSE/HUF emission, standards-compliant limits, optional checksum/content-size emission, and framed dictionary handling using `dictionary_bytes` plus `dictionary_id`.
- REQ-014: Implement full pure-Simple XZ/LZMA2 decode for `.xz` streams limited to the LZMA2-only filter chain, including stream and block validation, block/index/footer CRC verification, compressed and uncompressed LZMA2 chunks, multi-block streams, concatenated streams, and explicit failure for unsupported non-LZMA2 filter chains.
- REQ-015: Implement XZ + LZMA2 as the canonical pure-Simple encode format for `CompressionCodec.lzma2`.
- REQ-016: Enforce block-mode semantics without silent normalization: `lz4` must support `block` and `frame`; `zstd` must reject any mode other than `frame`; `lzma2` must reject any mode other than `frame`.
- REQ-017: Make `level` affect real compression behavior for each codec instead of remaining a documentation-only or default-only field.
- REQ-018: Make `checksum` emit and verify the codec’s normal framed checksum behavior where the format supports it.
- REQ-019: Make `content_size` emit and validate size metadata where the format supports it, and fail checked encode calls when the requested value is incompatible with the payload or codec rules.
- REQ-020: Honor `dictionary_bytes` plus `dictionary_id` for interoperable Zstd framed dictionary use.
- REQ-021: For LZ4 and LZMA2 dictionary combinations that the public option shape cannot yet express interoperably, return `CompressionError.UnsupportedFeature` from the checked encode APIs instead of silently normalizing or ignoring the request.
- REQ-022: Extract and share pure-Simple helper kernels for match extension, literal copy, overlap-safe match copy, CRC32, and XXH32 so codec modules reuse the same correctness core.
- REQ-023: Implement pure-Simple SIMD specializations for the shared helper kernels and relevant codec hot paths using the existing Simple-visible SIMD tier API only; no second dispatch stack and no new runtime/compiler feature work are allowed for this feature.
- REQ-024: The helper dispatch seam must allow tests to call scalar, AVX2, and NEON paths directly without host-dependent branching.
- REQ-025: Replace duplicate codec paths, including the kernel Zstd decoder, with thin adapters over `common.compress` that preserve their existing external interfaces while translating `CompressionError` as needed.
- REQ-026: Keep all feature implementation files for this feature in Simple code; no Rust/C codec bridge, fallback codec dependency, or runtime-owned parallel implementation is allowed.

## Verification-Coupled Functional Expectations

> Updated 2026-05-01 to reflect partial-landing reality; see `doc/09_report/verify_common_compression_framework.md` for the live failure list.

- REQ-027: Provide executable spec coverage for full roundtrip behavior, checked-API option failures, kernel-adapter parity, and typed corruption failures.
- REQ-028: Provide codec-focused unit or integration coverage for LZ4, Zstd, and XZ/LZMA2 using host-generated fixtures across small, medium, and large payloads; incompressible, repetitive, and mixed data; checksum on/off cases; multi-block cases; and dictionary cases where the API supports interoperability.
- REQ-029: Provide corruption and truncation matrices per codec, including bad headers, bad checksums, bad lengths, malformed entropy tables, unsupported filter chains, truncated block/index/footer tails, and invalid dictionary metadata.
- REQ-030 (Phase 1 / 2026-05-01): Provide forced-tier parity coverage for the helper paths that are SIMD-specialized today — checksum kernels (CRC32, XXH32) and byte-scan/copy kernels — comparing scalar against AVX2 and NEON outputs directly without relying on host-specific auto-detection.
- REQ-030 (Phase 2): Extend forced-tier parity coverage to SIMD-specialized codec hot paths (Zstd LZ77 match-search and codec-internal checksum kernels) once the SIMD int-intrinsics Phase 1 FR (`simd_int_intrinsics_for_crypto_2026-05-01`) lands. Until that FR lands, codec hot paths remain scalar and codec-output parity across forced tiers is not a Phase 1 acceptance criterion.
