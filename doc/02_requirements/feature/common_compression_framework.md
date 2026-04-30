# Feature Requirements — `common_compression_framework`

## Scope

This umbrella feature introduces a public shared compression library at `std.common.compress` and covers LZ4, Zstd, and LZMA2/XZ with phased delivery. The chosen scope from the planning conversation is retained: one umbrella feature, standard-format interoperability, reuse of existing SIMD tier detection, and compile-plus-fixture parity expectations for non-host architectures.

## Functional Requirements

- REQ-001: Provide a public façade under `std.common.compress`.
- REQ-002: Expose `CompressionCodec` with `lz4`, `zstd`, and `lzma2`.
- REQ-003: Expose validated `CompressionLevel`.
- REQ-004: Expose `CompressionOptions` with codec, level, checksum flag, frame/block mode, optional dictionary bytes, and optional content size.
- REQ-005: Expose `CompressionError` with invalid header, unsupported feature, truncated input, checksum mismatch, corrupt stream, and size-limit failure categories.
- REQ-006: Expose single-shot `compress_bytes`.
- REQ-007: Expose single-shot `decompress_bytes` with codec auto-detect plus explicit hint support.
- REQ-008: Expose streaming encoder and decoder state types with write/finalize operations.
- REQ-009: Support standard LZ4 block and frame round-trip interoperability.
- REQ-010: Support standard Zstd frame handling for the delivered subset.
- REQ-011: Support standard XZ/LZMA2 handling for the delivered subset.
- REQ-012: Reject unsupported wire features explicitly instead of silently corrupting data.
- REQ-013: Reuse existing common helpers and existing SIMD tier detection rather than creating a parallel subsystem.

## Delivery framing

- REQ-014: Delivery is phased within one umbrella feature, not a big-bang merge.
- REQ-015: The first landing must include docs, tests, code, and verification artifacts together.
