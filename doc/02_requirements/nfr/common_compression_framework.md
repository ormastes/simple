# NFR Requirements — `common_compression_framework`

Updated on 2026-05-01 to replace the earlier subset NFR set with full pure-Simple delivery expectations.

- NFR-001 Correctness: The library must produce and consume standards-compliant LZ4, Zstd, and XZ/LZMA2 streams within the documented scope, and it must reject malformed or unsupported inputs with typed errors rather than partial success or silent normalization.
- NFR-002 Interoperability: Encoded output for supported option combinations must round-trip with normal host tooling and host-generated fixtures must decode successfully through `common.compress`.
- NFR-003 Pure-Simple Ownership: Compression behavior for this feature must remain implemented in `.spl` modules under shared-library ownership; no Rust/runtime bridge, alternate native codec path, or duplicate runtime-owned implementation is permitted.
- NFR-004 API Safety: Unsupported option combinations must fail through `try_compress_bytes` and `encoder_finish_checked` with `UnsupportedFeature` or another precise `CompressionError`; unchecked wrappers may fail fast but must not silently rewrite the user’s request.
- NFR-005 Dictionary Semantics: Zstd dictionary handling must require interoperable metadata treatment of `dictionary_bytes` and `dictionary_id`, and unsupported dictionary semantics for other codecs must fail closed.
- NFR-006 Performance: Shared scalar helpers must remain the correctness oracle, and pure-Simple SIMD specializations must improve or at minimum not materially regress hot helper paths for checksums, byte scans, and copy kernels on supported tiers.
- NFR-007 Tier Parity: Scalar, AVX2, and NEON helper paths must be byte-for-byte equivalent for the same inputs, and test coverage must prove parity without relying on host-specific auto-detection.
- NFR-008 Maintainability: Shared byte kernels, checksums, and dispatch logic must be centralized so codec modules do not grow divergent copies of the same low-level routines.
- NFR-009 Duplicate-Path Reduction: Consumers that currently own duplicate compression or decompression logic must adapt through thin wrappers to `common.compress` instead of keeping parallel codec engines.
- NFR-010 Reliability: Truncation, checksum mismatch, invalid frame metadata, malformed entropy tables, unsupported filter chains, and size-limit failures must be detected deterministically and surfaced with stable typed errors.
- NFR-011 Verification Gate (current state, updated 2026-05-01 — partially landed; see `doc/09_report/verify_common_compression_framework.md` for the live failure list): Focused codec specs PASS for LZ4 (block/frame round-trip, corruption typing, forced-tier parity) and XZ/LZMA2 (emitted-stream interoperability, concatenated streams, explicit unsupported compressed-chunk handling). The Zstd focused subset (level=3, no-dictionary framed variants) covers the first four passing cases of `zstd_frame_variants_spec.spl`, but per the verify WARN that lane has stalled on repeated fresh runs and cannot yet claim a clean current PASS. Residual gates required for full closure:
  - (a) Zstd encode levels other than `3` (currently rejected at `src/lib/common/compress/mod.spl:49`).
  - (b) Zstd decode of FSE-compressed Huffman weights and non-RLE compressed-block sequence tables (currently rejected at `src/lib/common/compress/zstd.spl:704` and `src/lib/common/compress/zstd.spl:324`).
  - (c) Dictionary-backed Zstd frames on decode and dictionary support across all codecs on encode (currently rejected at `src/lib/common/compress/zstd.spl:1265` and the facade at `src/lib/common/compress/mod.spl:49`).
  - (d) LZMA2 decode of range-coded compressed chunks (currently rejected at `src/lib/common/compress/lzma2.spl:330`).
  - (e) XZ/LZMA2 encode with `checksum=false` (currently rejected at the facade `src/lib/common/compress/mod.spl:49`).
  - (f) Zstd `zstd_frame_variants_spec.spl` runs to completion deterministically without stalling (currently a verify WARN).
  - (g) Repository `verify` reports `STATUS: PASS` once (a)–(f) close, alongside `bin/simple test`, `bin/simple build lint`, `sh scripts/check-core-runtime-smoke.shs bin/simple`, and `SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs`.
- NFR-012 Documentation Freshness: Research, requirements, architecture, design, system-test, and task artifacts for this feature must describe the full pure-Simple implementation target and must not preserve phased/subset commitments that contradict the delivered scope.
