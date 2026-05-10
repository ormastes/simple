# NFR Requirements — `common_compression_framework`

Updated on 2026-05-04 to align the NFRs with the currently re-verified subset
without overstating broader framework closure.

- NFR-001 Correctness: The library must produce and consume standards-compliant
  LZ4, Zstd, and XZ/LZMA2 streams within the documented scope, and it must
  reject malformed or unsupported inputs with typed errors rather than partial
  success or silent normalization.
- NFR-002 Interoperability: Encoded output for supported option combinations
  must round-trip with normal host tooling and host-generated fixtures must
  decode successfully through `common.compress`.
- NFR-003 Pure-Simple Ownership: Compression behavior for this feature must
  remain implemented in `.spl` modules under shared-library ownership; no
  Rust/runtime bridge, alternate native codec path, or duplicate
  runtime-owned implementation is permitted.
- NFR-004 API Safety: Unsupported option combinations must fail through
  `try_compress_bytes` and `encoder_finish_checked` with `UnsupportedFeature`
  or another precise `CompressionError`; unchecked wrappers may fail fast but
  must not silently rewrite the user’s request.
- NFR-005 Dictionary Semantics: Zstd dictionary handling must require
  interoperable metadata treatment of `dictionary_bytes` and `dictionary_id`,
  and unsupported dictionary semantics for other codecs must fail closed.
- NFR-006 Performance: Shared scalar helpers must remain the correctness
  oracle, and pure-Simple SIMD specializations must improve or at minimum not
  materially regress hot helper paths for checksums, byte scans, and copy
  kernels on supported tiers.
- NFR-007 Tier Parity: Scalar, AVX2, and NEON helper paths must be
  byte-for-byte equivalent for the same inputs, and test coverage must prove
  parity without relying on host-specific auto-detection.
- NFR-008 Maintainability: Shared byte kernels, checksums, and dispatch logic
  must be centralized so codec modules do not grow divergent copies of the
  same low-level routines.
- NFR-009 Duplicate-Path Reduction: Consumers that currently own duplicate
  compression or decompression logic must adapt through thin wrappers to
  `common.compress` instead of keeping parallel codec engines.
- NFR-010 Reliability: Truncation, checksum mismatch, invalid frame metadata,
  malformed entropy tables, unsupported filter chains, and size-limit failures
  must be detected deterministically and surfaced with stable typed errors.
- NFR-011 Verification Gate (current state, updated 2026-05-04): the
  currently confirmed green subset is limited to the focused lanes re-run in
  the latest closure pass:
  `test/unit/lib/common/lz4_spec.spl`,
  `test/unit/lib/common/lzma2_range_coded_spec.spl`,
  `test/unit/lib/common/xz_lzma2_spec.spl`, and
  `test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl`.
  This is useful evidence, but it is not full framework closure. Residual
  broader gates remain explicitly open:
  - (a) fresh re-verification of `test/unit/lib/common/compress_framework_spec.spl`
    as the facade-level contract lane.
  - (b) fresh re-verification of broader Zstd lanes such as
    `test/unit/lib/common/zstd_frame_variants_spec.spl`.
  - (c) explicit re-verification, merge, or retirement of overlapping older
    Zstd weight coverage such as `test/unit/lib/common/zstd_fse_weights_spec.spl`.
  - (d) broader option-surface closure for non-default Zstd levels,
    dictionary-backed encode flows, and other `CompressionOptions` semantics
    not covered by the current focused green subset.
  - (e) repository-level `verify` evidence reaching `STATUS: PASS` once the
    broader compression gates above are either closed or intentionally narrowed
    in the feature requirements.
- NFR-012 Documentation Freshness: Research, requirements, architecture,
  design, system-test, and task artifacts for this feature must describe the
  live supported subset and must not present unverified broader closure as
  completed fact.
