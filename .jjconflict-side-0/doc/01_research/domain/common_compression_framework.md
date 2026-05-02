<!-- codex-research -->
# Domain Research — `common_compression_framework`

Updated on 2026-05-01 to replace the earlier phased/subset framing with a full pure-Simple implementation target.

## Standards-complete interoperability targets

- LZ4 requires two interoperable surfaces:
  - raw block coding/decoding with correct token, literal-run, offset, and match-length handling
  - framed streams with descriptor validation, optional block checksum, optional content checksum, optional content size, and multi-block stream handling
- Zstd interoperability is defined by full frame behavior rather than only raw/RLE blocks:
  - frame header variants and window rules
  - block kinds: raw, RLE, and compressed
  - literals modes including raw, RLE, compressed, and treeless reuse
  - sequence sections driven by FSE tables, including repeated-table reuse
  - optional content checksum verification and emission
  - multi-block and concatenated/multi-frame handling
  - framed dictionary metadata via dictionary ID when a dictionary is used
- XZ interoperability requires container correctness plus full LZMA2 coding within the supported filter-chain bound:
  - stream header, block headers, index, and footer validation
  - CRC validation at the required container points
  - LZMA2 compressed and uncompressed chunks
  - multi-block and concatenated stream handling
  - explicit rejection of unsupported non-LZMA2 filter chains

## Engineering guidance from codec standards and common implementations

- Silent normalization of unsupported options is the wrong API behavior for standards work. If the public option shape cannot express an interoperable behavior, the checked encode APIs should return `UnsupportedFeature` rather than guess.
- Compression level must affect real encoder behavior. Treating `level` as documentation-only breaks user expectation and makes parity with host-generated fixtures difficult to reason about.
- Frame checksum and content-size fields are part of normal interoperability, not optional polish:
  - LZ4 content checksum and content size must be emitted and validated when selected.
  - Zstd content checksum and content size must be emitted and validated where the format supports them.
  - XZ integrity checks and size-related validations must be enforced per container semantics.
- Dictionary handling is metadata-sensitive:
  - for Zstd, framed interoperability requires both dictionary bytes and dictionary ID
  - for LZ4 and LZMA2, if the current public options cannot express an interoperable standard dictionary mode, the checked API should fail closed instead of pretending support

## Pure-Simple implementation feasibility

- All three codec families are implementable in pure language code because the repository already exposes the necessary categories of building blocks:
  - byte-array manipulation
  - bitstream parsing/emission
  - checksum helpers
  - Huffman/FSE-style table logic
  - Simple-visible SIMD tier detection and intrinsics
- SIMD optimization does not require a runtime bridge if the fast paths are framed as pure-Simple helper specializations under a scalar oracle.
- A shared helper layer is standard engineering for these codecs because the same hot operations recur across them:
  - match extension
  - literal copy
  - overlap-safe backreference copy
  - rolling or block checksums
  - short byte compares and scan loops

## Architectural implications from the standards target

1. `common.compress` must own the public façade and shared helper/kernel layer.
2. Codec-specific modules should contain wire-format logic, not bespoke copies of the same byte kernels and checksum routines.
3. Duplicate decode or encode consumers should adapt to `common.compress` instead of keeping parallel parsers.
4. SIMD dispatch should be one shared helper seam keyed by the existing Simple-visible tier enum, with tests able to invoke scalar and SIMD paths directly.
5. No Rust/runtime bridge belongs in this feature scope because it would split ownership, duplicate behavior, and undermine pure-Simple verification.

## Verification expectations implied by domain research

- Full-feature claims require executable coverage, not prose-only promises:
  - roundtrip fixtures for small, medium, large, repetitive, mixed, and incompressible payloads
  - host-generated fixtures for LZ4, Zstd, and XZ/LZMA2
  - dictionary fixtures where the API supports interoperability
  - corruption and truncation matrices per codec
- SIMD claims require parity testing, not only performance anecdotes:
  - direct scalar/AVX2/NEON helper comparisons
  - codec-output parity between forced-tier paths
- Shared-library unification requires adapter parity tests so legacy consumers such as the kernel Zstd loader are proven behaviorally equivalent at their public surface.
