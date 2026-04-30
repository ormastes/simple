# System Test Plan — `common_compression_framework`

## Core scenarios

- ST-001: LZ4 block round-trip with explicit codec hint.
- ST-002: LZ4 frame round-trip with auto-detect.
- ST-003: Zstd frame emitted by Simple is decodable by host `zstd`.
- ST-004: XZ/LZMA2 stream emitted by Simple is decodable by host `xz`.
- ST-005: Shared API streaming state produces the same payload as single-shot APIs.
- ST-006: Truncated and malformed payloads fail with a typed error.

## Deferred scenarios for later phases

- Full compressed-block Zstd interoperability from third-party compressors.
- Full entropy-coded LZMA2 streams from third-party compressors.
- SIMD forced-tier parity across AVX2, NEON, and RVV implementations once fast paths land.
