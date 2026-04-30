# Local Research — `common_compression_framework`

## Existing code

- `src/lib/common/lz77/` already provides a pure-Simple sliding-window matcher and token stream expansion. It is suitable as an internal building block for LZ-family codecs, but it is not a public wire-format API.
- `src/lib/common/huffman/` provides reusable tree/codes/decode helpers that can be shared by later Zstd compressed-block work.
- `src/os/kernel/loader/zstd_decompress.spl` already proves a small zstd frame parser for raw and RLE blocks in production code.
- `src/lib/nogc_sync_mut/compression/` contains older ad hoc compression modules, but they are not the target public surface for `std.common.*`.
- `src/lib/nogc_sync_mut/simd.spl` already exposes the canonical runtime SIMD tier detector: `scalar`, `x86_64_avx2`, `aarch64_neon`, `riscv64_rvv`.

## Constraints from the feature request

- Public entrypoint must be `std.common.compress`.
- Delivery is one umbrella feature with phased rollout, not three unrelated codec drops.
- No new detector stack for SIMD dispatch.
- Standard-format interoperability matters more than codec-specific internal APIs.
- Non-host architecture work must at least compile and participate in fixture parity checks even when native perf hardware is unavailable.

## Implementation direction

- Create a shared façade with codec selection, validated levels, options, shared errors, and streaming state.
- Keep helper math, checksum, and bit-packing utilities close to existing common utilities; do not create a second math subsystem.
- Land working standard containers incrementally:
  - LZ4: block + frame
  - Zstd: raw/RLE frame subset first
  - XZ/LZMA2: single-filter LZMA2 pipeline with uncompressed chunks first
- Treat `src/lib/common/lz77` as an internal primitive instead of the final public API.

## Gaps identified before implementation

- No existing public `std.common.compress` façade.
- No shared compression error taxonomy.
- No test coverage for cross-format round trips through a shared API.
- No existing XZ/LZMA2 implementation in `src/lib/common/`.
