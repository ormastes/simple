<!-- codex-research -->
# Local Research — `common_compression_framework`

Updated on 2026-05-01 to replace the earlier subset/phased target with the full pure-Simple implementation target.

## Existing code and current state

- `src/lib/common/compress/` already exists as the intended shared library ownership point. It has a façade in `mod.spl`, shared types in `types.spl`, and active codec work for `lz4`, `zstd`, and `lzma2`.
- The façade already exposes the stable public shape required by the feature direction:
  - `CompressionCodec` remains `lz4`, `zstd`, `lzma2`.
  - `CompressionOptions` already includes `dictionary_id: i64?` alongside `dictionary_bytes: [u8]?`.
  - `try_compress_bytes(...)` and `encoder_finish_checked(...)` already exist next to the fail-fast wrappers.
- The current implementation is still subset-oriented:
  - `zstd` encode currently rejects non-default levels, checksum emission, and dictionaries.
  - `lzma2/xz` encode currently rejects non-default levels, dictionary use, and checksum selection, and the existing direction is still narrower than a full LZMA2 codec.
  - option validation still reflects a staged subset rather than the final standards-complete target.
- `src/os/kernel/loader/zstd_decompress.spl` is already a thin adapter over `common.compress`, translating `CompressionError` into `Result<[u8], text>`. This confirms the duplicate-path unification direction is viable and should remain the pattern for any other duplicate consumers.

## Reusable pure-Simple building blocks already in-tree

- `src/lib/common/lz77/` provides a pure-Simple sliding-window foundation that can be reused for LZ4, Zstd sequence generation, and LZMA2 match/literal decisions instead of growing separate match finders per codec.
- `src/lib/common/huffman/` provides reusable Huffman tree/code/decode helpers that can support Zstd literal compression and decode paths.
- `src/lib/common/compress/zstd_fse.spl` shows the tree already contains pure-Simple FSE decode-table work, which reduces risk for completing full Zstd compressed-block support without a runtime bridge.
- `src/lib/nogc_sync_mut/simd.spl` exposes the Simple-visible tier detector and enum (`scalar`, `x86_64_avx2`, `aarch64_neon`, `riscv64_rvv`). This is the canonical dispatch seam for compression SIMD work; a second detector stack is not justified.

## Local code constraints that the updated artifacts must reflect

- The feature must stay inside `.spl` ownership. The façade and current codec modules prove that the repository is already pointed at a pure-Simple solution, not a Rust/runtime codec bridge.
- The public API surface must stay centered on `common.compress`; duplicate codec implementations in consumers are technical debt, not a supported architecture.
- The checked APIs are no longer optional documentation ideas. They already exist in source and should now become the normative encode path for unsupported option combinations, dictionary metadata validation, and block-mode enforcement.
- `block_mode` handling must move from "subset rejection because not implemented yet" to strict standards semantics:
  - `lz4` supports `block` and `frame`.
  - `zstd` requires `frame`.
  - `lzma2` requires `frame` via XZ container emission and decode.
- `dictionary_id` is necessary to represent interoperable framed dictionary handling for Zstd. `dictionary_bytes` alone cannot express the framed dictionary metadata that peer implementations expect.

## Concrete gaps between current local code and the full target

- LZ4 needs completion and verification as a full implementation, not merely the easiest finished tranche:
  - raw block support must remain.
  - frame encode/decode must fully cover block checksums, content checksum, content size, multi-block framing, and flag validation.
  - encode-side match finding should reuse shared LZ77 and byte-kernel helpers where doing so removes duplicate logic.
- Zstd needs completion on both decode and encode:
  - decode must cover normal host-generated frames, frame-header variants, window/content-size validation, dictionary ID parsing, raw/RLE/compressed blocks, repeated FSE tables, compressed Huffman weights, treeless literals, 4-stream literals, checksum verification, and multi-block/multi-frame handling.
  - encode must become a real framed encoder with block splitting, sequence generation, literal compression, FSE/HUF emission, checksum/content-size emission, standards-compliant bounds, and framed dictionary handling using `dictionary_bytes` plus `dictionary_id`.
- XZ/LZMA2 must stop being framed around an uncompressed-only subset:
  - implement real LZMA2 chunk coding and decoding.
  - support `.xz` block/index/footer validation, CRC verification, multi-block streams, concatenated streams, and compressed chunks for the LZMA2-only filter chain.
  - fail non-LZMA2 filter chains explicitly.
- Shared helper extraction is still incomplete:
  - match extension
  - literal copy
  - overlap-safe match copy
  - CRC32
  - XXH32
  - tier-directed scalar/SIMD entrypoints that tests can call directly without host-dependent branching

## Local implementation direction required by the updated requirements

- Treat the scalar helper path as the oracle implementation and layer AVX2/NEON specializations underneath the same pure-Simple helper seam.
- Keep SIMD work implementation-level and immediate. The codebase already has a Simple-visible tier API; the missing work is helper specialization and test coverage, not architecture invention.
- Preserve the façade shape while tightening semantics:
  - `compress_bytes(...)` and `encoder_finish(...)` stay as fail-fast wrappers.
  - checked encode APIs become the required path for unsupported combinations and interoperability-sensitive validation.
- Remove any remaining ambiguity that staged subset behavior is acceptable. The target is full pure-Simple LZ4/Zstd/XZ-LZMA2 completion behind a single shared library.

## Local verification implications

- The executable spec and codec unit coverage must validate full round-trip behavior, corruption handling, typed errors, and duplicate-path parity instead of subset acceptance.
- SIMD verification must test forced scalar/AVX2/NEON helper entrypoints directly and require byte-for-byte parity across helper outputs and codec outputs.
- Final verification must include focused compression coverage, `bin/simple test`, `bin/simple build lint`, `sh scripts/check-core-runtime-smoke.shs bin/simple`, `SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs`, and a `verify` pass result of `STATUS: PASS`.
