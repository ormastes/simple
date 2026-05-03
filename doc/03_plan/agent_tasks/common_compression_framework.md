# Agent Task Breakdown — `common_compression_framework`

Updated on 2026-05-04 to reflect the focused closure that is live in the
current tree.

## Current Status

The active scope for this feature is the landed pure-Simple compression subset
behind `std.common.compress`, not the earlier full-scope completion target.

Focused gates re-verified on 2026-05-04:

- `test/unit/lib/common/lz4_spec.spl` — PASS (20/20)
- `test/unit/lib/common/lzma2_range_coded_spec.spl` — PASS (4/4)
- `test/unit/lib/common/xz_lzma2_spec.spl` — PASS (20/20)
- `test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl` — PASS (7/7)

Documentation aligned in the same pass:

- `doc/02_requirements/feature/common_compression_framework.md`
- `doc/02_requirements/nfr/common_compression_framework.md`
- `doc/09_report/verify_common_compression_framework.md`

## Live Supported Subset

- LZ4 block/frame encode and decode through the shared facade
- XZ/LZMA2 encode and decode for the verified host-interoperable subset
- LZMA range-coded decode coverage at LCLPPB `3/0/2`
- Focused Zstd framed behavior already exercised by the current specs
- Zstd Huffman-weight encode/decode lane covered by the dedicated focused spec

## Explicitly Deferred / Unsupported

- Broad Zstd feature completion beyond the focused green lanes
- General dictionary-backed encode support across all codecs
- Zstd encode levels outside the currently supported subset
- LZMA2 parameter tuples outside LCLPPB `3/0/2`
- Any claim that `zstd_frame_variants_spec.spl` is currently a stable green
  gate

These combinations must continue to fail closed with typed
`CompressionError.UnsupportedFeature` where applicable.

## Follow-up Work

1. Re-stabilize and re-verify the broader Zstd lanes before widening any
   support claims.
2. Expand requirements only after code and executable specs prove the wider
   behavior.
3. Keep the kernel Zstd loader as a thin adapter over `std.common.compress`.
