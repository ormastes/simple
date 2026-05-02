=== Verification Report: common_compression_framework ===

[PASS] doc/04_architecture/common_compression_framework.md:1 — architecture now describes the currently landed compression subset instead of the original full-scope target.
[PASS] doc/05_design/common_compression_framework.md:1 — design now documents the actual facade restrictions, supported checksums, and known unsupported codec paths.
[PASS] test/unit/lib/common/compress_framework_spec.spl:1 — focused facade tests still align with the current checked/fail-fast API surface.
[PASS] test/unit/lib/common/lz4_spec.spl:1 — focused LZ4 tests cover block/frame round-trip behavior, corruption typing, and forced-tier parity.
[WARN] test/unit/lib/common/zstd_frame_variants_spec.spl:1 — the spec still documents the current framed-subset expectations, but repeated fresh runs in this session stalled after the first four passing cases instead of completing, so this lane cannot claim a clean current PASS for it.
[PASS] test/unit/lib/common/xz_lzma2_spec.spl:1 — focused XZ/LZMA2 tests cover emitted-stream interoperability, concatenated streams, and host-xz-generated range-coded chunk decode (LCLPPB=3/0/2).
[PASS] test/unit/lib/common/lzma2_range_coded_spec.spl:1 — pure-Simple LZMA range decoder round-trips host `xz -z --check=crc32` outputs across literal-only, slot-≥14 distance, and rep-heavy payloads.
[PASS] src/os/kernel/loader/zstd_decompress.spl:1 — the kernel loader remains a thin adapter over `std.common.compress`.

[FAIL] src/lib/common/compress/mod.spl:49 — the facade still rejects Zstd encode levels other than `3`, dictionaries for all codecs, and `checksum=false` for XZ/LZMA2 encode, so docs cannot claim wider option support.
[FAIL] src/lib/common/compress/zstd.spl:324 — compressed-block decode still rejects non-RLE sequence tables.
[FAIL] src/lib/common/compress/zstd.spl:704 — FSE-compressed Huffman-weight decode is wired and dispatched (header_byte<128 -> `_zstd_parse_fse_compressed_weights`), and `test/unit/lib/common/zstd_fse_weights_spec.spl` (5 cases, PASS 2026-05-01) pins the typed-error surface (truncated bitstream, out-of-range accuracy_log, zero compressed_size, empty input) -- but the decoder mis-decodes every real-world host-zstd FSE Huffman tree (Kraft completion fails on 5/5 fixtures); see `doc/08_tracking/bug/bug_zstd_fse_huffman_weight_kraft_2026-05-01.md`.
[FAIL] src/lib/common/compress/zstd.spl:1265 — dictionary-backed Zstd frames remain explicitly unsupported on decode.
[WARN] src/lib/common/compress/lzma2.spl:330 — Status: LANDED 2026-05-01 (LCLPPB=3/0/2 only). Pure-Simple LZMA range decoder + LZMA2 chunk decoder now interoperate with host `xz -z --check=crc32` output at the default LCLPPB tuple (props 0x5D); other LCLPPB values are rejected explicitly via `UnsupportedFeature("LZMA2 LCLPPB other than 3/0/2")`. Full-LCLPPB closure tracked in `doc/08_tracking/feature_request/lzma2_full_lclppb_2026-05-01.md`.
[FAIL] doc/02_requirements/feature/common_compression_framework.md:30 — REQ-030 still overstates forced-tier parity closure relative to the focused verified surface.
[FAIL] doc/02_requirements/nfr/common_compression_framework.md:11 — NFR-011 still overstates end-to-end verification closure; repository `verify` cannot honestly report PASS for the original full-scope claims.

[WARN] src/lib/common/compress/zstd.spl:1 — the Zstd implementation remains large and multi-responsibility, which raises maintenance risk even though this lane did not modify code.
[WARN] doc/01_research/local/common_compression_framework.md:1 — the research artifacts still describe the original full completion target; that may be fine as intent, but they should not be read as current-state support documentation.

STATUS: FAIL (6 failures, 4 warnings)
