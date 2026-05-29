=== Verification Report: common_compression_framework ===

[PASS] doc/04_architecture/common_compression_framework.md:1 — architecture
describes the currently landed compression subset rather than the older
full-scope target.
[PASS] doc/05_design/common_compression_framework.md:1 — design documents the
live facade restrictions, supported checksums, and explicit unsupported codec
paths.
[PASS] doc/02_requirements/feature/common_compression_framework.md:1 — feature
requirements now match the live supported subset and no longer overclaim
full-scope codec behavior.
[PASS] doc/02_requirements/nfr/common_compression_framework.md:1 — NFR gates
now match the focused executable verification surface.
[PASS] test/unit/lib/common/compress_framework_spec.spl:1 — focused facade
tests align with the current checked/fail-fast API surface.
[PASS] test/unit/lib/common/lz4_spec.spl:1 — focused LZ4 tests cover
block/frame round-trip behavior, corruption typing, and forced-tier parity.
[PASS] test/unit/lib/common/lzma2_range_coded_spec.spl:1 — pure-Simple LZMA
range decode round-trips host `xz -z --check=crc32` outputs across the focused
fixture set.
[PASS] test/unit/lib/common/xz_lzma2_spec.spl:1 — focused XZ/LZMA2 tests cover
emitted-stream interoperability, concatenated streams, and host-`xz` fixtures
for the landed subset.
[PASS] test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl:1 — the
focused Zstd Huffman-weight encode/decode lane is green in the current tree.
[PASS] src/os/kernel/loader/zstd_decompress.spl:1 — the kernel loader remains
a thin adapter over `std.common.compress`.

[WARN] src/lib/common/compress/mod.spl:1 — the public option shape is broader
than the currently implemented subset; unsupported dictionaries, unsupported
Zstd levels, and unsupported LZMA2 parameter combinations still fail closed by
design.
[WARN] test/unit/lib/common/zstd_frame_variants_spec.spl:1 — this broader Zstd
lane is not part of the focused closure gate, and prior fresh runs in this
session family reported stalls after the first four passing cases. Do not cite
it as a green gate until it is re-stabilized.
[WARN] doc/01_research/local/common_compression_framework.md:1 — the research
artifact still captures the original full-completion intent and should be read
as background, not as current support documentation.

STATUS: PASS (focused subset) / WARN (broader deferred lanes)

Focused gates re-verified on 2026-05-04:
- `bin/simple test test/unit/lib/common/lz4_spec.spl` → Passed: 20, Failed: 0
- `bin/simple test test/unit/lib/common/lzma2_range_coded_spec.spl` →
  Passed: 4, Failed: 0
- `bin/simple test test/unit/lib/common/xz_lzma2_spec.spl` →
  Passed: 20, Failed: 0
- `bin/simple test test/unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl`
  → Passed: 7, Failed: 0

This report intentionally reflects the live supported subset. It does not claim
full Zstd feature closure, full LZMA2 parameter-space closure, or broad
dictionary support beyond what the checked APIs already reject explicitly.
