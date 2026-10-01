# Zstd Literals Huf Bounds Specification

> Tests covering Zstd Huffman literal stream bounds validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Literals Huf Bounds Specification

## Scenarios

### Zstd Huffman literal stream bounds validation

#### rejects negative literal section offsets before indexing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative literal section offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative literal section offsets before indexing")
expect_section_truncated(zstd_parse_literals_section_for_test([0x00u8], -1, 1, nil), "literals header")
```

</details>

#### rejects literal section ends beyond the backing input before payload reads

- rejects literal section ends beyond the backing input before payload reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects literal section ends beyond the backing input before payload reads")
expect_section_truncated(zstd_parse_literals_section_for_test([0x08u8], 0, 4, nil), "literals header")
```

</details>

#### rejects negative FSE weight offsets before indexing

- rejects negative FSE weight offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative FSE weight offsets before indexing")
expect_weight_truncated(zstd_parse_fse_huffman_weights([0x01u8], -1, 1), "tree header")
```

</details>

#### rejects FSE weight payload ends beyond the backing input before indexing

- rejects FSE weight payload ends beyond the backing input before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects FSE weight payload ends beyond the backing input before indexing")
expect_weight_truncated(zstd_parse_fse_huffman_weights([0x01u8], 0, 2), "tree header")
```

</details>

#### rejects negative direct weight offsets before indexing

- rejects negative direct weight offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative direct weight offsets before indexing")
expect_weight_truncated(zstd_parse_direct_huffman_weights_for_test([0x80u8], -1, 1), "tree header")
```

</details>

#### rejects direct weight payload ends beyond the backing input before indexing

- rejects direct weight payload ends beyond the backing input before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects direct weight payload ends beyond the backing input before indexing")
expect_weight_truncated(zstd_parse_direct_huffman_weights_for_test([0x80u8], 0, 2), "tree header")
```

</details>

#### rejects negative regenerated sizes before decoding

- rejects negative regenerated sizes before decoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative regenerated sizes before decoding")
val table = ZstdHufTableState(
    table_bits: 1,
    table: [
        ZstdHufDecodeEntry(symbol: 0, bits: 1),
        ZstdHufDecodeEntry(symbol: 1, bits: 1)
    ]
)
expect_corrupt(zstd_huf_decode_stream_for_test([0x02u8], 0, 1, -1, table), "regenerated size")
```

</details>

#### rejects negative 4-stream regenerated sizes before jump-table math

- rejects negative 4-stream regenerated sizes before jump-table math


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative 4-stream regenerated sizes before jump-table math")
val table = ZstdHufTableState(
    table_bits: 1,
    table: [
        ZstdHufDecodeEntry(symbol: 0, bits: 1),
        ZstdHufDecodeEntry(symbol: 1, bits: 1)
    ]
)
expect_corrupt(_zstd_decode_huffman_4streams([0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8], 0, 6, -1, table), "regenerated size")
```

</details>

#### rejects 4-stream ends beyond the backing input before jump-table math

- rejects 4-stream ends beyond the backing input before jump-table math


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects 4-stream ends beyond the backing input before jump-table math")
val table = ZstdHufTableState(
    table_bits: 1,
    table: [
        ZstdHufDecodeEntry(symbol: 0, bits: 1),
        ZstdHufDecodeEntry(symbol: 1, bits: 1)
    ]
)
expect_corrupt(_zstd_decode_huffman_4streams([0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8], 0, 7, 1, table), "4-stream range")
```

</details>

#### rejects malformed Huffman table widths before peeking

- rejects malformed Huffman table widths before peeking


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed Huffman table widths before peeking")
val table = ZstdHufTableState(
    table_bits: 12,
    table: [ZstdHufDecodeEntry(symbol: 0, bits: 1)]
)
expect_corrupt(zstd_huf_decode_stream_for_test([0x02u8], 0, 1, 1, table), "table width")
```

</details>

#### rejects too-short Huffman decode tables before indexing

- rejects too-short Huffman decode tables before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects too-short Huffman decode tables before indexing")
val table = ZstdHufTableState(
    table_bits: 1,
    table: [ZstdHufDecodeEntry(symbol: 0, bits: 1)]
)
expect_corrupt(zstd_huf_decode_stream_for_test([0x03u8], 0, 1, 1, table), "table size")
```

</details>

#### rejects entries that consume more bits than the table width

- rejects entries that consume more bits than the table width


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects entries that consume more bits than the table width")
val table = ZstdHufTableState(
    table_bits: 1,
    table: [
        ZstdHufDecodeEntry(symbol: 0, bits: 1),
        ZstdHufDecodeEntry(symbol: 1, bits: 2)
    ]
)
expect_corrupt(zstd_huf_decode_stream_for_test([0x03u8], 0, 1, 1, table), "decode entry")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Zstd Huffman literal stream bounds validation.
- Zstd Huffman literal stream bounds validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `30bc5e3a8eeeda33426a8d1949e8d4bb0bb494dd0524317f1d6e69f4c4e58ed2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `30bc5e3a8eeeda33426a8d1949e8d4bb0bb494dd0524317f1d6e69f4c4e58ed2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `30bc5e3a8eeeda33426a8d1949e8d4bb0bb494dd0524317f1d6e69f4c4e58ed2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative literal section offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects literal section ends beyond the backing input before payload reads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_literals_huf_bounds_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative FSE weight offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
