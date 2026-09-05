# Lzma2 Xz Read Bounds Specification

> Tests covering XZ little-endian reader bounds validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lzma2 Xz Read Bounds Specification

## Scenarios

### XZ little-endian reader bounds validation

#### rejects negative u32 offsets before indexing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative u32 offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative u32 offsets before indexing")
expect_truncated_u32(_xz_read_u32_le([0x01u8, 0x02u8, 0x03u8, 0x04u8], -1), "need 4 bytes")
```

</details>

#### rejects negative u64 offsets before indexing

- rejects negative u64 offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative u64 offsets before indexing")
expect_truncated_u64(_xz_read_u64_le([
    0x01u8, 0x02u8, 0x03u8, 0x04u8,
    0x05u8, 0x06u8, 0x07u8, 0x08u8
], -1), "need 8 bytes")
```

</details>

#### rejects negative LZMA range decoder offsets before indexing

- rejects negative LZMA range decoder offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative LZMA range decoder offsets before indexing")
expect_truncated_unit(_validate_lzma_range_decoder_init([
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8
], -1), "range decoder init")
```

</details>

#### rejects negative XZ stream offsets before indexing

- rejects negative XZ stream offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative XZ stream offsets before indexing")
expect_truncated_stream(_decompress_xz_stream([
    0xFDu8, 0x37u8, 0x7Au8, 0x58u8, 0x5Au8, 0x00u8,
    0x00u8, 0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8
], -1, CompressionSimdTier.scalar), "xz stream")
```

</details>

#### rejects negative XZ index offsets before indexing

- rejects negative XZ index offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative XZ index offsets before indexing")
expect_truncated_i64(_parse_xz_index([0x00u8, 0x00u8, 0x00u8, 0x00u8], -1, [], CompressionSimdTier.scalar), "xz index")
```

</details>

#### rejects negative XZ block header offsets before indexing

- rejects negative XZ block header offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative XZ block header offsets before indexing")
expect_truncated_block_header(_parse_block_header([0x01u8, 0x00u8, 0x00u8, 0x00u8], -1, CompressionSimdTier.scalar), "xz block header")
```

</details>

#### rejects negative XZ alignment offsets before indexing

- rejects negative XZ alignment offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative XZ alignment offsets before indexing")
expect_truncated_i64(_consume_alignment_zeroes([0x00u8, 0x00u8], 0, -1, "xz alignment"), "xz alignment")
```

</details>

#### rejects XZ alignment ranges that move before the span start

- rejects XZ alignment ranges that move before the span start


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects XZ alignment ranges that move before the span start")
expect_truncated_i64(_consume_alignment_zeroes([0x00u8, 0x00u8], 2, 1, "xz alignment"), "xz alignment")
```

</details>

#### rejects negative XZ VLI offsets before indexing

- rejects negative XZ VLI offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative XZ VLI offsets before indexing")
expect_truncated_vli(_vli_decode([0x00u8], -1), "xz vli")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering XZ little-endian reader bounds validation.
- XZ little-endian reader bounds validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `fd966cb6529a64d9947f902db89db1e38c5692eeb3b00ff92d5cc077d388493d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd966cb6529a64d9947f902db89db1e38c5692eeb3b00ff92d5cc077d388493d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd966cb6529a64d9947f902db89db1e38c5692eeb3b00ff92d5cc077d388493d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative u32 offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative u64 offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lzma2_xz_read_bounds_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative LZMA range decoder offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
