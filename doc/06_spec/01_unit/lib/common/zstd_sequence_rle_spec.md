# Zstd Sequence Rle Specification

> Tests covering zstd rle sequence execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Rle Specification

## Scenarios

### zstd rle sequence execution

#### decodes a one-sequence block with a normal offset

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes a one-sequence block with a normal offset
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a one-sequence block with a normal offset")
val frame = _zstd_frame(6, _compressed_block(true, [
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8,
    0x54u8,
    0x03u8, 0x02u8, 0x00u8,
    0x06u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### supports overlap-safe matches for offset one

- supports overlap-safe matches for offset one
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports overlap-safe matches for offset one")
val frame = _zstd_frame(6, _compressed_block(true, [
    0x08u8,
    0x61u8,
    0x01u8,
    0x54u8,
    0x01u8, 0x02u8, 0x02u8,
    0x04u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### supports rep1 offsets during rle sequence execution

- supports rep1 offsets during rle sequence execution
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports rep1 offsets during rle sequence execution")
val frame = _zstd_frame(4, _compressed_block(true, [
    0x08u8,
    0x61u8,
    0x01u8,
    0x54u8,
    0x01u8, 0x00u8, 0x00u8,
    0x01u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### supports zero-literal shifted repeat offsets

- supports zero-literal shifted repeat offsets
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x61u8, 0x62u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports zero-literal shifted repeat offsets")
val frame = _zstd_frame(7, _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8]) + _compressed_block(true, [
    0x00u8,
    0x01u8,
    0x54u8,
    0x00u8, 0x00u8, 0x00u8,
    0x01u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### carries repeat-offset history across compressed blocks

- carries repeat-offset history across compressed blocks
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8, 0x63u8, 0x63u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries repeat-offset history across compressed blocks")
val frame = _zstd_frame(9, _compressed_block(false, [
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8,
    0x54u8,
    0x03u8, 0x02u8, 0x00u8,
    0x06u8
]) + _compressed_block(true, [
    0x00u8,
    0x01u8,
    0x54u8,
    0x00u8, 0x00u8, 0x00u8,
    0x01u8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8, 0x63u8, 0x63u8, 0x63u8])
```

</details>

#### rejects invalid match offsets after literals are copied

- rejects invalid match offsets after literals are copied
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid match offsets after literals are copied")
val frame = _zstd_frame(6, _compressed_block(true, [
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8,
    0x54u8,
    0x03u8, 0x03u8, 0x00u8,
    0x0Eu8
]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "invalid match offset")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_sequence_rle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd rle sequence execution.
- zstd rle sequence execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `a3cc10922f295f199513fb4d8f9831ddeaf96e1927643c3f75edbdef6dee4378`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3cc10922f295f199513fb4d8f9831ddeaf96e1927643c3f75edbdef6dee4378`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3cc10922f295f199513fb4d8f9831ddeaf96e1927643c3f75edbdef6dee4378`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/zstd_sequence_rle_spec.spl
mirror: doc/06_spec/01_unit/lib/common/zstd_sequence_rle_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/zstd_sequence_rle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/zstd_sequence_rle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/zstd_sequence_rle_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes a one-sequence block with a normal offset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_sequence_rle_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports overlap-safe matches for offset one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_sequence_rle_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports rep1 offsets during rle sequence execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
