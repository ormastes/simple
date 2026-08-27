# Zstd Sequence Header Specification

> Tests covering zstd sequence header gates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Header Specification

## Scenarios

### zstd sequence header gates

#### rejects repeated fse tables explicitly after parsing the modes byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects repeated fse tables explicitly after parsing the modes byte
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects repeated fse tables explicitly after parsing the modes byte")
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x01u8, 0xC0u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "repeated fse tables")
```

</details>

#### rejects sequence decoding tables after parsing predefined modes

- rejects sequence decoding tables after parsing predefined modes
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects sequence decoding tables after parsing predefined modes")
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x01u8, 0x00u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "sequence decoding tables")
```

</details>

#### validates reserved bits in the sequence modes byte

- validates reserved bits in the sequence modes byte
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates reserved bits in the sequence modes byte")
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x01u8, 0x01u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "reserved bits")
```

</details>

#### parses the two-byte sequence count encoding before gating

- parses the two-byte sequence count encoding before gating
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the two-byte sequence count encoding before gating")
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0x80u8, 0x82u8, 0x00u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "sequence decoding tables")
```

</details>

#### parses the three-byte sequence count encoding before gating

- parses the three-byte sequence count encoding before gating
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the three-byte sequence count encoding before gating")
val frame = _zstd_frame(3, _compressed_block(_raw_literals_prefix() + [0xFFu8, 0x01u8, 0x00u8, 0x00u8]))
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "sequence decoding tables")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_sequence_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd sequence header gates.
- zstd sequence header gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `5edb05402998a16a14e57adcec3ea04b4eefba78a79cb8576f4a5922c31c2df3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5edb05402998a16a14e57adcec3ea04b4eefba78a79cb8576f4a5922c31c2df3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5edb05402998a16a14e57adcec3ea04b4eefba78a79cb8576f4a5922c31c2df3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/zstd_sequence_header_spec.spl
mirror: doc/06_spec/01_unit/lib/common/zstd_sequence_header_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/zstd_sequence_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/zstd_sequence_header_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/zstd_sequence_header_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects repeated fse tables explicitly after parsing the modes byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_sequence_header_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects sequence decoding tables after parsing predefined modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_sequence_header_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates reserved bits in the sequence modes byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
