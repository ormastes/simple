# Zstd Frame Header Specification

> Tests covering Zstd frame header validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Frame Header Specification

## Scenarios

### Zstd frame header validation

#### rejects negative content size offsets before indexing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative content size offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative content size offsets before indexing")
val decoded = _zstd_parse_content_size([0x01u8], -1, 0, true)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd frame content size"))
    _:
        check(false)
```

</details>

#### rejects negative dictionary id offsets before indexing

- rejects negative dictionary id offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative dictionary id offsets before indexing")
val decoded = _zstd_parse_dictionary_id([0x01u8], -1, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd dictionary id"))
    _:
        check(false)
```

</details>

#### rejects negative frame header offsets before indexing

- rejects negative frame header offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative frame header offsets before indexing")
var frame: [u8] = [
    0x28u8, 0xB5u8, 0x2Fu8, 0xFDu8,
    0x00u8
]
val decoded = _zstd_parse_frame_header(frame, -1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd frame header"))
    _:
        check(false)
```

</details>

#### rejects the unused frame header bit before later parsing

- rejects the unused frame header bit before later parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the unused frame header bit before later parsing")
var frame: [u8] = [
    0x28u8, 0xB5u8, 0x2Fu8, 0xFDu8,
    0x10u8
]
val decoded = _zstd_parse_frame_header(frame, 0)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("unused frame header bit"))
    _:
        check(false)
```

</details>

#### public decompressor rejects the unused frame header bit

- public decompressor rejects the unused frame header bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public decompressor rejects the unused frame header bit")
var frame: [u8] = [
    0x28u8, 0xB5u8, 0x2Fu8, 0xFDu8,
    0x10u8
]
val decoded = zstd_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("unused frame header bit"))
    _:
        check(false)
```

</details>

#### public decompressor rejects zero-size rle blocks

- public decompressor rejects zero-size rle blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public decompressor rejects zero-size rle blocks")
var frame: [u8] = [
    0x28u8, 0xB5u8, 0x2Fu8, 0xFDu8,
    0x20u8, 0x00u8,
    0x03u8, 0x00u8, 0x00u8,
    0x41u8
]
val decoded = zstd_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("empty rle block"))
    _:
        check(false)
```

</details>

#### public decompressor rejects zero-size compressed blocks

- public decompressor rejects zero-size compressed blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public decompressor rejects zero-size compressed blocks")
var frame: [u8] = [
    0x28u8, 0xB5u8, 0x2Fu8, 0xFDu8,
    0x20u8, 0x00u8,
    0x05u8, 0x00u8, 0x00u8
]
val decoded = zstd_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("empty compressed block"))
    _:
        check(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/zstd_frame_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Zstd frame header validation.
- Zstd frame header validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `d264385230e9f2935999e393d40a81d56ee42dd31d76a2210e989a4499bafe87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d264385230e9f2935999e393d40a81d56ee42dd31d76a2210e989a4499bafe87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d264385230e9f2935999e393d40a81d56ee42dd31d76a2210e989a4499bafe87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/zstd_frame_header_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/zstd_frame_header_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/zstd_frame_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/zstd_frame_header_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/zstd_frame_header_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative content size offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_frame_header_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative dictionary id offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_frame_header_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative frame header offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
