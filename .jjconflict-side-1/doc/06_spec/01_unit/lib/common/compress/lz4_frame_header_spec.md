# Lz4 Frame Header Specification

> Tests covering LZ4 frame header validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lz4 Frame Header Specification

## Scenarios

### LZ4 frame header validation

#### rejects reserved frame descriptor flags

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects reserved frame descriptor flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reserved frame descriptor flags")
val flg: u8 = 0x62u8
val bd: u8 = 0x40u8
var frame: [u8] = [
    0x04u8, 0x22u8, 0x4Du8, 0x18u8,
    flg, bd, _header_checksum(flg, bd),
    0x00u8, 0x00u8, 0x00u8, 0x00u8
]
val decoded = lz4_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("descriptor flags"))
    _:
        check(false)
```

</details>

#### rejects invalid block descriptor codes

- rejects invalid block descriptor codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid block descriptor codes")
val flg: u8 = 0x60u8
val bd: u8 = 0x00u8
var frame: [u8] = [
    0x04u8, 0x22u8, 0x4Du8, 0x18u8,
    flg, bd, _header_checksum(flg, bd),
    0x00u8, 0x00u8, 0x00u8, 0x00u8
]
val decoded = lz4_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("block descriptor"))
    _:
        check(false)
```

</details>

#### rejects dictionary id frames as unsupported

- rejects dictionary id frames as unsupported


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dictionary id frames as unsupported")
val flg: u8 = 0x61u8
val bd: u8 = 0x40u8
var frame: [u8] = [
    0x04u8, 0x22u8, 0x4Du8, 0x18u8,
    flg, bd, _header_checksum(flg, bd),
    0x00u8, 0x00u8, 0x00u8, 0x00u8
]
val decoded = lz4_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.UnsupportedFeature(message):
        check(message.contains("dictionary id"))
    _:
        check(false)
```

</details>

#### rejects blocks larger than the descriptor maximum

- rejects blocks larger than the descriptor maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects blocks larger than the descriptor maximum")
val flg: u8 = 0x60u8
val bd: u8 = 0x40u8
var frame: [u8] = [
    0x04u8, 0x22u8, 0x4Du8, 0x18u8,
    flg, bd, _header_checksum(flg, bd),
    0x01u8, 0x00u8, 0x01u8, 0x00u8
]
val decoded = lz4_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("block size"))
    _:
        check(false)
```

</details>

#### rejects negative signed content sizes

- rejects negative signed content sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative signed content sizes")
val flg: u8 = 0x68u8
val bd: u8 = 0x40u8
var content_size: [u8] = [
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x80u8
]
var frame: [u8] = [
    0x04u8, 0x22u8, 0x4Du8, 0x18u8,
    flg, bd,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x80u8,
    _content_size_header_checksum(flg, bd, content_size),
    0x00u8, 0x00u8, 0x00u8, 0x00u8
]
val decoded = lz4_decompress_frame(frame)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("content size"))
    _:
        check(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/lz4_frame_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LZ4 frame header validation.
- LZ4 frame header validation

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

- Canonical SPipe generation for source `2ebcf5126d76fd1ba93429e83465a717ee7580e8f3ef33181e2f6d58c964fe00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ebcf5126d76fd1ba93429e83465a717ee7580e8f3ef33181e2f6d58c964fe00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ebcf5126d76fd1ba93429e83465a717ee7580e8f3ef33181e2f6d58c964fe00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/lz4_frame_header_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/lz4_frame_header_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/lz4_frame_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/lz4_frame_header_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/lz4_frame_header_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects reserved frame descriptor flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lz4_frame_header_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid block descriptor codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lz4_frame_header_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects dictionary id frames as unsupported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
