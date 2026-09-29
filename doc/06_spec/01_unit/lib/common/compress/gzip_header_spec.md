# Gzip Header Specification

> Tests covering gzip header validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gzip Header Specification

## Scenarios

### gzip header validation

#### rejects reserved header flags

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects reserved header flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reserved header flags")
var data: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x20u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x03u8
]
val parsed = gzip_header_parse(data)
check(parsed == nil)
```

</details>

#### rejects truncated extra field payload

- rejects truncated extra field payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated extra field payload")
var data: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x04u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x03u8,
    0x04u8, 0x00u8,
    0x41u8
]
val parsed = gzip_header_parse(data)
check(parsed == nil)
```

</details>

#### accepts a valid header crc

- accepts a valid header crc


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a valid header crc")
var data: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x02u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x03u8
]
data = _append_header_crc(data)
val parsed = gzip_header_parse(data)
check(parsed != nil)
```

</details>

#### rejects a mismatched header crc

- rejects a mismatched header crc


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a mismatched header crc")
var data: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x02u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x03u8
]
data = _append_header_crc(data)
data[10] = data[10] ^ 0x01u8
val parsed = gzip_header_parse(data)
check(parsed == nil)
```

</details>

#### rejects truncated header crc

- rejects truncated header crc


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated header crc")
var data: [u8] = [
    0x1Fu8, 0x8Bu8, 0x08u8, 0x02u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x03u8,
    0x00u8
]
val parsed = gzip_header_parse(data)
check(parsed == nil)
```

</details>

#### rejects negative footer offsets

- rejects negative footer offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative footer offsets")
var data: [u8] = [
    0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8
]
val parsed = gzip_footer_parse(data, -1)
check(parsed == nil)
```

</details>

#### treats malformed parsed header info as size zero

- treats malformed parsed header info as size zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats malformed parsed header info as size zero")
var header_info: [i64] = [0]
val size = gzip_header_size(header_info)
check(size == 0)
```

</details>

#### rejects malformed parsed footer info

- rejects malformed parsed footer info


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed parsed footer info")
var footer_info: [i64] = [0]
var data: [u8] = []
val valid = gzip_footer_validate(footer_info, data, 0)
check(valid == false)
```

</details>

#### rejects nil footer payloads

- rejects nil footer payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects nil footer payloads")
var footer_info: [i64] = [0, 0]
val valid = gzip_footer_validate(footer_info, nil, 0)
check(valid == false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/gzip_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gzip header validation.
- gzip header validation

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

- Canonical SPipe generation for source `5e29b0fb7c308d6373d29a3626919d414c3e829e806d1dbcebad8e310d31974f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e29b0fb7c308d6373d29a3626919d414c3e829e806d1dbcebad8e310d31974f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e29b0fb7c308d6373d29a3626919d414c3e829e806d1dbcebad8e310d31974f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/gzip_header_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/gzip_header_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/gzip_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/gzip_header_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/gzip_header_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects reserved header flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/gzip_header_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncated extra field payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/gzip_header_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a valid header crc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
