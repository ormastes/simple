# Protobuf Bounds Guard Specification

> Tests covering protobuf decode bounds guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protobuf Bounds Guard Specification

## Scenarios

### protobuf decode bounds guards

#### rejects overlong varint encodings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects overlong varint encodings


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlong varint encodings")
val zero_result = pb_decode_varint([0x80, 0x00], 0)
val small_result = pb_decode_varint([0x81, 0x00], 0)
assert_equal(zero_result[0], 0)
assert_equal(zero_result[1], 0)
assert_equal(small_result[0], 0)
assert_equal(small_result[1], 0)
```

</details>

#### rejects zero field numbers

- rejects zero field numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero field numbers")
val r = pb_decode_field([0, 1], 0)
assert_equal(r[0], 0)
assert_equal(r[1], 0)
assert_equal(r[2], 0)
assert_equal(r[3], 0)
```

</details>

#### rejects oversized field numbers

- rejects oversized field numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized field numbers")
val r = pb_decode_field([128, 128, 128, 128, 16, 1], 0)
assert_equal(r[0], 0)
assert_equal(r[1], 0)
assert_equal(r[2], 0)
assert_equal(r[3], 0)
```

</details>

#### rejects unsupported wire types

- rejects unsupported wire types


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported wire types")
val r = pb_decode_field([0x0B], 0)
assert_equal(r[0], 0)
assert_equal(r[1], 0)
assert_equal(r[2], 0)
assert_equal(r[3], 0)
```

</details>

#### rejects truncated varint field payloads

- rejects truncated varint field payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated varint field payloads")
val r = pb_decode_field([0x08, 0x80], 0)
assert_equal(r[0], 1)
assert_equal(r[1], 0)
assert_equal(r[2], 0)
assert_equal(r[3], 1)
```

</details>

#### rejects truncated fixed32 fields without zero filling

- rejects truncated fixed32 fields without zero filling


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated fixed32 fields without zero filling")
val tag = pb_encode_tag(3, 5)
val r = pb_decode_field(tag, 0)
assert_equal(r[0], 3)
assert_equal(r[1], 5)
assert_equal(r[2], 0)
assert_equal(r[3], 1)
```

</details>

#### keeps valid fixed32 fields

- keeps valid fixed32 fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid fixed32 fields")
var data: [u8] = []
val tag = pb_encode_tag(3, 5)
val body = pb_encode_fixed32(300)
var i = 0
while i < tag.len():
    data.push(tag[i])
    i = i + 1
i = 0
while i < body.len():
    data.push(body[i])
    i = i + 1
val r = pb_decode_field(data, 0)
assert_equal(r[0], 3)
assert_equal(r[1], 5)
assert_equal(r[2], 300)
assert_equal(r[3], 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering protobuf decode bounds guards.
- protobuf decode bounds guards

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

- Canonical SPipe generation for source `b21b1797a212efcfbc336d9513e75fe9636b175b65ea069a829f9fd7c171204f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b21b1797a212efcfbc336d9513e75fe9636b175b65ea069a829f9fd7c171204f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b21b1797a212efcfbc336d9513e75fe9636b175b65ea069a829f9fd7c171204f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overlong varint encodings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects zero field numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_bounds_guard_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects oversized field numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
