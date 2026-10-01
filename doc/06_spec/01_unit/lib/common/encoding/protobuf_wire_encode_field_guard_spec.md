# Protobuf Wire Encode Field Guard Specification

> Tests covering Protobuf wire encode field guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protobuf Wire Encode Field Guard Specification

## Scenarios

### Protobuf wire encode field guards

#### rejects zero and negative field numbers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects zero and negative field numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero and negative field numbers")
assert_equal(pb_encode_field(0, pb_wire_varint(), [1]).len(), 0)
assert_equal(pb_encode_field(-1, pb_wire_varint(), [1]).len(), 0)
```

</details>

#### rejects oversized field numbers

- rejects oversized field numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized field numbers")
assert_equal(pb_encode_field(536870912, pb_wire_varint(), [1]).len(), 0)
```

</details>

#### rejects unsupported wire types

- rejects unsupported wire types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported wire types")
assert_equal(pb_encode_field(1, 3, [1]).len(), 0)
assert_equal(pb_encode_field(1, 4, [1]).len(), 0)
assert_equal(pb_encode_field(1, 6, [1]).len(), 0)
```

</details>

#### rejects invalid payload bytes

- rejects invalid payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid payload bytes")
assert_equal(pb_encode_field(1, pb_wire_len(), [300]).len(), 0)
assert_equal(pb_encode_field(1, pb_wire_len(), [-1]).len(), 0)
```

</details>

#### keeps valid raw field encoding

- keeps valid raw field encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid raw field encoding")
val result = pb_encode_field(1, pb_wire_varint(), [1])
assert_equal(result.len(), 2)
assert_equal(result[0], 8)
assert_equal(result[1], 1)
```

</details>

#### applies field number guard through numeric wrappers

- applies field number guard through numeric wrappers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies field number guard through numeric wrappers")
assert_equal(pb_encode_uint32(0, 1).len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Protobuf wire encode field guards.
- Protobuf wire encode field guards

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

- Canonical SPipe generation for source `a8523fb67abf5cabd2af3ae3779b9f77f74f82f51d677a5c97d2632afdaf19f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8523fb67abf5cabd2af3ae3779b9f77f74f82f51d677a5c97d2632afdaf19f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8523fb67abf5cabd2af3ae3779b9f77f74f82f51d677a5c97d2632afdaf19f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects zero and negative field numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects oversized field numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_wire_encode_field_guard_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported wire types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
