# Protobuf Wire Bounds Guard Specification

> Tests covering Protobuf wire bounds guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protobuf Wire Bounds Guard Specification

## Scenarios

### Protobuf wire bounds guards

#### rejects negative varint offsets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative varint offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative varint offsets")
val bytes = [0x08, 0x01]
val result = pb_read_varint(bytes, -1)
assert_equal(result.0, 0)
assert_equal(result.1, -1)
```

</details>

#### rejects invalid varint byte values

- rejects invalid varint byte values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid varint byte values")
val high_result = pb_read_varint([300], 0)
val low_result = pb_read_varint([-1], 0)
assert_equal(high_result.0, 0)
assert_equal(high_result.1, 0)
assert_equal(low_result.0, 0)
assert_equal(low_result.1, 0)
```

</details>

#### rejects overlong varint encodings

- rejects overlong varint encodings


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlong varint encodings")
val zero_result = pb_read_varint([128, 0], 0)
val small_result = pb_read_varint([129, 0], 0)
assert_equal(zero_result.0, 0)
assert_equal(zero_result.1, 0)
assert_equal(small_result.0, 0)
assert_equal(small_result.1, 0)
```

</details>

#### rejects overflowing terminal varint bytes

- rejects overflowing terminal varint bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overflowing terminal varint bytes")
val result = pb_read_varint([255, 255, 255, 255, 255, 255, 255, 255, 255, 127], 0)
assert_equal(result.0, 0)
assert_equal(result.1, 0)
```

</details>

#### rejects negative field offsets

- rejects negative field offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative field offsets")
val bytes = [0x08, 0x01]
val result = pb_read_field(bytes, -1)
assert_equal(result.0, 0)
assert_equal(result.3, -1)
```

</details>

#### rejects fields with invalid tag bytes

- rejects fields with invalid tag bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fields with invalid tag bytes")
val result = pb_read_field([300, 0], 0)
assert_equal(result.0, 0)
assert_equal(result.3, 0)
```

</details>

#### rejects fields with zero field numbers

- rejects fields with zero field numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fields with zero field numbers")
val result = pb_read_field([0, 1], 0)
assert_equal(result.0, 0)
assert_equal(result.3, 0)
```

</details>

#### rejects fields with oversized field numbers

- rejects fields with oversized field numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fields with oversized field numbers")
val result = pb_read_field([128, 128, 128, 128, 16, 1], 0)
assert_equal(result.0, 0)
assert_equal(result.3, 0)
```

</details>

#### rejects fixed32 fields with invalid payload bytes

- rejects fixed32 fields with invalid payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fixed32 fields with invalid payload bytes")
val result = pb_read_field([13, 1, 300, 2, 3], 0)
assert_equal(result.0, 0)
assert_equal(result.3, 0)
```

</details>

#### rejects length-delimited fields with invalid payload bytes

- rejects length-delimited fields with invalid payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects length-delimited fields with invalid payload bytes")
val result = pb_read_field([10, 2, 1, 300], 0)
assert_equal(result.0, 0)
assert_equal(result.3, 0)
```

</details>

#### rejects negative byte slices

- rejects negative byte slices


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative byte slices")
val bytes = [1, 2, 3]
val result = pb_bytes_slice(bytes, -1, 2)
assert_equal(result.len(), 0)
```

</details>

#### rejects truncated byte slices

- rejects truncated byte slices


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated byte slices")
val bytes = [1, 2, 3]
val result = pb_bytes_slice(bytes, 2, 2)
assert_equal(result.len(), 0)
```

</details>

#### rejects invalid byte values in slices

- rejects invalid byte values in slices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid byte values in slices")
val high_result = pb_bytes_slice([1, 300], 0, 2)
val low_result = pb_bytes_slice([-1], 0, 1)
assert_equal(high_result.len(), 0)
assert_equal(low_result.len(), 0)
```

</details>

#### keeps valid byte slices

- keeps valid byte slices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid byte slices")
val result = pb_bytes_slice([1, 2, 3], 1, 2)
assert_equal(result.len(), 2)
assert_equal(result[0], 2)
assert_equal(result[1], 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Protobuf wire bounds guards.
- Protobuf wire bounds guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `55996ca4d3583285d1a4ec394bfc43dbd14a1fc9d03abe1dbb190668de673a8f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55996ca4d3583285d1a4ec394bfc43dbd14a1fc9d03abe1dbb190668de673a8f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55996ca4d3583285d1a4ec394bfc43dbd14a1fc9d03abe1dbb190668de673a8f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative varint offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid varint byte values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_wire_bounds_guard_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overlong varint encodings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
