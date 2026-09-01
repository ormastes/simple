# Cbor String Payload Byte Guard Specification

> Tests covering CBOR string payload byte guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor String Payload Byte Guard Specification

## Scenarios

### CBOR string payload byte guard

#### rejects invalid definite byte string payload bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects invalid definite byte string payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid definite byte string payload bytes")
val negative_result = cbor_decode_bytes([0x41, -1], 0)
val high_result = cbor_decode_bytes([0x41, 300], 0)
assert_equal(negative_result.1, 0)
assert_equal(high_result.1, 0)
```

</details>

#### rejects invalid definite text string payload bytes

- rejects invalid definite text string payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid definite text string payload bytes")
val negative_result = cbor_decode_text([0x61, -1], 0)
val high_result = cbor_decode_text([0x61, 300], 0)
assert_equal(negative_result.1, 0)
assert_equal(high_result.1, 0)
```

</details>

#### rejects invalid payload bytes inside indefinite string chunks

- rejects invalid payload bytes inside indefinite string chunks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid payload bytes inside indefinite string chunks")
val byte_result = cbor_decode_bytes([0x5F, 0x41, 300, 0xFF], 0)
val text_result = cbor_decode_text([0x7F, 0x61, -1, 0xFF], 0)
assert_equal(byte_result.1, 0)
assert_equal(text_result.1, 0)
```

</details>

#### keeps valid byte and text payloads working

- keeps valid byte and text payloads working


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid byte and text payloads working")
val byte_result = cbor_decode_bytes([0x41, 255], 0)
val text_result = cbor_decode_text([0x61, 65], 0)
assert_equal(byte_result.0.len(), 1)
assert_equal(byte_result.0[0], 255)
assert_equal(byte_result.1, 2)
assert_equal(text_result.0, "A")
assert_equal(text_result.1, 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_string_payload_byte_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CBOR string payload byte guard.
- CBOR string payload byte guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `f446267ee0333e1265cc850b6c51bc3aa31b5032c01cc407f6c632c7e21484ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f446267ee0333e1265cc850b6c51bc3aa31b5032c01cc407f6c632c7e21484ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f446267ee0333e1265cc850b6c51bc3aa31b5032c01cc407f6c632c7e21484ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/cbor_string_payload_byte_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/cbor_string_payload_byte_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/cbor_string_payload_byte_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/cbor_string_payload_byte_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/cbor_string_payload_byte_guard_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid definite byte string payload bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_string_payload_byte_guard_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid definite text string payload bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_string_payload_byte_guard_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid payload bytes inside indefinite string chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
