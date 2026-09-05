# Cbor Uint Payload Byte Guard Specification

> Tests covering CBOR uint payload byte guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Uint Payload Byte Guard Specification

## Scenarios

### CBOR uint payload byte guard

#### rejects invalid uint8 payload bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects invalid uint8 payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid uint8 payload bytes")
val negative_result = cbor_decode_unsigned([0x18, -1], 0)
val high_result = cbor_decode_unsigned([0x18, 300], 0)
assert_equal(negative_result.1, 0)
assert_equal(high_result.1, 0)
```

</details>

#### rejects invalid multi-byte integer payload bytes

- rejects invalid multi-byte integer payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid multi-byte integer payload bytes")
val uint16_result = cbor_decode_unsigned([0x19, 1, 300], 0)
val uint32_result = cbor_decode_unsigned([0x1A, 0, -1, 0, 1], 0)
assert_equal(uint16_result.1, 0)
assert_equal(uint32_result.1, 0)
```

</details>

#### rejects invalid payload bytes when decoding lengths and simple values

- rejects invalid payload bytes when decoding lengths and simple values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid payload bytes when decoding lengths and simple values")
val text_result = cbor_decode_text([0x78, 300, 65], 0)
val array_header = cbor_decode_array_header([0x98, -1], 0)
val simple_result = cbor_decode_simple_value([0xF8, 300], 0)
assert_equal(text_result.1, 0)
assert_equal(array_header.2, 0)
assert_equal(simple_result.1, 0)
```

</details>

#### keeps valid payload bytes working

- keeps valid payload bytes working


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid payload bytes working")
val unsigned_result = cbor_decode_unsigned([0x18, 24], 0)
val text_result = cbor_decode_text([0x78, 1, 65], 0)
val simple_result = cbor_decode_simple_value([0xF8, 16], 0)
assert_equal(unsigned_result.0, 24)
assert_equal(unsigned_result.1, 2)
assert_equal(text_result.0, "A")
assert_equal(text_result.1, 3)
assert_equal(simple_result.0, 16)
assert_equal(simple_result.1, 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CBOR uint payload byte guard.
- CBOR uint payload byte guard

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

- Canonical SPipe generation for source `c07a67be1ee02224e3f41b492706ac7150a2f68d8443fbca3e7bb4cd1665a523`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c07a67be1ee02224e3f41b492706ac7150a2f68d8443fbca3e7bb4cd1665a523`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c07a67be1ee02224e3f41b492706ac7150a2f68d8443fbca3e7bb4cd1665a523`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid uint8 payload bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid multi-byte integer payload bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_uint_payload_byte_guard_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid payload bytes when decoding lengths and simple values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
