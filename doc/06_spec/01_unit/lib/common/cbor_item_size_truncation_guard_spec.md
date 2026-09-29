# Cbor Item Size Truncation Guard Specification

> Tests covering CBOR item size truncation guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Item Size Truncation Guard Specification

## Scenarios

### CBOR item size truncation guards

#### rejects truncated integer headers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects truncated integer headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated integer headers")
val encoded = [make_initial_byte(major_unsigned_int(), addl_uint16()), 0]
assert_equal(cbor_item_size(encoded, 0), 0)
assert_equal(cbor_validate(encoded), false)
```

</details>

#### rejects truncated byte string payloads

- rejects truncated byte string payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated byte string payloads")
val encoded = [make_initial_byte(major_byte_string(), 2), 0x41]
assert_equal(cbor_item_size(encoded, 0), 0)
assert_equal(cbor_validate(encoded), false)
```

</details>

#### rejects truncated nested arrays

- rejects truncated nested arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated nested arrays")
val encoded = [make_initial_byte(major_array(), 1), make_initial_byte(major_text_string(), 2), 0x41]
assert_equal(cbor_item_size(encoded, 0), 0)
assert_equal(cbor_validate(encoded), false)
```

</details>

#### keeps complete byte strings valid

- keeps complete byte strings valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps complete byte strings valid")
val encoded = [make_initial_byte(major_byte_string(), 2), 0x41, 0x42]
assert_equal(cbor_item_size(encoded, 0), 3)
assert_equal(cbor_validate(encoded), true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_item_size_truncation_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CBOR item size truncation guards.
- CBOR item size truncation guards

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

- Canonical SPipe generation for source `7438e9bee593cf9c9ac4aa75d44bebc3113f308b18c495be2b8f8c1f81de24e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7438e9bee593cf9c9ac4aa75d44bebc3113f308b18c495be2b8f8c1f81de24e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7438e9bee593cf9c9ac4aa75d44bebc3113f308b18c495be2b8f8c1f81de24e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/cbor_item_size_truncation_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/cbor_item_size_truncation_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/cbor_item_size_truncation_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/cbor_item_size_truncation_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/cbor_item_size_truncation_guard_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncated integer headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_item_size_truncation_guard_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncated byte string payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_item_size_truncation_guard_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncated nested arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
