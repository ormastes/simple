# Protobuf Wire Fixed Payload Guard Specification

> Tests covering Protobuf wire fixed payload guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protobuf Wire Fixed Payload Guard Specification

## Scenarios

### Protobuf wire fixed payload guards

#### rejects short fixed32 payloads

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects short fixed32 payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects short fixed32 payloads")
assert_equal(pb_fixed32_from_payload([1, 2, 3]), 0)
```

</details>

#### rejects invalid fixed32 payload bytes

- rejects invalid fixed32 payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid fixed32 payload bytes")
assert_equal(pb_fixed32_from_payload([1, 2, 300, 4]), 0)
assert_equal(pb_fixed32_from_payload([1, -1, 3, 4]), 0)
```

</details>

#### keeps valid fixed32 payload decoding

- keeps valid fixed32 payload decoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid fixed32 payload decoding")
assert_equal(pb_fixed32_from_payload([1, 2, 3, 4]), 67305985)
```

</details>

#### rejects short fixed64 payloads

- rejects short fixed64 payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects short fixed64 payloads")
assert_equal(pb_fixed64_from_payload([1, 2, 3, 4, 5, 6, 7]), 0)
```

</details>

#### rejects invalid fixed64 payload bytes

- rejects invalid fixed64 payload bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid fixed64 payload bytes")
assert_equal(pb_fixed64_from_payload([1, 2, 3, 4, 5, 6, 7, 300]), 0)
assert_equal(pb_fixed64_from_payload([1, 2, 3, 4, 5, 6, -1, 8]), 0)
```

</details>

#### keeps valid fixed64 payload decoding

- keeps valid fixed64 payload decoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid fixed64 payload decoding")
assert_equal(pb_fixed64_from_payload([1, 2, 3, 4, 5, 6, 7, 8]), 578437695752307201)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Protobuf wire fixed payload guards.
- Protobuf wire fixed payload guards

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

- Canonical SPipe generation for source `97d20c19305d66a7b646acac64030c1a5957bbee40decf54b65bd77e3329b8c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97d20c19305d66a7b646acac64030c1a5957bbee40decf54b65bd77e3329b8c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97d20c19305d66a7b646acac64030c1a5957bbee40decf54b65bd77e3329b8c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects short fixed32 payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid fixed32 payload bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/protobuf_wire_fixed_payload_guard_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid fixed32 payload decoding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
