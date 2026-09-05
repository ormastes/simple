# P256 Probe2 Specification

> Tests covering probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Probe2 Specification

## Scenarios

### probe

#### smoke len inline

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- smoke len inline
   - Expected: out.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("smoke len inline")
var s: [u8] = []
var i: u64 = 0u64
while i < 31u64:
    s.push(0x00u8)
    i = i + 1u64
s.push(0x01u8)
val out = p256_keypair_pub(s)
expect(out.len().to_u64()).to_equal(65u64)
```

</details>

#### smoke len fn-result-stored

- smoke len fn-result-stored
   - Expected: out.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("smoke len fn-result-stored")
val s: [u8] = _cs()
val out = p256_keypair_pub(s)
expect(out.len().to_u64()).to_equal(65u64)
```

</details>

#### smoke len fn-direct

- smoke len fn-direct
   - Expected: out.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("smoke len fn-direct")
val out = p256_keypair_pub(_cs())
expect(out.len().to_u64()).to_equal(65u64)
```

</details>

#### trivial fn

- trivial fn
   - Expected: s.len().to_u64() equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trivial fn")
val s: [u8] = _trivial()
expect(s.len().to_u64()).to_equal(1u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/_p256_probe2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering probe.
- probe

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

- Canonical SPipe generation for source `42ea1a60ed6d5c6b497c768b8a667d0205f9065f98367fa88aacb37c217ab99f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42ea1a60ed6d5c6b497c768b8a667d0205f9065f98367fa88aacb37c217ab99f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42ea1a60ed6d5c6b497c768b8a667d0205f9065f98367fa88aacb37c217ab99f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/_p256_probe2_spec.spl
mirror: doc/06_spec/unit/os/tls13/_p256_probe2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/_p256_probe2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/_p256_probe2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/_p256_probe2_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'smoke len inline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/_p256_probe2_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'smoke len fn-result-stored' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/_p256_probe2_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'smoke len fn-direct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
