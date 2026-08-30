# Mock Specification

> Tests covering Mock Library (std twin smoke test).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Specification

## Scenarios

### Mock Library

### MockPolicy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a mock, stubs it, and verifies the call was recorded


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a mock, stubs it, and verifies the call was recorded")
val m = Mock.new("Service")
m.when("get").returns(42)
expect m.call("get", []) == 42
m.verify("get").was_called().verify()
expect m.recorder.call_count("get") == 1
```

</details>

#### tracks initialization state

- creates a spy and records calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a spy and records calls")
val s = Spy.new("Service")
s.record_call("ping", [])
expect s.was_called("ping") == true
```

</details>

#### matches HAL patterns

- creates a stub and stores values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a stub and stores values")
val s = Stub.new("Config").set("k", 1)
expect s.get("k") == 1
```

</details>

#### records and verifies via CallRecorder/CallVerifier directly

- records and verifies via CallRecorder/CallVerifier directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records and verifies via CallRecorder/CallVerifier directly")
var recorder = CallRecorder.new()
recorder = recorder.record("m", [])
val verifier = CallVerifier.new(recorder, "m")
expect verifier.get_matching_calls().len() == 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock Library (std twin smoke test).
- Mock Library (std twin smoke test)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
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

- Canonical SPipe generation for source `bce675f9df906dcd96057b3c669837913951e762b0ae306e5d5638af3d12bd6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bce675f9df906dcd96057b3c669837913951e762b0ae306e5d5638af3d12bd6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bce675f9df906dcd96057b3c669837913951e762b0ae306e5d5638af3d12bd6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/mock_spec.spl
mirror: doc/06_spec/01_unit/std/mock_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/mock_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a mock, stubs it, and verifies the call was recorded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a spy and records calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a stub and stores values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
