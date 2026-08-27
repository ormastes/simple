# simple_nesting_spec

> Simple Nesting Test - 5 levels only

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_nesting_spec

Simple Nesting Test - 5 levels only

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/simple_nesting_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Nesting Test - 5 levels only
Tests if hook caching fixes the performance issue.

## Scenarios

### Simple Nesting (5 levels)

#### L1

#### L2

#### L3

#### L4

#### L5

#### test 1

- test 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test 1")
expect true
```

</details>

#### test 2

- test 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test 2")
expect true
```

</details>

#### test 3

- test 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test 3")
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `268e6769c22ff7d944dde31d6dab651fe36e4836a7ab7f2e88b0de7e8cfd25da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `268e6769c22ff7d944dde31d6dab651fe36e4836a7ab7f2e88b0de7e8cfd25da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `268e6769c22ff7d944dde31d6dab651fe36e4836a7ab7f2e88b0de7e8cfd25da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/generated/simple_nesting_spec.spl
mirror: doc/06_spec/03_system/generated/simple_nesting_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/generated/simple_nesting_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/generated/simple_nesting_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/generated/simple_nesting_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 1' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/simple_nesting_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/simple_nesting_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 2' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/simple_nesting_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/simple_nesting_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 3' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/simple_nesting_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
