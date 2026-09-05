# Probability Utils Specification

> Tests covering Probability Utilities, Collision Probability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Probability Utils Specification

## Scenarios

### Probability Utilities

### Collision Probability

#### returns 0 for n=0

- returns 0 for n=0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for n=0")
val prob = collision_probability(0)
expect prob == 0.0
```

</details>

#### returns very low probability for small n

- returns very low probability for small n


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns very low probability for small n")
val prob = collision_probability(10)
expect prob < 0.0001
```

</details>

#### returns low probability for moderate n

- returns low probability for moderate n


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns low probability for moderate n")
val prob = collision_probability(1000)
expect prob < 0.01
```

</details>

#### probability increases with n

- probability increases with n


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probability increases with n")
val prob_10 = collision_probability(10)
val prob_100 = collision_probability(100)
expect prob_100 > prob_10
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/probability_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Probability Utilities, Collision Probability.
- Probability Utilities
- Collision Probability

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

- Canonical SPipe generation for source `642469b56eee61a0b4e469c1d45ab04b55037b1b3d0d5ea321afd61775ca6982`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `642469b56eee61a0b4e469c1d45ab04b55037b1b3d0d5ea321afd61775ca6982`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `642469b56eee61a0b4e469c1d45ab04b55037b1b3d0d5ea321afd61775ca6982`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/probability_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/probability_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/probability_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/probability_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/probability_utils_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for n=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/probability_utils_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns very low probability for small n' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/probability_utils_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns low probability for moderate n' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
