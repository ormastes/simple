# Feature Ids Specification

> Tests covering FeatureId new variants to_string, FeatureId new variants distinctness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Ids Specification

## Scenarios

### FeatureId new variants to_string

#### PracticeScript has correct to_string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- PracticeScript has correct to_string
   - Expected: f.to_string() equals `PracticeScript`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PracticeScript has correct to_string")
val f = FeatureId.PracticeScript
expect(f.to_string()).to_equal("PracticeScript")
```

</details>

#### OpenocdMonitor has correct to_string

- OpenocdMonitor has correct to_string
   - Expected: f.to_string() equals `OpenocdMonitor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OpenocdMonitor has correct to_string")
val f = FeatureId.OpenocdMonitor
expect(f.to_string()).to_equal("OpenocdMonitor")
```

</details>

#### SemihostRead has correct to_string

- SemihostRead has correct to_string
   - Expected: f.to_string() equals `SemihostRead`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SemihostRead has correct to_string")
val f = FeatureId.SemihostRead
expect(f.to_string()).to_equal("SemihostRead")
```

</details>

### FeatureId new variants distinctness

#### PracticeScript is not OpenocdMonitor

- PracticeScript is not OpenocdMonitor
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PracticeScript is not OpenocdMonitor")
val a = FeatureId.PracticeScript
val b = FeatureId.OpenocdMonitor
expect(a.eq(b)).to_equal(false)
```

</details>

#### OpenocdMonitor is not SemihostRead

- OpenocdMonitor is not SemihostRead
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OpenocdMonitor is not SemihostRead")
val a = FeatureId.OpenocdMonitor
val b = FeatureId.SemihostRead
expect(a.eq(b)).to_equal(false)
```

</details>

#### PracticeScript equals itself

- PracticeScript equals itself
   - Expected: a.eq(b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PracticeScript equals itself")
val a = FeatureId.PracticeScript
val b = FeatureId.PracticeScript
expect(a.eq(b)).to_equal(true)
```

</details>

#### new variants are distinct from existing

- new variants are distinct from existing
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new variants are distinct from existing")
val a = FeatureId.PracticeScript
val b = FeatureId.FlashProgram
expect(a.eq(b)).to_equal(false)
```

</details>

#### OpenocdMonitor is distinct from SystemReset

- OpenocdMonitor is distinct from SystemReset
   - Expected: a.eq(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OpenocdMonitor is distinct from SystemReset")
val a = FeatureId.OpenocdMonitor
val b = FeatureId.SystemReset
expect(a.eq(b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/feature_ids_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FeatureId new variants to_string, FeatureId new variants distinctness.
- FeatureId new variants to_string
- FeatureId new variants distinctness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `0466194e96a195750f6c5867422aa57524bb43c354c7dda4ee941c90dfd7960c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0466194e96a195750f6c5867422aa57524bb43c354c7dda4ee941c90dfd7960c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0466194e96a195750f6c5867422aa57524bb43c354c7dda4ee941c90dfd7960c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/debug/remote/feature_ids_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/feature_ids_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/feature_ids_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/feature_ids_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/feature_ids_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PracticeScript has correct to_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/feature_ids_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'OpenocdMonitor has correct to_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/feature_ids_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SemihostRead has correct to_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
