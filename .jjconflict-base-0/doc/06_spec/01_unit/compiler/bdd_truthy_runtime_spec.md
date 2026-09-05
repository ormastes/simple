# Bdd Truthy Runtime Specification

> Tests covering rt_bdd_expect_truthy_rv accepts bool and comparison results.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bdd Truthy Runtime Specification

## Scenarios

### rt_bdd_expect_truthy_rv accepts bool and comparison results

#### literal true is truthy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- literal true is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("literal true is truthy")
expect true
```

</details>

#### comparison result is truthy

- comparison result is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comparison result is truthy")
expect 1 == 1
```

</details>

#### integer one is truthy

- integer one is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer one is truthy")
expect 1
```

</details>

#### integer zero deliberate-fail RED

- integer zero deliberate-fail RED


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer zero deliberate-fail RED")
expect 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bdd_truthy_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_bdd_expect_truthy_rv accepts bool and comparison results.
- rt_bdd_expect_truthy_rv accepts bool and comparison results

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

- Canonical SPipe generation for source `7f6e5a92c07d9d0115a5477cc5e053c2a2a83916a5b860d586eff2a5459a0a3c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f6e5a92c07d9d0115a5477cc5e053c2a2a83916a5b860d586eff2a5459a0a3c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f6e5a92c07d9d0115a5477cc5e053c2a2a83916a5b860d586eff2a5459a0a3c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bdd_truthy_runtime_spec.spl
mirror: doc/06_spec/01_unit/compiler/bdd_truthy_runtime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bdd_truthy_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bdd_truthy_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bdd_truthy_runtime_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'literal true is truthy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_truthy_runtime_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'comparison result is truthy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_truthy_runtime_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integer one is truthy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
