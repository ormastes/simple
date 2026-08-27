# Case Soft Keyword Specification

> Tests covering `case` is a soft keyword, not a reserved word.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Case Soft Keyword Specification

## Scenarios

### `case` is a soft keyword, not a reserved word

<details>
<summary>Advanced: binds `case` as a for-loop variable</summary>

#### binds `case` as a for-loop variable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds `case` as a for-loop variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds `case` as a for-loop variable")
# THE ORIGINAL REPRO: this line alone used to kill the whole file.
var total = 0
for case in [1, 2, 3]:
    total = total + case
expect total to_equal 6
```

</details>


</details>

#### binds `case` as a val and reads a field off it

- binds `case` as a val and reads a field off it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds `case` as a val and reads a field off it")
val case = Scenario(label: "alpha", weight: 7)
expect case.label to_equal "alpha"
expect case.weight to_equal 7
```

</details>

#### reassigns `case` as a var

- reassigns `case` as a var


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassigns `case` as a var")
var case = 1
case = case + 41
expect case to_equal 42
```

</details>

#### iterates structs bound to `case`, the shape sfnt_spec.spl used

- iterates structs bound to `case`, the shape sfnt_spec.spl used


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates structs bound to `case`, the shape sfnt_spec.spl used")
val cases = [Scenario(label: "a", weight: 1), Scenario(label: "b", weight: 2)]
var sum = 0
var names = ""
for case in cases:
    sum = sum + case.weight
    names = names + case.label
expect sum to_equal 3
expect names to_equal "ab"
```

</details>

#### still parses `case` as a match arm marker

- still parses `case` as a match arm marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still parses `case` as a match arm marker")
# The un-reservation must NOT cost the keyword its real job.
val classify = \n: match n:
    case 0: "zero"
    case 1: "one"
    case _: "many"
expect classify(0) to_equal "zero"
expect classify(1) to_equal "one"
expect classify(9) to_equal "many"
```

</details>

#### uses a variable named `case` inside a match arm body

- uses a variable named `case` inside a match arm body


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses a variable named `case` inside a match arm body")
var case = 10
val label = match case:
    case 10: "ten"
    case _: "other"
expect label to_equal "ten"
expect case to_equal 10
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/case_soft_keyword_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering `case` is a soft keyword, not a reserved word.
- `case` is a soft keyword, not a reserved word

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

- Canonical SPipe generation for source `045fed9ed2f1e5dc51d125991f2f8fc94905176e8ad318513bde66ac4a1e9545`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `045fed9ed2f1e5dc51d125991f2f8fc94905176e8ad318513bde66ac4a1e9545`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `045fed9ed2f1e5dc51d125991f2f8fc94905176e8ad318513bde66ac4a1e9545`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/case_soft_keyword_spec.spl
mirror: doc/06_spec/01_unit/compiler/case_soft_keyword_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/case_soft_keyword_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/case_soft_keyword_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/case_soft_keyword_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds `case` as a for-loop variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/case_soft_keyword_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds `case` as a val and reads a field off it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/case_soft_keyword_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reassigns `case` as a var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
