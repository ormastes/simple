# Guard Clause Specification

> Tests covering guard clauses, basic guard evaluation, guard with multiple arms.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guard Clause Specification

## Scenarios

### guard clauses

### basic guard evaluation

#### guard true: matches arm

- guard true: matches arm
   - Expected: result equals `big_five`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard true: matches arm")
val x = 5
val result = match x:
    case 5 if x > 3: "big_five"
    case 5: "five"
    case _: "other"
expect(result).to_equal("big_five")
```

</details>

#### guard false: falls to next arm

- guard false: falls to next arm
   - Expected: result equals `five`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard false: falls to next arm")
val x = 5
val result = match x:
    case 5 if x > 10: "big_five"
    case 5: "five"
    case _: "other"
expect(result).to_equal("five")
```

</details>

#### guard with string match

- guard with string match
   - Expected: result equals `long_hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard with string match")
val s = "hello"
val result = match s:
    case "hello" if s.len() > 3: "long_hello"
    case "hello": "hello"
    case _: "other"
expect(result).to_equal("long_hello")
```

</details>

#### guard with equality check

- guard with equality check
   - Expected: result equals `perfect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard with equality check")
val n = 42
val result = match n:
    case 42 if n == 42: "perfect"
    case 42: "forty_two"
    case _: "other"
expect(result).to_equal("perfect")
```

</details>

### guard with multiple arms

#### multiple guards evaluated in order

- multiple guards evaluated in order
   - Expected: result equals `medium`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple guards evaluated in order")
val x = 7
val result = match x:
    case 7 if x > 10: "large"
    case 7 if x > 5: "medium"
    case 7: "small"
    case _: "other"
expect(result).to_equal("medium")
```

</details>

#### wildcard with guard

- wildcard with guard
   - Expected: result equals `large`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wildcard with guard")
val x = 99
val result = match x:
    case 5: "five"
    case _ if x > 50: "large"
    case _: "other"
expect(result).to_equal("large")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/guard_clause_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering guard clauses, basic guard evaluation, guard with multiple arms.
- guard clauses
- basic guard evaluation
- guard with multiple arms

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

- Canonical SPipe generation for source `094cc8f07a50b31cc624177658334813e757e3f1cd460010c143eee6b7b9f106`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `094cc8f07a50b31cc624177658334813e757e3f1cd460010c143eee6b7b9f106`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `094cc8f07a50b31cc624177658334813e757e3f1cd460010c143eee6b7b9f106`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler_core/guard_clause_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/guard_clause_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/guard_clause_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/guard_clause_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/guard_clause_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guard true: matches arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/guard_clause_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guard false: falls to next arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/guard_clause_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guard with string match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
