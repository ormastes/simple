# Guard Clause Specification

> Tests covering guard clauses in match.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guard Clause Specification

## Scenarios

### guard clauses in match

#### guard filters match arm

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guard filters match arm
   - Expected: result equals `big ten`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard filters match arm")
val x = 10
val result = match x:
    case 10 if x > 5: "big ten"
    case 10: "small ten"
    case _: "other"
expect(result).to_equal("big ten")
```

</details>

#### guard false skips arm falls through

- guard false skips arm falls through
   - Expected: result equals `small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard false skips arm falls through")
val x = 3
val result = match x:
    case 3 if x > 5: "big"
    case _: "small"
expect(result).to_equal("small")
```

</details>

#### guard with complex condition

- guard with complex condition
   - Expected: result equals `above threshold`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard with complex condition")
val n = 42
val threshold = 40
val result = match n:
    case 42 if n > threshold: "above threshold"
    case _: "below"
expect(result).to_equal("above threshold")
```

</details>

#### guard with else fallthrough

- guard with else fallthrough
   - Expected: result equals `seven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard with else fallthrough")
val x = 7
val result = match x:
    case 7 if x < 5: "small seven"
    case 7: "seven"
    case _: "other"
expect(result).to_equal("seven")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/guard_clause_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering guard clauses in match.
- guard clauses in match

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

- Canonical SPipe generation for source `105a05b095389f87be2a792ebc9f029665b778d105e72897979ad1ab6cedb5ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `105a05b095389f87be2a792ebc9f029665b778d105e72897979ad1ab6cedb5ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `105a05b095389f87be2a792ebc9f029665b778d105e72897979ad1ab6cedb5ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/parser/guard_clause_spec.spl
mirror: doc/06_spec/unit/compiler/parser/guard_clause_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/guard_clause_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/guard_clause_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/guard_clause_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guard filters match arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/guard_clause_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guard false skips arm falls through' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/guard_clause_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guard with complex condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
