# Match Expr Binding Scope Specification

> Tests covering interpreter match-expression binding scope.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Expr Binding Scope Specification

## Scenarios

### interpreter match-expression binding scope

#### discards a binding when its guard fails

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discards a binding when its guard fails
   - Expected: result equals `0`
   - Expected: n equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("discards a binding when its guard fails")
var n = 99
val result = match 5:
    case n if n < 0: -1
    case _: 0
expect(result).to_equal(0)
expect(n).to_equal(99)
```

</details>

#### keeps a successful arm binding local to the arm

- keeps a successful arm binding local to the arm
   - Expected: result equals `5`
   - Expected: n equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a successful arm binding local to the arm")
var n = 99
val result = match 5:
    case n if n > 0: n
    case _: 0
expect(result).to_equal(5)
expect(n).to_equal(99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/match_expr_binding_scope_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter match-expression binding scope.
- interpreter match-expression binding scope

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b76dd8e3f9f624e7975583e6fabcd0d622c3bc5b21be51def2a31df203649752`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b76dd8e3f9f624e7975583e6fabcd0d622c3bc5b21be51def2a31df203649752`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b76dd8e3f9f624e7975583e6fabcd0d622c3bc5b21be51def2a31df203649752`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/match_expr_binding_scope_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/match_expr_binding_scope_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/match_expr_binding_scope_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/match_expr_binding_scope_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/match_expr_binding_scope_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/match_expr_binding_scope_spec.spl:9:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discards a binding when its guard fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/match_expr_binding_scope_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a successful arm binding local to the arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
