# Match Expr Post Statement Cost Specification

> Tests covering match expression post-statement cost.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Expr Post Statement Cost Specification

## Scenarios

### match expression post-statement cost

#### returning arms still return and the taken arm yields its value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returning arms still return and the taken arm yields its value
   - Expected: work_match(1) equals `-1`
   - Expected: work_match(2) equals `-2`
   - Expected: work_match(5) equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returning arms still return and the taken arm yields its value")
expect(work_match(1)).to_equal(-1)
expect(work_match(2)).to_equal(-2)
expect(work_match(5)).to_equal(23)
```

</details>

#### statements after a match expression cost no more than 3x the hoisted form

- statements after a match expression cost no more than 3x the hoisted form


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("statements after a match expression cost no more than 3x the hoisted form")
# warm-up
time_calls(true)
time_calls(false)
val hoisted = time_calls(false)
val matched = time_calls(true)
val floor = if hoisted < 1000: 1000 else: hoisted
expect(matched <= floor * 3).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering match expression post-statement cost.
- match expression post-statement cost

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

- Canonical SPipe generation for source `da9d8267855cbc832c8e95f65c917a2ccd6cfb2710a4965ec9486aec8cfd00f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da9d8267855cbc832c8e95f65c917a2ccd6cfb2710a4965ec9486aec8cfd00f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da9d8267855cbc832c8e95f65c917a2ccd6cfb2710a4965ec9486aec8cfd00f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returning arms still return and the taken arm yields its value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/match_expr_post_statement_cost_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'statements after a match expression cost no more than 3x the hoisted form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
