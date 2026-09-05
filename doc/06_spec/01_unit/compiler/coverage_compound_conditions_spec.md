# Coverage Compound Conditions Specification

> Tests covering Interpreter compound control coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Compound Conditions Specification

## Scenarios

### Interpreter compound control coverage

#### assigns source-stable condition identifiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns source-stable condition identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns source-stable condition identifiers")
val source = coverage_interpreter_source()
expect(source).to_contain("fn coverage_condition_id(condition_eid: i64) -> i64")
expect(source).to_contain("return span_start(condition_span) + 1")
expect(source).to_contain("condition_eid + 1")
```

</details>

#### records only short-circuit evaluated atomic operands

- records only short-circuit evaluated atomic operands


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records only short-circuit evaluated atomic operands")
val source = coverage_interpreter_source()
expect(source).to_contain("fn eval_control_condition(condition_eid: i64, decision_id: i64) -> i64")
expect(source).to_contain("if condition_node.tag == EXPR_BINARY and condition_node.i_val == 55:")
expect(source).to_contain("if condition_node.tag == EXPR_BINARY and condition_node.i_val == 56:")
expect(source).to_contain("record_control_condition(decision_id, condition_eid, taken)")
```

</details>

#### uses compound instrumentation for if while and match guards

- uses compound instrumentation for if while and match guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses compound instrumentation for if while and match guards")
val source = coverage_interpreter_source()
expect(source).to_contain("val cond_val = eval_control_condition(cond_id, eid)")
expect(source).to_contain("val cond_val = eval_control_condition(cond_eid, eid)")
expect(source).to_contain("val guard_val = eval_control_condition(guard_eid, arm_id)")
expect(source).to_contain("record_control_decision(")
```

</details>

#### uses the same predicate evaluation for statement controls

- uses the same predicate evaluation for statement controls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the same predicate evaluation for statement controls")
val source = coverage_statement_source()
expect(source).to_contain("fn record_stmt_control_decision(sid: i64, taken: bool)")
expect(source).to_contain("val cond_val = eval_control_condition(cond_eid, sid)")
expect(source).to_contain("record_stmt_control_decision(sid, taken)")
expect(source).to_contain("val guard_val = eval_control_condition(guard_eid, arm_id)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/coverage_compound_conditions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Interpreter compound control coverage.
- Interpreter compound control coverage

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

- Canonical SPipe generation for source `4715f5683930c87774021b6486a0c0d2a8199de615617a232be994561984e5ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4715f5683930c87774021b6486a0c0d2a8199de615617a232be994561984e5ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4715f5683930c87774021b6486a0c0d2a8199de615617a232be994561984e5ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/coverage_compound_conditions_spec.spl
mirror: doc/06_spec/01_unit/compiler/coverage_compound_conditions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/coverage_compound_conditions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/coverage_compound_conditions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/coverage_compound_conditions_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns source-stable condition identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/coverage_compound_conditions_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records only short-circuit evaluated atomic operands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/coverage_compound_conditions_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses compound instrumentation for if while and match guards' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
