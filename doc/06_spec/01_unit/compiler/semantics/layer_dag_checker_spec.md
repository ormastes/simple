# Layer Dag Checker Specification

> Tests covering layer DAG checker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Dag Checker Specification

## Scenarios

### layer DAG checker

#### accepts the sketch's acyclic DAG (draw <- gui <- web/wm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the sketch's acyclic DAG (draw <- gui <- web/wm)
   - Expected: v.diagnostic equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the sketch's acyclic DAG (draw <- gui <- web/wm)")
val reg = LayerDagRegistry.new()
reg.declare("draw")
reg.declare("gui")
reg.declare("web")
reg.declare("wm")
reg.uses("gui", "draw")
reg.uses("web", "gui")
reg.uses("web", "draw")
reg.uses("wm", "gui")
reg.uses("wm", "draw")
val v = check_layer_dag(reg)
assert_true(v.ok)
expect(v.diagnostic).to_equal("")
```

</details>

#### rejects a 2-cycle

- rejects a 2-cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 2-cycle")
val reg = LayerDagRegistry.new()
reg.declare("a")
reg.declare("b")
reg.uses("a", "b")
reg.uses("b", "a")
val v = check_layer_cycles(reg)
expect_not(v.ok)
assert_true(v.diagnostic.contains("cycle"))
```

</details>

#### rejects a 3-cycle

- rejects a 3-cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 3-cycle")
val reg = LayerDagRegistry.new()
reg.declare("a")
reg.declare("b")
reg.declare("c")
reg.uses("a", "b")
reg.uses("b", "c")
reg.uses("c", "a")
val v = check_layer_cycles(reg)
expect_not(v.ok)
assert_true(v.diagnostic.contains("cycle"))
```

</details>

#### rejects a self-edge

- rejects a self-edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a self-edge")
val reg = LayerDagRegistry.new()
reg.declare("a")
reg.uses("a", "a")
val v = check_layer_cycles(reg)
expect_not(v.ok)
assert_true(v.diagnostic.contains("cycle"))
```

</details>

#### rejects a declared-upward uses edge

- rejects a declared-upward uses edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a declared-upward uses edge")
val reg = LayerDagRegistry.new()
reg.declare("draw")
reg.declare("gui")
# "draw" is declared before "gui" but reaches upward to use it.
reg.uses("draw", "gui")
val v = check_declared_upward(reg)
expect_not(v.ok)
assert_true(v.diagnostic.contains("declared-upward"))
```

</details>

#### rejects a uses edge to an undeclared layer

- rejects a uses edge to an undeclared layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a uses edge to an undeclared layer")
val reg = LayerDagRegistry.new()
reg.declare("gui")
reg.uses("gui", "draw")
val v = check_declared_upward(reg)
expect_not(v.ok)
assert_true(v.diagnostic.contains("undeclared"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/layer_dag_checker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering layer DAG checker.
- layer DAG checker

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

- Canonical SPipe generation for source `29d0ad48bcc73d335393b75d969890327c1ebbf784689adf8a239cb8b650401f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29d0ad48bcc73d335393b75d969890327c1ebbf784689adf8a239cb8b650401f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29d0ad48bcc73d335393b75d969890327c1ebbf784689adf8a239cb8b650401f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/layer_dag_checker_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/layer_dag_checker_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/layer_dag_checker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/layer_dag_checker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/layer_dag_checker_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the sketch's acyclic DAG (draw <- gui <- web/wm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/layer_dag_checker_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a 2-cycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/layer_dag_checker_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a 3-cycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
