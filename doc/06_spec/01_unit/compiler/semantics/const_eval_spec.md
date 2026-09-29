# Const Eval Specification

> Tests covering evaluated constant text formatting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Eval Specification

## Scenarios

### evaluated constant text formatting

#### formats nested values through the typed formatter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats nested values through the typed formatter
   - Expected: value.to_text() equals `(7, [true, "ok"])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats nested values through the typed formatter")
val value = EvaluatedConstValue.Tuple([
    EvaluatedConstValue.Int(7),
    EvaluatedConstValue.Array([EvaluatedConstValue.Bool(true), EvaluatedConstValue.String("ok")])
])

expect(value.to_text()).to_equal("(7, [true, \"ok\"])")
```

</details>

#### uses the owned string helper for compile-time environment booleans

- uses the owned string helper for compile-time environment booleans
   - Expected: source does not contain `rt_env_get(env_name).to_lowercase()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the owned string helper for compile-time environment booleans")
val source = file_read("src/compiler/35.semantics/const_eval.spl")
expect(source).to_contain("str_to_lower(rt_env_get(env_name))")
expect(source.contains("rt_env_get(env_name).to_lowercase()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/const_eval_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering evaluated constant text formatting.
- evaluated constant text formatting

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a045b81ab4a1c00c520d2446b5ffaa62a83c21a67e156e421651ebad16144642`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a045b81ab4a1c00c520d2446b5ffaa62a83c21a67e156e421651ebad16144642`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a045b81ab4a1c00c520d2446b5ffaa62a83c21a67e156e421651ebad16144642`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/semantics/const_eval_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/const_eval_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/semantics/const_eval_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/const_eval_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/const_eval_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/semantics/const_eval_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/semantics/const_eval_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats nested values through the typed formatter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/const_eval_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the owned string helper for compile-time environment booleans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
