# Tmp Test Specification

> Tests covering tmp test.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test Specification

## Scenarios

### tmp test

#### should report undefined identifiers during expression evaluation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should report undefined identifiers during expression evaluation
   - Expected: src contains `fn eval_ident(eid: i64) -> i64`
   - Expected: src contains `val vid = env_lookup(name)`
   - Expected: src contains `val decl_id = func_table_lookup(name)`
   - Expected: src contains `eval_set_error("undefined variable: " + name)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should report undefined identifiers during expression evaluation")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(src.contains("fn eval_ident(eid: i64) -> i64")).to_equal(true)
expect(src.contains("val vid = env_lookup(name)")).to_equal(true)
expect(src.contains("val decl_id = func_table_lookup(name)")).to_equal(true)
expect(src.contains("eval_set_error(\"undefined variable: \" + name)")).to_equal(true)
```

</details>

#### should report undefined variables during statement assignment

- should report undefined variables during statement assignment
   - Expected: src contains `eval_set_error("undefined variable: " + name)`
   - Expected: src contains `val old_val = env_lookup(name)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should report undefined variables during statement assignment")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("eval_set_error(\"undefined variable: \" + name)")).to_equal(true)
expect(src.contains("val old_val = env_lookup(name)")).to_equal(true)
```

</details>

#### should keep the public undefined-name diagnostic helper exported

- should keep the public undefined-name diagnostic helper exported
   - Expected: error_src contains `fn error_undefined_name(line: i64, col: i64, name: text)`
   - Expected: error_src contains `undefined name ``
   - Expected: init_src contains `export error_undefined_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should keep the public undefined-name diagnostic helper exported")
val error_src = read_source("src/compiler/10.frontend/core/error.spl")
val init_src = read_source("src/compiler/10.frontend/core/__init__.spl")
expect(error_src.contains("fn error_undefined_name(line: i64, col: i64, name: text)")).to_equal(true)
expect(error_src.contains("undefined name `")).to_equal(true)
expect(init_src.contains("export error_undefined_name")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/tmp_test_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tmp test.
- tmp test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `162a3782af011475432abacb22a6470a6f01d024fc6f33a8f02acbe9dc3a1e3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `162a3782af011475432abacb22a6470a6f01d024fc6f33a8f02acbe9dc3a1e3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `162a3782af011475432abacb22a6470a6f01d024fc6f33a8f02acbe9dc3a1e3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler_core/tmp_test_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/tmp_test_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/tmp_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/tmp_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/tmp_test_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report undefined identifiers during expression evaluation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/tmp_test_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report undefined identifiers during expression evaluation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/tmp_test_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report undefined variables during statement assignment' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/tmp_test_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report undefined variables during statement assignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/tmp_test_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the public undefined-name diagnostic helper exported' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/tmp_test_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep the public undefined-name diagnostic helper exported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
