# Ast Clone Specification

> Tests covering Ast Clone.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ast Clone Specification

## Scenarios

### Ast Clone

#### should clone expression scalar fields and child links

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should clone expression scalar fields and child links
   - Expected: src contains `fn ast_clone_expr(source_eid: i64) -> i64`
   - Expected: src contains `if source_eid < 0`
   - Expected: src contains `dst.i_val = src.i_val`
   - Expected: src contains `dst.left = ast_clone_expr(src.left)`
   - Expected: src contains `dst.right = ast_clone_expr(src.right)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should clone expression scalar fields and child links")
val src = ast_clone_source()
expect(src.contains("fn ast_clone_expr(source_eid: i64) -> i64")).to_equal(true)
expect(src.contains("if source_eid < 0")).to_equal(true)
expect(src.contains("dst.i_val = src.i_val")).to_equal(true)
expect(src.contains("dst.left = ast_clone_expr(src.left)")).to_equal(true)
expect(src.contains("dst.right = ast_clone_expr(src.right)")).to_equal(true)
```

</details>

#### should clone expression argument and statement lists

- should clone expression argument and statement lists
   - Expected: src contains `fn ast_clone_expr_list(source_eids: [i64]) -> [i64]`
   - Expected: src contains `for arg_eid in src.args`
   - Expected: src contains `new_args.push(ast_clone_expr(arg_eid))`
   - Expected: src contains `for stmt_id in src.stmts`
   - Expected: src contains `new_stmts.push(ast_clone_stmt(stmt_id))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should clone expression argument and statement lists")
val src = ast_clone_source()
expect(src.contains("fn ast_clone_expr_list(source_eids: [i64]) -> [i64]")).to_equal(true)
expect(src.contains("for arg_eid in src.args")).to_equal(true)
expect(src.contains("new_args.push(ast_clone_expr(arg_eid))")).to_equal(true)
expect(src.contains("for stmt_id in src.stmts")).to_equal(true)
expect(src.contains("new_stmts.push(ast_clone_stmt(stmt_id))")).to_equal(true)
```

</details>

#### should clone statement values bodies and elif branches

- should clone statement values bodies and elif branches
   - Expected: src contains `fn ast_clone_stmt(source_sid: i64) -> i64`
   - Expected: src contains `if source_sid < 0`
   - Expected: src contains `dst.target = ast_clone_expr(src.target)`
   - Expected: src contains `dst.body = new_body`
   - Expected: src contains `dst.elif_bodies = new_elif_bodies`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should clone statement values bodies and elif branches")
val src = ast_clone_source()
expect(src.contains("fn ast_clone_stmt(source_sid: i64) -> i64")).to_equal(true)
expect(src.contains("if source_sid < 0")).to_equal(true)
expect(src.contains("dst.target = ast_clone_expr(src.target)")).to_equal(true)
expect(src.contains("dst.body = new_body")).to_equal(true)
expect(src.contains("dst.elif_bodies = new_elif_bodies")).to_equal(true)
```

</details>

#### should clone declarations while clearing specialization type parameters

- should clone declarations while clearing specialization type parameters
   - Expected: src contains `fn ast_clone_decl(source_did: i64) -> i64`
   - Expected: src contains `if source_did < 0`
   - Expected: src contains `dst.param_names = new_param_names`
   - Expected: src contains `dst.body_stmts = new_body`
   - Expected: src contains `dst.type_params = []`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should clone declarations while clearing specialization type parameters")
val src = ast_clone_source()
expect(src.contains("fn ast_clone_decl(source_did: i64) -> i64")).to_equal(true)
expect(src.contains("if source_did < 0")).to_equal(true)
expect(src.contains("dst.param_names = new_param_names")).to_equal(true)
expect(src.contains("dst.body_stmts = new_body")).to_equal(true)
expect(src.contains("dst.type_params = []")).to_equal(true)
```

</details>

#### should expose generic detection helpers

- should expose generic detection helpers
   - Expected: src contains `fn ast_clone_get_type_params(decl_id: i64) -> [text]`
   - Expected: src contains `fn ast_clone_is_generic(decl_id: i64) -> bool`
   - Expected: src contains `tparams.len() > 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose generic detection helpers")
val src = ast_clone_source()
expect(src.contains("fn ast_clone_get_type_params(decl_id: i64) -> [text]")).to_equal(true)
expect(src.contains("fn ast_clone_is_generic(decl_id: i64) -> bool")).to_equal(true)
expect(src.contains("tparams.len() > 0")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/ast_clone_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ast Clone.
- Ast Clone

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `de2adb2a6b67a4265fbd43d213061af9573e0ede6e5fe674162f0205f359c004`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de2adb2a6b67a4265fbd43d213061af9573e0ede6e5fe674162f0205f359c004`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de2adb2a6b67a4265fbd43d213061af9573e0ede6e5fe674162f0205f359c004`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler_core/ast_clone_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/ast_clone_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/ast_clone_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/ast_clone_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/ast_clone_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clone expression scalar fields and child links' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ast_clone_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should clone expression scalar fields and child links' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ast_clone_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clone expression argument and statement lists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ast_clone_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should clone expression argument and statement lists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ast_clone_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clone statement values bodies and elif branches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ast_clone_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should clone statement values bodies and elif branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ast_clone_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clone declarations while clearing specialization type parameters' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ast_clone_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose generic detection helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
