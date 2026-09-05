# Ignored Return Warning Specification

> Tests covering Ignored Return Warning.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ignored Return Warning Specification

## Scenarios

### Ignored Return Warning

#### should inspect expression statements for direct function calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should inspect expression statements for direct function calls
   - Expected: src contains `fn eval_stmt_expr(sid: i64) -> i64:`
   - Expected: src contains `if e_tag == EXPR_CALL`
   - Expected: src contains `val callee_eid = e_node.left`
   - Expected: src contains `if callee_tag == EXPR_IDENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should inspect expression statements for direct function calls")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
# Anchored to real code; the "# Check if this is a function call with
# ignored return value" comment must not be able to satisfy this.
expect(src.contains("fn eval_stmt_expr(sid: i64) -> i64:")).to_equal(true)
expect(src.contains("if e_tag == EXPR_CALL")).to_equal(true)
expect(src.contains("val callee_eid = e_node.left")).to_equal(true)
expect(src.contains("if callee_tag == EXPR_IDENT")).to_equal(true)
```

</details>

#### should use registered return types to suppress void and unknown calls

- should use registered return types to suppress void and unknown calls
   - Expected: stmt_src contains `val ret_type = func_lookup_return_type(fn_name)`
   - Expected: stmt_src contains `val is_void = ret_type == 0`
   - Expected: stmt_src contains `val is_unknown = ret_type == -1`
   - Expected: stmt_src contains `if is_void == false and is_unknown == false`
   - Expected: table_src contains `fn func_lookup_return_type(name: text) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should use registered return types to suppress void and unknown calls")
val stmt_src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
val table_src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
expect(stmt_src.contains("val ret_type = func_lookup_return_type(fn_name)")).to_equal(true)
expect(stmt_src.contains("val is_void = ret_type == 0")).to_equal(true)
expect(stmt_src.contains("val is_unknown = ret_type == -1")).to_equal(true)
expect(stmt_src.contains("if is_void == false and is_unknown == false")).to_equal(true)
expect(table_src.contains("fn func_lookup_return_type(name: text) -> i64")).to_equal(true)
```

</details>

#### should emit normal ignored return warnings with type and function name

- should emit normal ignored return warnings with type and function name
   - Expected: src contains `val type_name = type_tag_name(ret_type)`
   - Expected: src contains `warning: return value of type '`
   - Expected: src contains `from function '`
   - Expected: src contains `is ignored`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should emit normal ignored return warnings with type and function name")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("val type_name = type_tag_name(ret_type)")).to_equal(true)
expect(src.contains("warning: return value of type '")).to_equal(true)
expect(src.contains("from function '")).to_equal(true)
expect(src.contains("is ignored")).to_equal(true)
```

</details>

#### should route must_use and critical cases through R9 diagnostics

- should route must_use and critical cases through R9 diagnostics
   - Expected: src contains `if must_use_is_registered(fn_name)`
   - Expected: src contains `error[R9]: return value of function '`
   - Expected: src contains `elif must_use_critical_mode`
   - Expected: src contains `discarded in @profile(critical)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should route must_use and critical cases through R9 diagnostics")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("if must_use_is_registered(fn_name)")).to_equal(true)
expect(src.contains("error[R9]: return value of function '")).to_equal(true)
expect(src.contains("elif must_use_critical_mode")).to_equal(true)
expect(src.contains("discarded in @profile(critical)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/ignored_return_warning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ignored Return Warning.
- Ignored Return Warning

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

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09a37a3f986b67ccc6eb4900de4dec5045087558fcd84236f96f853d7e794f64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09a37a3f986b67ccc6eb4900de4dec5045087558fcd84236f96f853d7e794f64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09a37a3f986b67ccc6eb4900de4dec5045087558fcd84236f96f853d7e794f64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler_core/ignored_return_warning_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/ignored_return_warning_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/ignored_return_warning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/ignored_return_warning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/ignored_return_warning_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should inspect expression statements for direct function calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ignored_return_warning_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should inspect expression statements for direct function calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ignored_return_warning_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use registered return types to suppress void and unknown calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ignored_return_warning_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use registered return types to suppress void and unknown calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ignored_return_warning_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit normal ignored return warnings with type and function name' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ignored_return_warning_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit normal ignored return warnings with type and function name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ignored_return_warning_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route must_use and critical cases through R9 diagnostics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
