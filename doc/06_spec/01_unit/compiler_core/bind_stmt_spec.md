# Bind Stmt Specification

> Tests covering Bind Stmt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bind Stmt Specification

## Scenarios

### Bind Stmt

#### should reserve statement and token tags for bind statements

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reserve statement and token tags for bind statements
   - Expected: stmt_src contains `const STMT_BIND = 20`
   - Expected: token_src contains `const TOK_KW_BIND: i64 = 204`
   - Expected: token_src contains `if name == "bind": return TOK_KW_BIND`
   - Expected: token_src contains `if kind == TOK_KW_BIND: return "bind"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should reserve statement and token tags for bind statements")
val stmt_src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
val token_src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(stmt_src.contains("const STMT_BIND = 20")).to_equal(true)
expect(token_src.contains("const TOK_KW_BIND: i64 = 204")).to_equal(true)
expect(token_src.contains("if name == \"bind\": return TOK_KW_BIND")).to_equal(true)
expect(token_src.contains("if kind == TOK_KW_BIND: return \"bind\"")).to_equal(true)
```

</details>

#### should construct bind statements with name and expression

- should construct bind statements with name and expression
   - Expected: stmt_src contains `fn stmt_bind_stmt(var_name: text, rhs_expr: i64, span_id: i64) -> i64`
   - Expected: stmt_src contains `val idx = stmt_alloc(STMT_BIND, span_id)`
   - Expected: stmt_src contains `stmt_name[idx] = var_name`
   - Expected: stmt_src contains `stmt_expr[idx] = rhs_expr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should construct bind statements with name and expression")
val stmt_src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
expect(stmt_src.contains("fn stmt_bind_stmt(var_name: text, rhs_expr: i64, span_id: i64) -> i64")).to_equal(true)
expect(stmt_src.contains("val idx = stmt_alloc(STMT_BIND, span_id)")).to_equal(true)
expect(stmt_src.contains("stmt_name[idx] = var_name")).to_equal(true)
expect(stmt_src.contains("stmt_expr[idx] = rhs_expr")).to_equal(true)
```

</details>

#### should expose bind parsing and evaluation surfaces

- should expose bind parsing and evaluation surfaces
   - Expected: parser_src contains `use compiler.core.tokens.{TOK_KW_BIND`
   - Expected: parser_src contains `STMT_BIND, stmt_bind_stmt`
   - Expected: eval_src contains `if tag == STMT_BIND`
   - Expected: init_src contains `export STMT_BIND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose bind parsing and evaluation surfaces")
val parser_src = read_source("src/compiler/10.frontend/core/parser_stmts.spl")
val eval_src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
val init_src = read_source("src/compiler/10.frontend/core/__init__.spl")
expect(parser_src.contains("use compiler.core.tokens.{TOK_KW_BIND")).to_equal(true)
expect(parser_src.contains("STMT_BIND, stmt_bind_stmt")).to_equal(true)
expect(eval_src.contains("if tag == STMT_BIND")).to_equal(true)
expect(init_src.contains("export STMT_BIND")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/bind_stmt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bind Stmt.
- Bind Stmt

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

- Canonical SPipe generation for source `951d64d2e049a217af9efeb6cea37ab931833a1fbfd1e928ab16ce08fd874cea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `951d64d2e049a217af9efeb6cea37ab931833a1fbfd1e928ab16ce08fd874cea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `951d64d2e049a217af9efeb6cea37ab931833a1fbfd1e928ab16ce08fd874cea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler_core/bind_stmt_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/bind_stmt_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/bind_stmt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/bind_stmt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/bind_stmt_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reserve statement and token tags for bind statements' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/bind_stmt_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reserve statement and token tags for bind statements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/bind_stmt_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct bind statements with name and expression' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/bind_stmt_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct bind statements with name and expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/bind_stmt_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose bind parsing and evaluation surfaces' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/bind_stmt_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose bind parsing and evaluation surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
