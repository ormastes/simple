# Receive Specification

> Tests covering Receive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Receive Specification

## Scenarios

### Receive

#### should reserve receive and after token tags

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reserve receive and after token tags
   - Expected: src contains `const TOK_KW_RECEIVE: i64 = 206`
   - Expected: src contains `const TOK_KW_AFTER: i64 = 207`
   - Expected: src contains `if name == "receive": return TOK_KW_RECEIVE`
   - Expected: src contains `if name == "after": return TOK_KW_AFTER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should reserve receive and after token tags")
val src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(src.contains("const TOK_KW_RECEIVE: i64 = 206")).to_equal(true)
expect(src.contains("const TOK_KW_AFTER: i64 = 207")).to_equal(true)
expect(src.contains("if name == \"receive\": return TOK_KW_RECEIVE")).to_equal(true)
expect(src.contains("if name == \"after\": return TOK_KW_AFTER")).to_equal(true)
```

</details>

#### should reserve and construct receive statements

- should reserve and construct receive statements
   - Expected: src contains `const STMT_RECEIVE = 19`
   - Expected: src contains `fn stmt_receive_stmt(arm_indices: [i64], timeout_expr: i64, timeout_body_idx:... (full value in folded executable source)`
   - Expected: src contains `val idx = stmt_alloc(STMT_RECEIVE, span_id)`
   - Expected: src contains `stmt_body[idx] = arm_indices`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should reserve and construct receive statements")
val src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
expect(src.contains("const STMT_RECEIVE = 19")).to_equal(true)
expect(src.contains("fn stmt_receive_stmt(arm_indices: [i64], timeout_expr: i64, timeout_body_idx: i64, span_id: i64) -> i64")).to_equal(true)
expect(src.contains("val idx = stmt_alloc(STMT_RECEIVE, span_id)")).to_equal(true)
expect(src.contains("stmt_body[idx] = arm_indices")).to_equal(true)
```

</details>

#### should parse receive arms and after timeout arms

- should parse receive arms and after timeout arms
   - Expected: src contains `fn parse_receive_stmt() -> i64`
   - Expected: src contains `if par_kind_get() == 207`
   - Expected: src contains `timeout_expr = parse_expr()`
   - Expected: src contains `arm_new_with_binding_and_rationale`
   - Expected: src contains `stmt_receive_stmt(arm_indices, timeout_expr, timeout_body_idx, 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should parse receive arms and after timeout arms")
val src = read_source("src/compiler/10.frontend/core/parser_stmts.spl")
expect(src.contains("fn parse_receive_stmt() -> i64")).to_equal(true)
expect(src.contains("if par_kind_get() == 207")).to_equal(true)
expect(src.contains("timeout_expr = parse_expr()")).to_equal(true)
expect(src.contains("arm_new_with_binding_and_rationale")).to_equal(true)
expect(src.contains("stmt_receive_stmt(arm_indices, timeout_expr, timeout_body_idx, 0)")).to_equal(true)
```

</details>

#### should evaluate timeout body or first receive arm body

- should evaluate timeout body or first receive arm body
   - Expected: src contains `if tag == STMT_RECEIVE`
   - Expected: src contains `val recv_timeout_body = s_node_recv.type_tag`
   - Expected: src contains `return eval_stmt(recv_timeout_body)`
   - Expected: src contains `val first_arm_body = arm_get_body(recv_arms[0])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should evaluate timeout body or first receive arm body")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("if tag == STMT_RECEIVE")).to_equal(true)
expect(src.contains("val recv_timeout_body = s_node_recv.type_tag")).to_equal(true)
expect(src.contains("return eval_stmt(recv_timeout_body)")).to_equal(true)
expect(src.contains("val first_arm_body = arm_get_body(recv_arms[0])")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/receive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Receive.
- Receive

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

- Canonical SPipe generation for source `eff22e3a9c3a465f31e9b1f41724e8b511e84b511d292caf050731bf568613d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eff22e3a9c3a465f31e9b1f41724e8b511e84b511d292caf050731bf568613d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eff22e3a9c3a465f31e9b1f41724e8b511e84b511d292caf050731bf568613d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler_core/receive_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/receive_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/receive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/receive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/receive_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reserve receive and after token tags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/receive_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reserve receive and after token tags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/receive_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reserve and construct receive statements' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/receive_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reserve and construct receive statements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/receive_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse receive arms and after timeout arms' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/receive_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse receive arms and after timeout arms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/receive_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate timeout body or first receive arm body' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
