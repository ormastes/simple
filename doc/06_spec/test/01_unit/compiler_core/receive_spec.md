# Receive Specification

> <details>

<!-- sdn-diagram:id=receive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=receive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

receive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=receive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Receive Specification

## Scenarios

### Receive

#### should reserve receive and after token tags

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(src.contains("const TOK_KW_RECEIVE: i64 = 206")).to_equal(true)
expect(src.contains("const TOK_KW_AFTER: i64 = 207")).to_equal(true)
expect(src.contains("if name == \"receive\": return TOK_KW_RECEIVE")).to_equal(true)
expect(src.contains("if name == \"after\": return TOK_KW_AFTER")).to_equal(true)
```

</details>

#### should reserve and construct receive statements

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
expect(src.contains("const STMT_RECEIVE = 19")).to_equal(true)
expect(src.contains("fn stmt_receive_stmt(arm_indices: [i64], timeout_expr: i64, timeout_body_idx: i64, span_id: i64) -> i64")).to_equal(true)
expect(src.contains("val idx = stmt_alloc(STMT_RECEIVE, span_id)")).to_equal(true)
expect(src.contains("stmt_body[idx] = arm_indices")).to_equal(true)
```

</details>

#### should parse receive arms and after timeout arms

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_stmts.spl")
expect(src.contains("fn parse_receive_stmt() -> i64")).to_equal(true)
expect(src.contains("if par_kind_get() == 207")).to_equal(true)
expect(src.contains("timeout_expr = parse_expr()")).to_equal(true)
expect(src.contains("arm_new_with_binding_and_rationale")).to_equal(true)
expect(src.contains("stmt_receive_stmt(arm_indices, timeout_expr, timeout_body_idx, 0)")).to_equal(true)
```

</details>

#### should evaluate timeout body or first receive arm body

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
