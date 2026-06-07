# Bind Stmt Specification

> <details>

<!-- sdn-diagram:id=bind_stmt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bind_stmt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bind_stmt_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bind_stmt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bind Stmt Specification

## Scenarios

### Bind Stmt

#### should reserve statement and token tags for bind statements

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt_src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
val token_src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(stmt_src.contains("const STMT_BIND = 20")).to_equal(true)
expect(token_src.contains("const TOK_KW_BIND: i64 = 204")).to_equal(true)
expect(token_src.contains("if name == \"bind\": return TOK_KW_BIND")).to_equal(true)
expect(token_src.contains("if kind == TOK_KW_BIND: return \"bind\"")).to_equal(true)
```

</details>

#### should construct bind statements with name and expression

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt_src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
expect(stmt_src.contains("fn stmt_bind_stmt(var_name: text, rhs_expr: i64, span_id: i64) -> i64")).to_equal(true)
expect(stmt_src.contains("val idx = stmt_alloc(STMT_BIND, span_id)")).to_equal(true)
expect(stmt_src.contains("stmt_name[idx] = var_name")).to_equal(true)
expect(stmt_src.contains("stmt_expr[idx] = rhs_expr")).to_equal(true)
```

</details>

#### should expose bind parsing and evaluation surfaces

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
