# Eval Specification

> <details>

<!-- sdn-diagram:id=eval_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=eval_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

eval_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=eval_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Eval Specification

## Scenarios

### Eval

#### keeps evaluator reset error and expression dispatch available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = eval_source()

expect(source).to_contain("fn eval_reset()")
expect(source).to_contain("fn eval_set_error(msg: text)")
expect(source).to_contain("fn eval_get_error() -> text")
expect(source).to_contain("fn eval_has_error() -> bool")
expect(source).to_contain("fn eval_expr(eid: i64) -> i64")
expect(source).to_contain("fn eval_binary(eid: i64) -> i64")
expect(source).to_contain("fn eval_unary(eid: i64) -> i64")
```

</details>

#### keeps evaluator statement and declaration dispatch available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmts = eval_stmts_source()
val decls = eval_decls_source()

expect(stmts).to_contain("fn eval_stmt(sid: i64) -> i64")
expect(stmts).to_contain("fn eval_stmt_val_decl(sid: i64) -> i64")
expect(stmts).to_contain("fn eval_stmt_var_decl(sid: i64) -> i64")
expect(stmts).to_contain("fn eval_stmt_assign(sid: i64) -> i64")
expect(decls).to_contain("fn eval_decl(did: i64) -> i64")
expect(decls).to_contain("fn eval_module() -> i64")
expect(decls).to_contain("fn eval_init()")
```

</details>

#### keeps evaluator function table helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = eval_tables_source()

expect(source).to_contain("fn func_table_reset()")
expect(source).to_contain("fn func_table_register(name: text, decl_id: i64)")
expect(source).to_contain("fn func_table_lookup(name: text) -> i64")
expect(source).to_contain("fn func_table_remove(name: text) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/eval_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Eval

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
