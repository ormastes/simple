# Ast Clone Specification

> <details>

<!-- sdn-diagram:id=ast_clone_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ast_clone_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ast_clone_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ast_clone_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ast Clone Specification

## Scenarios

### Ast Clone

#### should clone expression scalar fields and child links

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ast_clone_source()
expect(src.contains("fn ast_clone_expr(source_eid: i64) -> i64")).to_equal(true)
expect(src.contains("if source_eid < 0")).to_equal(true)
expect(src.contains("dst.i_val = src.i_val")).to_equal(true)
expect(src.contains("dst.left = ast_clone_expr(src.left)")).to_equal(true)
expect(src.contains("dst.right = ast_clone_expr(src.right)")).to_equal(true)
```

</details>

#### should clone expression argument and statement lists

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ast_clone_source()
expect(src.contains("fn ast_clone_expr_list(source_eids: [i64]) -> [i64]")).to_equal(true)
expect(src.contains("for arg_eid in src.args")).to_equal(true)
expect(src.contains("new_args.push(ast_clone_expr(arg_eid))")).to_equal(true)
expect(src.contains("for stmt_id in src.stmts")).to_equal(true)
expect(src.contains("new_stmts.push(ast_clone_stmt(stmt_id))")).to_equal(true)
```

</details>

#### should clone statement values bodies and elif branches

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ast_clone_source()
expect(src.contains("fn ast_clone_stmt(source_sid: i64) -> i64")).to_equal(true)
expect(src.contains("if source_sid < 0")).to_equal(true)
expect(src.contains("dst.target = ast_clone_expr(src.target)")).to_equal(true)
expect(src.contains("dst.body = new_body")).to_equal(true)
expect(src.contains("dst.elif_bodies = new_elif_bodies")).to_equal(true)
```

</details>

#### should clone declarations while clearing specialization type parameters

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = ast_clone_source()
expect(src.contains("fn ast_clone_decl(source_did: i64) -> i64")).to_equal(true)
expect(src.contains("if source_did < 0")).to_equal(true)
expect(src.contains("dst.param_names = new_param_names")).to_equal(true)
expect(src.contains("dst.body_stmts = new_body")).to_equal(true)
expect(src.contains("dst.type_params = []")).to_equal(true)
```

</details>

#### should expose generic detection helpers

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
