# Traits Specification

> <details>

<!-- sdn-diagram:id=traits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Specification

## Scenarios

### Traits

#### should reserve tokens for keyof and static_for

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(src.contains("const TOK_KW_KEYOF: i64 = 200")).to_equal(true)
expect(src.contains("const TOK_KW_STATIC_FOR: i64 = 201")).to_equal(true)
expect(src.contains("if name == \"keyof\": return TOK_KW_KEYOF")).to_equal(true)
expect(src.contains("if name == \"static_for\": return TOK_KW_STATIC_FOR")).to_equal(true)
expect(src.contains("if kind == TOK_KW_KEYOF: return \"keyof\"")).to_equal(true)
expect(src.contains("if kind == TOK_KW_STATIC_FOR: return \"static_for\"")).to_equal(true)
```

</details>

#### should desugar annotation calls and keyof into traits calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_primary_part2.spl")
expect(src.contains("@traits(query, T, ...) desugars to __traits")).to_equal(true)
expect(src.contains("val at_callee = expr_ident(\"__traits\", 0)")).to_equal(true)
expect(src.contains("val at_builtin_name = \"__builtin_\" + ann_name")).to_equal(true)
expect(src.contains("keyof_args.push(expr_string_lit(\"fields\", 0))")).to_equal(true)
expect(src.contains("val keyof_callee = expr_ident(\"__traits\", 0)")).to_equal(true)
```

</details>

#### should parse and build static_for statements

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser_src = read_source("src/compiler/10.frontend/core/parser_stmts.spl")
val ast_src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
expect(parser_src.contains("fn parse_static_for_stmt() -> i64")).to_equal(true)
expect(parser_src.contains("stmt_static_for_stmt(iter_name, iterable, body, 0)")).to_equal(true)
expect(ast_src.contains("const STMT_STATIC_FOR = 17")).to_equal(true)
expect(ast_src.contains("fn stmt_static_for_stmt(iter_name: text, iterable: i64, body_stmts: [i64], span_id: i64) -> i64")).to_equal(true)
```

</details>

#### should evaluate core traits reflection queries

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if name == \"__traits\"")).to_equal(true)
expect(src.contains("if tr_query == \"fields\"")).to_equal(true)
expect(src.contains("if tr_query == \"has_member\"")).to_equal(true)
expect(src.contains("if tr_query == \"enum_members\"")).to_equal(true)
expect(src.contains("if tr_query == \"is_struct\"")).to_equal(true)
expect(src.contains("if tr_query == \"is_enum\"")).to_equal(true)
```

</details>

<details>
<summary>Advanced: should execute static_for using normal loop semantics in interpreter mode</summary>

#### should execute static_for using normal loop semantics in interpreter mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("fn eval_stmt_static_for(sid: i64) -> i64")).to_equal(true)
expect(src.contains("if val_is_array(sf_iterable)")).to_equal(true)
expect(src.contains("env_define(sf_iter_name, sf_elem_vid)")).to_equal(true)
expect(src.contains("eval_set_error(\"static_for: cannot iterate over \"")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Traits

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
