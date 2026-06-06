# Ce Block Specification

> <details>

<!-- sdn-diagram:id=ce_block_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ce_block_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ce_block_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ce_block_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ce Block Specification

## Scenarios

### Ce Block

#### should reserve declaration and token tags for ce blocks

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ast_src = read_source("src/compiler/10.frontend/core/ast_part1.spl")
val token_src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(ast_src.contains("const DECL_CE = 11")).to_equal(true)
expect(token_src.contains("const TOK_KW_CE: i64 = 205")).to_equal(true)
expect(token_src.contains("if name == \"ce\": return TOK_KW_CE")).to_equal(true)
expect(token_src.contains("if kind == TOK_KW_CE: return \"ce\"")).to_equal(true)
```

</details>

#### should construct ce declarations with builder name and body

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ast_src = read_source("src/compiler/10.frontend/core/ast_part1.spl")
expect(ast_src.contains("fn decl_ce_block(builder_name: text, body_stmts: [i64], span_id: i64) -> i64")).to_equal(true)
expect(ast_src.contains("val idx = decl_alloc(DECL_CE, span_id)")).to_equal(true)
expect(ast_src.contains("decl_name[idx] = builder_name")).to_equal(true)
expect(ast_src.contains("decl_body_stmts[idx] = body_stmts")).to_equal(true)
```

</details>

#### should expose ce declarations through parser and core exports

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser_src = read_source("src/compiler/10.frontend/core/parser_decls_part2.spl")
val init_src = read_source("src/compiler/10.frontend/core/__init__.spl")
expect(parser_src.contains("use compiler.core.ast.{DECL_CE, decl_ce_block}")).to_equal(true)
expect(parser_src.contains("TOK_KW_CE")).to_equal(true)
expect(init_src.contains("export DECL_CE, decl_ce_block")).to_equal(true)
expect(init_src.contains("export TOK_KW_BIND, TOK_KW_CE")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/ce_block_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ce Block

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
