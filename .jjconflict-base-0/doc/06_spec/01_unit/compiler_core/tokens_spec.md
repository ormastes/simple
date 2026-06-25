# Tokens Specification

> <details>

<!-- sdn-diagram:id=tokens_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tokens_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tokens_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tokens_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tokens Specification

## Scenarios

### Tokens

#### defines token names, keyword lookup, and precedence helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/10.frontend/core/tokens.spl")

expect(src).to_contain("fn tok_kind_name(kind: i64) -> text:")
expect(src).to_contain("if kind == TOK_INT_LIT: return \"IntLit\"")
expect(src).to_contain("if kind == TOK_PIPE_FORWARD: return \"|>\"")
expect(src).to_contain("return \"Unknown(\" + kind.to_text() + \")\"")

expect(src).to_contain("fn keyword_lookup(name: text) -> i64:")
expect(src).to_contain("if name == \"fn\": return TOK_KW_FN")
expect(src).to_contain("if name == \"nil\": return TOK_NIL_LIT")
expect(src).to_contain("    TOK_IDENT")

expect(src).to_contain("fn tok_precedence(kind: i64) -> i64:")
expect(src).to_contain("if kind == TOK_ASSIGN: return 1")
expect(src).to_contain("if kind == TOK_STAR_STAR: return 12")
expect(src).to_contain("return 0")
```

</details>

#### defines token classification helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/10.frontend/core/tokens.spl")

expect(src).to_contain("fn tok_is_right_assoc(kind: i64) -> bool:")
expect(src).to_contain("if kind == TOK_STAR_STAR: return true")
expect(src).to_contain("if tok_is_assignment(kind): return true")

expect(src).to_contain("fn tok_is_literal(kind: i64) -> bool:")
expect(src).to_contain("if kind == TOK_INT_LIT: return true")
expect(src).to_contain("if kind == TOK_NIL_LIT: return true")

expect(src).to_contain("fn tok_is_comparison(kind: i64) -> bool:")
expect(src).to_contain("if kind == TOK_GT_EQ: return true")
expect(src).to_contain("fn tok_is_assignment(kind: i64) -> bool:")
expect(src).to_contain("if kind == TOK_PERCENT_EQ: return true")
expect(src).to_contain("fn tok_is_additive(kind: i64) -> bool:")
expect(src).to_contain("fn tok_is_multiplicative(kind: i64) -> bool:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/tokens_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tokens

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
