# New Tokens Specification

> <details>

<!-- sdn-diagram:id=new_tokens_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=new_tokens_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

new_tokens_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=new_tokens_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# New Tokens Specification

## Scenarios

### New Tokens

#### defines compile-time keyword token constants

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/10.frontend/core/tokens.spl")

expect(src).to_contain("const TOK_KW_STATIC_FOR: i64 = 201")
expect(src).to_contain("const TOK_KW_COMPTIME: i64 = 202")
expect(src).to_contain("const TOK_KW_MIXIN: i64 = 203")
```

</details>

#### maps compile-time keyword token names and keyword lookup

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/10.frontend/core/tokens.spl")

expect(src).to_contain("if kind == TOK_KW_STATIC_FOR: return \"static_for\"")
expect(src).to_contain("if kind == TOK_KW_COMPTIME: return \"comptime\"")
expect(src).to_contain("if kind == TOK_KW_MIXIN: return \"mixin\"")
expect(src).to_contain("if name == \"static_for\": return TOK_KW_STATIC_FOR")
expect(src).to_contain("if name == \"comptime\": return TOK_KW_COMPTIME")
expect(src).to_contain("if name == \"mixin\": return TOK_KW_MIXIN")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/new_tokens_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- New Tokens

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
