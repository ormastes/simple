# Keyof Token Specification

> <details>

<!-- sdn-diagram:id=keyof_token_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=keyof_token_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

keyof_token_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=keyof_token_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Keyof Token Specification

## Scenarios

### Keyof Token

#### defines keyof as a distinct keyword token

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/10.frontend/core/tokens.spl")

expect(src).to_contain("const TOK_KW_DYN: i64 = 199")
expect(src).to_contain("const TOK_KW_KEYOF: i64 = 200")
expect(src).to_contain("# keyof type operator")
```

</details>

#### maps keyof through token name and keyword lookup

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/compiler/10.frontend/core/tokens.spl")

expect(src).to_contain("if kind == TOK_KW_KEYOF: return \"keyof\"")
expect(src).to_contain("if name == \"keyof\": return TOK_KW_KEYOF")
expect(src).to_contain("    TOK_IDENT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/keyof_token_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Keyof Token

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
