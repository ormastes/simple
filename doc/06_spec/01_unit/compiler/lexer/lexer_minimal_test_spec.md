# Lexer Minimal Test Specification

> <details>

<!-- sdn-diagram:id=lexer_minimal_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_minimal_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_minimal_test_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_minimal_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Minimal Test Specification

## Scenarios

### Lexer Minimal Test

#### keeps struct based core lexer creation available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lexer_struct_source()

expect(source).to_contain("struct CoreLexer:")
expect(source).to_contain("fn make_core_lexer(source: text) -> CoreLexer")
expect(source).to_contain("fn at_end() -> bool")
expect(source).to_contain("fn peek() -> text")
expect(source).to_contain("me advance() -> text")
expect(source).to_contain("me make_token(kind: i64, tok_text: text, start_line: i64, start_col: i64)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_minimal_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lexer Minimal Test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
