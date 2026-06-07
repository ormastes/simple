# Lexer New Specification

> <details>

<!-- sdn-diagram:id=lexer_new_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_new_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_new_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_new_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer New Specification

## Scenarios

### Lexer New

#### keeps public lexer construction and token iteration available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lexer_source()

expect(source).to_contain("struct Lexer:")
expect(source).to_contain("fn lexer_new(source: text) -> Lexer")
expect(source).to_contain("fn lexer_next_token(self: Lexer) -> Token")
expect(source).to_contain("static fn new(source: text) -> Lexer")
expect(source).to_contain("fn lex_next() -> i64")
expect(source).to_contain("fn lex_next_token_record() -> Token")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_new_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lexer New

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
