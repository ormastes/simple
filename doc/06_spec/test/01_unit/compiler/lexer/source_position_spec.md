# Source Position Specification

> <details>

<!-- sdn-diagram:id=source_position_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=source_position_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

source_position_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=source_position_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Source Position Specification

## Scenarios

### Source Position

#### keeps source span and token structures available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lexer_types_source()

expect(source).to_contain("struct Span:")
expect(source).to_contain("start: i64")
expect(source).to_contain("end_pos: i64")
expect(source).to_contain("line: i64")
expect(source).to_contain("col: i64")
expect(source).to_contain("struct Token:")
```

</details>

#### keeps span and token helper constructors available

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lexer_types_source()

expect(source).to_contain("fn lex_span_new(start: i64, end_pos: i64, line: i64, col: i64) -> Span")
expect(source).to_contain("fn lex_span_empty() -> Span")
expect(source).to_contain("fn span_merge(a: Span, b: Span) -> Span")
expect(source).to_contain("fn span_len(s: Span) -> i64")
expect(source).to_contain("fn lex_token_new(kind: i64, text: text, line: i64, col: i64) -> Token")
expect(source).to_contain("fn lex_token_eof(line: i64) -> Token")
expect(source).to_contain("fn lex_token_error(msg: text, line: i64, col: i64) -> Token")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/source_position_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Source Position

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
