# Lexer Specification

> <details>

<!-- sdn-diagram:id=lexer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Specification

## Scenarios

### Lexer

#### keeps lexer character classification helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lexer_source("lexer_chars.spl")

expect(source).to_contain("fn is_digit(c: text) -> bool")
expect(source).to_contain("fn is_hex_digit(c: text) -> bool")
expect(source).to_contain("fn is_alpha(c: text) -> bool")
expect(source).to_contain("fn is_ident_char(c: text) -> bool")
expect(source).to_contain("fn is_octal_digit(c: text) -> bool")
expect(source).to_contain("fn is_space(c: text) -> bool")
```

</details>

#### keeps lexer scanner dispatch helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lexer_source("lexer_scanners.spl")

expect(source).to_contain("fn lex_scan_number()")
expect(source).to_contain("fn lex_scan_string()")
expect(source).to_contain("fn lex_scan_ident()")
expect(source).to_contain("fn lex_skip_spaces()")
expect(source).to_contain("fn lex_handle_indentation()")
expect(source).to_contain("fn lex_scan_token()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lexer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
