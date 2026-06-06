# Lexer Import Debug Specification

> <details>

<!-- sdn-diagram:id=lexer_import_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_import_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_import_debug_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_import_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Import Debug Specification

## Scenarios

### Lexer Import Debug

#### documents the current lexer import surface

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = rt_file_read_text("src/compiler/10.frontend/core/lexer.spl")
val types = rt_file_read_text("src/compiler/10.frontend/core/lexer_types.spl")

expect(lexer).to_contain("use compiler.core.lexer_types.{Token, Span")
expect(lexer).to_contain("use compiler.frontend.core.lexer_struct.{CoreLexer, make_core_lexer")
expect(lexer).to_contain("use compiler.core.lexer_scanners.{lex_scan_number")
expect(types).to_contain("struct Span:")
expect(types).to_contain("struct Token:")
expect(types).to_contain("fn lex_token_new(kind: i64, text: text, line: i64, col: i64) -> Token:")
```

</details>

#### documents character helper imports used by lexer modules

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chars = rt_file_read_text("src/compiler/10.frontend/core/lexer_chars.spl")
val core = rt_file_read_text("src/compiler/10.frontend/core/lexer_struct.spl")

expect(core).to_contain("use compiler.core.lexer_chars.{is_digit")
expect(chars).to_contain("char_code")
expect(chars).to_contain("fn is_digit(c: text) -> bool:")
expect(chars).to_contain("fn is_ident_char(c: text) -> bool:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_import_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lexer Import Debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
