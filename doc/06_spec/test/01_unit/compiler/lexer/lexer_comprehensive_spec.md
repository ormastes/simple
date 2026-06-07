# Lexer Comprehensive Specification

> <details>

<!-- sdn-diagram:id=lexer_comprehensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_comprehensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_comprehensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_comprehensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Comprehensive Specification

## Scenarios

### Lexer Comprehensive

#### defines public lexer wrapper and core lexer state

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = rt_file_read_text("src/compiler/10.frontend/core/lexer.spl")
val core = rt_file_read_text("src/compiler/10.frontend/core/lexer_struct.spl")

expect(lexer).to_contain("struct Lexer:")
expect(lexer).to_contain("fn lexer_new(source: text) -> Lexer:")
expect(lexer).to_contain("fn lexer_next_token(self: Lexer) -> Token:")
expect(lexer).to_contain("static fn new(source: text) -> Lexer:")
expect(lexer).to_contain("fn lex_init_with_path(source: text, source_path: text):")
expect(core).to_contain("struct CoreLexer:")
expect(core).to_contain("fn make_core_lexer(source: text) -> CoreLexer:")
expect(core).to_contain("indent_stack: [i64]")
expect(core).to_contain("pending_dedents: i64")
expect(core).to_contain("at_line_start: bool")
```

</details>

#### defines scanning paths for numbers, strings, identifiers, and tokens

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chars = rt_file_read_text("src/compiler/10.frontend/core/lexer_chars.spl")
val scanners = rt_file_read_text("src/compiler/10.frontend/core/lexer_scanners.spl")

expect(chars).to_contain("fn is_digit(c: text) -> bool:")
expect(chars).to_contain("fn is_hex_digit(c: text) -> bool:")
expect(chars).to_contain("fn is_alpha(c: text) -> bool:")
expect(chars).to_contain("fn is_ident_char(c: text) -> bool:")
expect(chars).to_contain("fn is_octal_digit(c: text) -> bool:")
expect(chars).to_contain("fn is_space(c: text) -> bool:")
expect(scanners).to_contain("fn lex_scan_number():")
expect(scanners).to_contain("fn lex_scan_string():")
expect(scanners).to_contain("fn lex_scan_ident():")
expect(scanners).to_contain("fn lex_handle_indentation():")
expect(scanners).to_contain("fn lex_scan_token():")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_comprehensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lexer Comprehensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
