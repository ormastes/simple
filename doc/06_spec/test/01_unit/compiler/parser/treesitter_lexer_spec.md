# Treesitter Lexer Specification

> 1. check

<!-- sdn-diagram:id=treesitter_lexer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_lexer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_lexer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_lexer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Lexer Specification

## Scenarios

### Lexer

#### tokenizes empty source

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val tokens = lexer.tokenize_empty()
check(tokens.len() == 0)
```

</details>

#### tokenizes keywords

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val result = lexer.tokenize_keywords("val x = 42")
check(result)
```

</details>

#### tokenizes identifiers

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val tokens = lexer.tokenize_identifiers("foo")
check(tokens.len() > 0)
```

</details>

#### tokenizes numbers

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val tokens = lexer.tokenize_numbers("123")
check(tokens.len() > 0)
```

</details>

#### tokenizes strings

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val tokens = lexer.tokenize_strings("\"hello\"")
check(tokens.len() > 0)
```

</details>

#### tokenizes operators

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val tokens = lexer.tokenize_operators("+")
check(tokens.len() > 0)
```

</details>

#### handles whitespace

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val result = lexer.handle_whitespace("   x   ")
check(result)
```

</details>

#### handles comments

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lexer = MockLexer.new()
val result = lexer.handle_comments("# comment")
check(result)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_lexer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lexer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
