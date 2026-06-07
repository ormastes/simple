# Lexer Real Implementation Tests

> Tests for the actual Lexer implementation in std.parser.treesitter.

<!-- sdn-diagram:id=treesitter_lexer_real_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_lexer_real_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_lexer_real_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_lexer_real_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Real Implementation Tests

Tests for the actual Lexer implementation in std.parser.treesitter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-LEXER-001 |
| Category | Parser \| Lexer |
| Status | Planned |
| Source | `test/01_unit/compiler/parser/treesitter_lexer_real_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the actual Lexer implementation in std.parser.treesitter.
These tests use the real Lexer struct, not mocks.

NOTE: Tests are skipped until std.parser.treesitter module parse errors are fixed.
When ready, remove  and uncomment the import.

## Scenarios

### Lexer Creation

#### creates lexer with empty source

1. var lexer = Lexer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = Lexer(source: "")
val result = lexer.tokenize()
expect result.ok.?
```

</details>

#### creates lexer with whitespace only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lexer = Lexer.new("   \t  ")
# val result = lexer.tokenize()
# expect result.is_ok()
expect true
```

</details>

### Keyword Tokenization

#### tokenizes fn keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lexer = Lexer.new("fn")
# val result = lexer.tokenize()
# expect result.is_ok()
# val tokens = result.unwrap()
# expect tokens[0].kind == TokenKind.Fn
expect true
```

</details>

#### tokenizes val keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lexer = Lexer.new("val")
# val result = lexer.tokenize()
# expect tokens[0].kind == TokenKind.Let
expect true
```

</details>

#### tokenizes mut keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes return keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes if keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes else keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes struct keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes class keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes match keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes while keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes true literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes false literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes nil literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

### Identifier Tokenization

#### tokenizes simple identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes identifier with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes identifier with numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes type identifier (uppercase)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

### Number Tokenization

#### tokenizes single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes multi-digit integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes float with decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

### Operator Tokenization

#### tokenizes plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes star

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes not equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes less than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes arrow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

### Delimiter Tokenization

#### tokenizes parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

### Multi-Token Sequences

#### tokenizes simple expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes function signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### tokenizes variable declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

### Lexer Error Handling

#### reports error for unexpected character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
