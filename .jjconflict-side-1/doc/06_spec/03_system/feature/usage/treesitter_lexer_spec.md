# TreeSitter Lexer Specification

> use compiler.core.lexer.{Lexer, lexer_new, lexer_next_token, Token, TokenKind}

<!-- sdn-diagram:id=treesitter_lexer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_lexer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_lexer_spec -> compiler
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
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Lexer Specification

use compiler.core.lexer.{Lexer, lexer_new, lexer_next_token, Token, TokenKind}

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-LEX-001 to #TS-LEX-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_lexer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use compiler.core.lexer.{Lexer, lexer_new, lexer_next_token, Token, TokenKind}

var lexer = lexer_new(source)
val token = lexer_next_token(lexer)
```

## Scenarios

### Core Lexer Keyword Tokenization

#### tokenizes fn keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("fn")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwFn
```

</details>

#### tokenizes val keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("val")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwVal
```

</details>

#### tokenizes var keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("var")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwVar
```

</details>

#### tokenizes if keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("if")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwIf
```

</details>

#### tokenizes struct keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("struct")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwStruct
```

</details>

#### tokenizes enum keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("enum")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwEnum
```

</details>

#### tokenizes impl keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("impl")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwImpl
```

</details>

#### tokenizes trait keyword

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("trait")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwTrait
```

</details>

### Core Lexer Identifier Tokenization

#### tokenizes simple identifier

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("foo")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Ident
```

</details>

#### tokenizes identifier with underscore

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("_bar")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Ident
```

</details>

#### tokenizes identifier with digits

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("foo123")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Ident
```

</details>

### Core Lexer Number Tokenization

#### tokenizes integer

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("42")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Integer
```

</details>

#### tokenizes float

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("3.14")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Float
```

</details>

#### tokenizes zero

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("0")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Integer
```

</details>

### Core Lexer Operator Tokenization

#### tokenizes plus

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("+")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Plus
```

</details>

#### tokenizes minus

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("-")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Minus
```

</details>

#### tokenizes star

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("*")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Star
```

</details>

#### tokenizes colon

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new(":")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Colon
```

</details>

#### tokenizes arrow

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("->")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Arrow
```

</details>

### Core Lexer Delimiter Tokenization

#### tokenizes left paren

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("(")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.LParen
```

</details>

#### tokenizes right paren

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new(")")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.RParen
```

</details>

#### tokenizes left brace

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("{")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.LBrace
```

</details>

#### tokenizes right brace

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("}")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.RBrace
```

</details>

#### tokenizes left bracket

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("[")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.LBracket
```

</details>

#### tokenizes right bracket

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("]")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.RBracket
```

</details>

### Core Lexer Multi-Token Sequence

#### tokenizes function signature

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("fn add(a: i64):")
val t1 = lexer_next_token(lexer)
expect t1.kind to_equal TokenKind.KwFn
val t2 = lexer_next_token(lexer)
expect t2.kind to_equal TokenKind.Ident
```

</details>

#### tokenizes variable declaration

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("val x = 42")
val t1 = lexer_next_token(lexer)
expect t1.kind to_equal TokenKind.KwVal
val t2 = lexer_next_token(lexer)
expect t2.kind to_equal TokenKind.Ident
```

</details>

### Core Lexer EOF Token

#### produces EOF for empty input

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Eof
```

</details>

#### produces EOF after all tokens consumed

1. var lexer = lexer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lexer = lexer_new("x")
val t1 = lexer_next_token(lexer)
val t2 = lexer_next_token(lexer)
expect t2.kind to_equal TokenKind.Eof
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
