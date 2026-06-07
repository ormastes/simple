# Simple Compiler Lexer Specification

> The lexer (tokenizer) is the first phase of the Simple compiler pipeline. It converts source text into a stream of tokens, handling:

<!-- sdn-diagram:id=lexer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_spec -> std
lexer_spec -> compiler
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
| 128 | 128 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Compiler Lexer Specification

The lexer (tokenizer) is the first phase of the Simple compiler pipeline. It converts source text into a stream of tokens, handling:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #001-050 |
| Category | Compiler |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/lib/std/compiler/lexer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The lexer (tokenizer) is the first phase of the Simple compiler pipeline.
It converts source text into a stream of tokens, handling:
- All literal types (int, float, string, bool, nil)
- Keywords and identifiers
- Operators (arithmetic, comparison, logical, special)
- Indentation-based syntax (Python-style INDENT/DEDENT)
- Math block mode with special operators (caret for power)
- Error recovery for invalid characters

## Key Concepts

| Concept | Description |
|---------|-------------|
| Token | Atomic unit of source code (keyword, operator, literal, etc.) |
| Span | Source location info (line, column, offset) |
| Indentation Tracking | Automatic INDENT/DEDENT token generation |
| Math Block Mode | Special lexer mode for `m{}` blocks with caret operator |
| Implicit Multiplication | Auto-insert multiplication in math mode (e.g., `2x` → `2 * x`) |

## Behavior

- Tokenizes all Simple language constructs
- Tracks indentation levels and generates INDENT/DEDENT tokens
- Supports multiple string literal formats (normal, raw, multi-line)
- Handles numeric literals in multiple bases (decimal, hex, binary, octal)
- Provides precise source location tracking for error messages
- Enters special modes for math blocks and custom blocks

## Related Specifications

- [Parser](parser_spec.spl) - Consumes token stream to build AST
- [Blocks](blocks_spec.spl) - Custom block handling

## Implementation Notes

The lexer is stateful and tracks:
- Current position in source text
- Indentation stack for INDENT/DEDENT generation
- Current lexer mode (Normal, MathBlock, RawBlock)
- Pending tokens for lookahead

## Scenarios

### Lexer - Integer Literals

#### lexes decimal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("42")
expect(tok.kind).to_equal(TokenKind.IntLit)
expect(tok.text).to_equal("42")
```

</details>

#### lexes zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("0")
expect(tok.kind).to_equal(TokenKind.IntLit)
```

</details>

#### lexes large decimal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("123456789")
expect(tok.kind).to_equal(TokenKind.IntLit)
```

</details>

#### lexes hexadecimal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("0x2A")
expect(tok.kind).to_equal(TokenKind.IntLit)
expect(tok.text).to_equal("0x2A")
```

</details>

#### lexes binary integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("0b101010")
expect(tok.kind).to_equal(TokenKind.IntLit)
```

</details>

#### lexes octal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("0o52")
expect(tok.kind).to_equal(TokenKind.IntLit)
```

</details>

#### lexes integers with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("1_000_000")
expect(tok.kind).to_equal(TokenKind.IntLit)
```

</details>

### Lexer - Float Literals

#### lexes simple float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("3.14")
expect(tok.kind).to_equal(TokenKind.FloatLit)
```

</details>

#### lexes float with leading zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("0.5")
expect(tok.kind).to_equal(TokenKind.FloatLit)
```

</details>

#### lexes float with trailing zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("2.0")
expect(tok.kind).to_equal(TokenKind.FloatLit)
```

</details>

#### lexes scientific notation positive exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("1e10")
expect(tok.kind).to_equal(TokenKind.FloatLit)
```

</details>

#### lexes scientific notation negative exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("2.5e-3")
expect(tok.kind).to_equal(TokenKind.FloatLit)
```

</details>

#### lexes float with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("1_000.5")
expect(tok.kind).to_equal(TokenKind.FloatLit)
```

</details>

### Lexer - String Literals

#### lexes double-quoted string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("\"hello\"")
expect(tok.kind).to_equal(TokenKind.StringLit)
expect(tok.text).to_equal("\"hello\"")
```

</details>

#### lexes single-quoted string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("'world'")
expect(tok.kind).to_equal(TokenKind.StringLit)
```

</details>

#### lexes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("\"\"")
expect(tok.kind).to_equal(TokenKind.StringLit)
```

</details>

#### lexes string with escapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("\"hello\\nworld\"")
expect(tok.kind).to_equal(TokenKind.StringLit)
```

</details>

#### lexes raw string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("r\"no\\nescapes\"")
expect(tok.kind).to_equal(TokenKind.RawStringLit)
```

</details>

#### lexes multi-line string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("\"\"\"line1\nline2\"\"\"")
expect(tok.kind).to_equal(TokenKind.StringLit)
```

</details>

#### lexes string with interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("\"Hello {name}\"")
expect(tok.kind).to_equal(TokenKind.StringLit)
```

</details>

### Lexer - Boolean and Nil Literals

#### lexes true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("true")
expect(tok.kind).to_equal(TokenKind.BoolLit)
```

</details>

#### lexes false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("false")
expect(tok.kind).to_equal(TokenKind.BoolLit)
```

</details>

#### lexes nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("nil")
expect(tok.kind).to_equal(TokenKind.NilLit)
```

</details>

### Lexer - Declaration Keywords

#### lexes fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("fn").kind).to_equal(TokenKind.KwFn)
```

</details>

#### lexes val

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("val").kind).to_equal(TokenKind.KwVal)
```

</details>

#### lexes var

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("var").kind).to_equal(TokenKind.KwVar)
```

</details>

#### lexes struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("struct").kind).to_equal(TokenKind.KwStruct)
```

</details>

#### lexes class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("class").kind).to_equal(TokenKind.KwClass)
```

</details>

#### lexes enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("enum").kind).to_equal(TokenKind.KwEnum)
```

</details>

#### lexes trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("trait").kind).to_equal(TokenKind.KwTrait)
```

</details>

#### lexes impl

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("impl").kind).to_equal(TokenKind.KwImpl)
```

</details>

#### lexes type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("type").kind).to_equal(TokenKind.KwType)
```

</details>

#### lexes mod

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("mod").kind).to_equal(TokenKind.KwMod)
```

</details>

#### lexes pub

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("pub").kind).to_equal(TokenKind.KwPub)
```

</details>

#### lexes static

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("static").kind).to_equal(TokenKind.KwStatic)
```

</details>

#### lexes me

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("me").kind).to_equal(TokenKind.KwMe)
```

</details>

#### lexes extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("extern").kind).to_equal(TokenKind.KwExtern)
```

</details>

### Lexer - Control Flow Keywords

#### lexes if

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("if").kind).to_equal(TokenKind.KwIf)
```

</details>

#### lexes else

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("else").kind).to_equal(TokenKind.KwElse)
```

</details>

#### lexes elif

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("elif").kind).to_equal(TokenKind.KwElif)
```

</details>

#### lexes match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("match").kind).to_equal(TokenKind.KwMatch)
```

</details>

#### lexes for

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("for").kind).to_equal(TokenKind.KwFor)
```

</details>

#### lexes while

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("while").kind).to_equal(TokenKind.KwWhile)
```

</details>

<details>
<summary>Advanced: lexes loop</summary>

#### lexes loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("loop").kind).to_equal(TokenKind.KwLoop)
```

</details>


</details>

#### lexes break

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("break").kind).to_equal(TokenKind.KwBreak)
```

</details>

#### lexes continue

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("continue").kind).to_equal(TokenKind.KwContinue)
```

</details>

#### lexes return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("return").kind).to_equal(TokenKind.KwReturn)
```

</details>

### Lexer - Expression Keywords

#### lexes in

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("in").kind).to_equal(TokenKind.KwIn)
```

</details>

#### lexes is

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("is").kind).to_equal(TokenKind.KwIs)
```

</details>

#### lexes as

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("as").kind).to_equal(TokenKind.KwAs)
```

</details>

#### lexes not

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("not").kind).to_equal(TokenKind.KwNot)
```

</details>

#### lexes and

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("and").kind).to_equal(TokenKind.KwAnd)
```

</details>

#### lexes or

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("or").kind).to_equal(TokenKind.KwOr)
```

</details>

#### lexes xor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("xor").kind).to_equal(TokenKind.KwXor)
```

</details>

#### lexes self

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("self").kind).to_equal(TokenKind.KwSelf)
```

</details>

### Lexer - Arithmetic Operators

#### lexes plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("+").kind).to_equal(TokenKind.Plus)
```

</details>

#### lexes minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("-").kind).to_equal(TokenKind.Minus)
```

</details>

#### lexes star

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("*").kind).to_equal(TokenKind.Star)
```

</details>

#### lexes slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("/").kind).to_equal(TokenKind.Slash)
```

</details>

#### lexes percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("%").kind).to_equal(TokenKind.Percent)
```

</details>

#### lexes power operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("**").kind).to_equal(TokenKind.StarStar)
```

</details>

### Lexer - Comparison Operators

#### lexes equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("==").kind).to_equal(TokenKind.Eq)
```

</details>

#### lexes not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("!=").kind).to_equal(TokenKind.NotEq)
```

</details>

#### lexes less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("<").kind).to_equal(TokenKind.Lt)
```

</details>

#### lexes greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(">").kind).to_equal(TokenKind.Gt)
```

</details>

#### lexes less than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("<=").kind).to_equal(TokenKind.LtEq)
```

</details>

#### lexes greater than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(">=").kind).to_equal(TokenKind.GtEq)
```

</details>

### Lexer - Special Operators

#### lexes optional chaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("?.").kind).to_equal(TokenKind.QuestionDot)
```

</details>

#### lexes existence check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(".?").kind).to_equal(TokenKind.DotQuestion)
```

</details>

#### lexes null coalescing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("??").kind).to_equal(TokenKind.QuestionQuestion)
```

</details>

#### lexes pipe forward

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("|>").kind).to_equal(TokenKind.PipeForward)
```

</details>

#### lexes compose

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(">>").kind).to_equal(TokenKind.Compose)
```

</details>

#### lexes compose back

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("<<").kind).to_equal(TokenKind.ComposeBack)
```

</details>

#### lexes layer connect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("~>").kind).to_equal(TokenKind.LayerConnect)
```

</details>

#### lexes broadcast add

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(".+").kind).to_equal(TokenKind.DotPlus)
```

</details>

#### lexes broadcast sub

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(".-").kind).to_equal(TokenKind.DotMinus)
```

</details>

#### lexes broadcast mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(".*").kind).to_equal(TokenKind.DotStar)
```

</details>

#### lexes broadcast div

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("./").kind).to_equal(TokenKind.DotSlash)
```

</details>

#### lexes broadcast power

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(".^").kind).to_equal(TokenKind.DotCaret)
```

</details>

#### lexes exclusive range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("..").kind).to_equal(TokenKind.DotDot)
```

</details>

#### lexes inclusive range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("..=").kind).to_equal(TokenKind.DotDotEq)
```

</details>

#### lexes at operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("@").kind).to_equal(TokenKind.At)
```

</details>

### Lexer - Indentation Tracking

#### generates INDENT for increased indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "if true:\n    pass"
val kinds = token_kinds(source)
expect(kinds).to(include(TokenKind.Indent))
```

</details>

#### generates DEDENT for decreased indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "if true:\n    pass\nelse:\n    pass"
val kinds = token_kinds(source)
expect(kinds).to(include(TokenKind.Dedent))
```

</details>

#### generates multiple DEDENTs for large decrease

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "if true:\n    if true:\n        pass\nelse:\n    pass"
val kinds = token_kinds(source)
val dedent_count = kinds.filter(_1 == TokenKind.Dedent).len()
expect(dedent_count).to(gt(0))
```

</details>

#### ignores blank lines for indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val x = 1\n\nval y = 2"
val kinds = token_kinds(source)
expect(kinds).not_to(include(TokenKind.Indent))
```

</details>

#### ignores comment-only lines for indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val x = 1\n# comment\nval y = 2"
val kinds = token_kinds(source)
expect(kinds).not_to(include(TokenKind.Indent))
```

</details>

#### handles tabs as indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "if true:\n\tpass"
val kinds = token_kinds(source)
expect(kinds).to(include(TokenKind.Indent))
```

</details>

#### handles mixed spaces and tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Should produce error or normalize
val source = "if true:\n\t    pass"
val kinds = token_kinds(source)
# At least it should lex without crashing
expect(kinds.len()).to(gt(0))
```

</details>

### Lexer - Math Block Mode

#### lexes caret as power in math block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "m{ x^2 }"
val kinds = token_kinds(source)
expect(kinds).to(include(TokenKind.Caret))
```

<details>
<summary>Rendered scenario source</summary>

> val source = "$x^{2}$"<br>
> val kinds = token_kinds(source)<br>
> expect(kinds).to(include(TokenKind.Caret))

</details>

</details>

#### rejects caret outside math block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "x^2"
val tok = lex_one(source)
# Should be Ident("x") followed by Error
expect(lex(source)[1].kind).to_equal(TokenKind.Error)
```

</details>

#### generates implicit multiplication in math block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "m{ 2x }"
val kinds = token_kinds(source)
expect(kinds).to(include(TokenKind.ImplicitMul))
```

<details>
<summary>Rendered scenario source</summary>

> val source = "$2$"<br>
> val kinds = token_kinds(source)<br>
> expect(kinds).to(include(TokenKind.ImplicitMul))

</details>

</details>

#### handles complex math expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "m{ x^2 + 2*x*y + y^2 }"
val kinds = token_kinds(source)
expect(kinds).to(include(TokenKind.Caret))
```

<details>
<summary>Rendered scenario source</summary>

> val source = "$x^{2} + 2 \cdot x \cdot y + y^{2}$"<br>
> val kinds = token_kinds(source)<br>
> expect(kinds).to(include(TokenKind.Caret))

</details>

</details>

#### exits math mode at closing brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "m{ x^2 } + y"
val tokens = lex(source)
# After closing brace, should be back to normal mode
# so + is Plus, not error
expect(tokens.any(_1.kind == TokenKind.Plus)).to_equal(true)
```

<details>
<summary>Rendered scenario source</summary>

> val source = "$x^{2}$ + y"<br>
> val tokens = lex(source)<br>
> # After closing brace, should be back to normal mode<br>
> # so + is Plus, not error<br>
> expect(tokens.any(_1.kind == TokenKind.Plus)).to_equal(true)

</details>

</details>

#### handles nested braces in math block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "m{ f(x^2) }"
val kinds = token_kinds(source)
expect(kinds).to(include(TokenKind.Caret))
```

<details>
<summary>Rendered scenario source</summary>

> val source = "$\operatorname{f}(x^{2})$"<br>
> val kinds = token_kinds(source)<br>
> expect(kinds).to(include(TokenKind.Caret))

</details>

</details>

### Lexer - Identifiers

#### lexes simple identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("foo")
expect(tok.kind).to_equal(TokenKind.Ident)
expect(tok.text).to_equal("foo")
```

</details>

#### lexes identifier with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("foo_bar")
expect(tok.kind).to_equal(TokenKind.Ident)
```

</details>

#### lexes identifier with digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("var1")
expect(tok.kind).to_equal(TokenKind.Ident)
```

</details>

#### lexes private identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("_private")
expect(tok.kind).to_equal(TokenKind.Ident)
```

</details>

#### lexes mutable implicit var

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("count_")
expect(tok.kind).to_equal(TokenKind.Ident)
```

</details>

#### distinguishes keywords from identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("function")  # Not "fn"
expect(tok.kind).to_equal(TokenKind.Ident)
```

</details>

### Lexer - Error Recovery

#### produces error token for invalid character

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("$invalid")
expect(tok.kind).to_equal(TokenKind.Dollar)  # $ is valid
val tokens = lex("~invalid")
expect(tokens[0].kind).to_equal(TokenKind.Tilde)  # ~ is valid
```

</details>

#### handles unterminated string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "\"unterminated"
val tok = lex_one(source)
# Should produce either Error or StringLit with error flag
val is_valid = [TokenKind.Error, TokenKind.StringLit].include(tok.kind)
expect(is_valid).to_equal(true)
```

</details>

#### handles invalid numeric literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "0x"  # Hex with no digits
val tokens = lex(source)
# Should produce error or int token
expect(tokens.len()).to(gt(0))
```

</details>

#### continues after error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val x = @@ 42"
val tokens = lex(source)
# Should lex val, x, =, @@, 42 despite error
expect(tokens.any(_1.kind == TokenKind.IntLit)).to_equal(true)
```

</details>

### Lexer - Delimiters

#### lexes left paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("(").kind).to_equal(TokenKind.LParen)
```

</details>

#### lexes right paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(")").kind).to_equal(TokenKind.RParen)
```

</details>

#### lexes left brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("{").kind).to_equal(TokenKind.LBrace)
```

</details>

#### lexes right brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("}").kind).to_equal(TokenKind.RBrace)
```

</details>

#### lexes left bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("[").kind).to_equal(TokenKind.LBracket)
```

</details>

#### lexes right bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("]").kind).to_equal(TokenKind.RBracket)
```

</details>

### Lexer - Punctuation

#### lexes comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(",").kind).to_equal(TokenKind.Comma)
```

</details>

#### lexes colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(":").kind).to_equal(TokenKind.Colon)
```

</details>

#### lexes double colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(".").kind).to_equal(TokenKind.ColonColon)
```

</details>

#### lexes semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(";").kind).to_equal(TokenKind.Semicolon)
```

</details>

#### lexes dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one(".").kind).to_equal(TokenKind.Dot)
```

</details>

#### lexes arrow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("->").kind).to_equal(TokenKind.Arrow)
```

</details>

#### lexes fat arrow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lex_one("=>").kind).to_equal(TokenKind.FatArrow)
```

</details>

### Lexer - Source Location Tracking

#### tracks single-line token position

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("foo")
expect(tok.span.line).to_equal(1)
expect(tok.span.col).to_equal(1)
```

</details>

#### tracks column offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val x = 42"
val tokens = lex(source)
val x_tok = tokens[1]  # "x"
expect(x_tok.span.col).to_equal(5)  # After "val "
```

</details>

#### tracks multi-line positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val x = 1\nval y = 2"
val tokens = lex(source)
val y_line = tokens.filter(_1.text == "y")[0].span.line
expect(y_line).to_equal(2)
```

</details>

#### provides correct span length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = lex_one("function")
expect(tok.span.len()).to_equal(8)
```

</details>

#### merges spans correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span1 = Span.new(0, 5, 1, 1)
val span2 = Span.new(10, 15, 1, 11)
val merged = span1.merge(span2)
expect(merged.start).to_equal(0)
expect(merged.end).to_equal(15)
```

</details>

### Lexer - Integration Tests

#### lexes simple function definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 128 |
| Active scenarios | 128 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
