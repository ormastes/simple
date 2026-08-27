# TreeSitter Lexer Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Lexer Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-LEX-001 to #TS-LEX-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_lexer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use std.spec.step

use compiler.core.lexer.{Lexer, lexer_new, lexer_next_token, Token, TokenKind}

var lexer = lexer_new(source)
val token = lexer_next_token(lexer)
```

## Scenarios

### Core Lexer Keyword Tokenization

#### tokenizes fn keyword

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenizes fn keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes fn keyword")
var lexer = lexer_new("fn")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwFn
```

</details>

#### tokenizes val keyword

- tokenizes val keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes val keyword")
var lexer = lexer_new("val")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwVal
```

</details>

#### tokenizes var keyword

- tokenizes var keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes var keyword")
var lexer = lexer_new("var")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwVar
```

</details>

#### tokenizes if keyword

- tokenizes if keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes if keyword")
var lexer = lexer_new("if")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwIf
```

</details>

#### tokenizes struct keyword

- tokenizes struct keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes struct keyword")
var lexer = lexer_new("struct")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwStruct
```

</details>

#### tokenizes enum keyword

- tokenizes enum keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes enum keyword")
var lexer = lexer_new("enum")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwEnum
```

</details>

#### tokenizes impl keyword

- tokenizes impl keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes impl keyword")
var lexer = lexer_new("impl")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwImpl
```

</details>

#### tokenizes trait keyword

- tokenizes trait keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes trait keyword")
var lexer = lexer_new("trait")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.KwTrait
```

</details>

### Core Lexer Identifier Tokenization

#### tokenizes simple identifier

- tokenizes simple identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes simple identifier")
var lexer = lexer_new("foo")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Ident
```

</details>

#### tokenizes identifier with underscore

- tokenizes identifier with underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes identifier with underscore")
var lexer = lexer_new("_bar")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Ident
```

</details>

#### tokenizes identifier with digits

- tokenizes identifier with digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes identifier with digits")
var lexer = lexer_new("foo123")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Ident
```

</details>

### Core Lexer Number Tokenization

#### tokenizes integer

- tokenizes integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes integer")
var lexer = lexer_new("42")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Integer
```

</details>

#### tokenizes float

- tokenizes float


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes float")
var lexer = lexer_new("3.14")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Float
```

</details>

#### tokenizes zero

- tokenizes zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes zero")
var lexer = lexer_new("0")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Integer
```

</details>

### Core Lexer Operator Tokenization

#### tokenizes plus

- tokenizes plus


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes plus")
var lexer = lexer_new("+")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Plus
```

</details>

#### tokenizes minus

- tokenizes minus


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes minus")
var lexer = lexer_new("-")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Minus
```

</details>

#### tokenizes star

- tokenizes star


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes star")
var lexer = lexer_new("*")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Star
```

</details>

#### tokenizes colon

- tokenizes colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes colon")
var lexer = lexer_new(":")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Colon
```

</details>

#### tokenizes arrow

- tokenizes arrow


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes arrow")
var lexer = lexer_new("->")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Arrow
```

</details>

### Core Lexer Delimiter Tokenization

#### tokenizes left paren

- tokenizes left paren


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes left paren")
var lexer = lexer_new("(")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.LParen
```

</details>

#### tokenizes right paren

- tokenizes right paren


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes right paren")
var lexer = lexer_new(")")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.RParen
```

</details>

#### tokenizes left brace

- tokenizes left brace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes left brace")
var lexer = lexer_new("{")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.LBrace
```

</details>

#### tokenizes right brace

- tokenizes right brace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes right brace")
var lexer = lexer_new("}")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.RBrace
```

</details>

#### tokenizes left bracket

- tokenizes left bracket


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes left bracket")
var lexer = lexer_new("[")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.LBracket
```

</details>

#### tokenizes right bracket

- tokenizes right bracket


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes right bracket")
var lexer = lexer_new("]")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.RBracket
```

</details>

### Core Lexer Multi-Token Sequence

#### tokenizes function signature

- tokenizes function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes function signature")
var lexer = lexer_new("fn add(a: i64):")
val t1 = lexer_next_token(lexer)
expect t1.kind to_equal TokenKind.KwFn
val t2 = lexer_next_token(lexer)
expect t2.kind to_equal TokenKind.Ident
```

</details>

#### tokenizes variable declaration

- tokenizes variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tokenizes variable declaration")
var lexer = lexer_new("val x = 42")
val t1 = lexer_next_token(lexer)
expect t1.kind to_equal TokenKind.KwVal
val t2 = lexer_next_token(lexer)
expect t2.kind to_equal TokenKind.Ident
```

</details>

### Core Lexer EOF Token

#### produces EOF for empty input

- produces EOF for empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("produces EOF for empty input")
var lexer = lexer_new("")
val token = lexer_next_token(lexer)
expect token.kind to_equal TokenKind.Eof
```

</details>

#### produces EOF after all tokens consumed

- produces EOF after all tokens consumed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("produces EOF after all tokens consumed")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c590581287abe0cdd21a469703419f1e55dc0687542275a2b16b379c7672531`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c590581287abe0cdd21a469703419f1e55dc0687542275a2b16b379c7672531`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c590581287abe0cdd21a469703419f1e55dc0687542275a2b16b379c7672531`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/treesitter_lexer_spec.spl
mirror: doc/06_spec/feature/usage/treesitter_lexer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/treesitter_lexer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/treesitter_lexer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/treesitter_lexer_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes fn keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_lexer_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes val keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_lexer_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes var keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
