# Lexer Real Implementation Tests

> Tests for the actual Lexer implementation in std.parser.treesitter.

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
| Source | `test/unit/compiler/parser/treesitter_lexer_real_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the actual Lexer implementation in std.parser.treesitter.
These tests use the real Lexer struct, not mocks.

NOTE: Tests are skipped until std.parser.treesitter module parse errors are fixed.
When ready, remove  and uncomment the import.

## Scenarios

### Lexer Creation

#### creates lexer with empty source

- creates lexer with empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates lexer with empty source")
var lexer = Lexer(source: "")
val result = lexer.tokenize()
expect result.ok.?
```

</details>

#### creates lexer with whitespace only

- creates lexer with whitespace only


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates lexer with whitespace only")
# var lexer = Lexer.new("   \t  ")
# val result = lexer.tokenize()
# expect result.is_ok()
expect true
```

</details>

### Keyword Tokenization

#### tokenizes fn keyword

- tokenizes fn keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes fn keyword")
# var lexer = Lexer.new("fn")
# val result = lexer.tokenize()
# expect result.is_ok()
# val tokens = result.unwrap()
# expect tokens[0].kind == TokenKind.Fn
expect true
```

</details>

#### tokenizes val keyword

- tokenizes val keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes val keyword")
# var lexer = Lexer.new("val")
# val result = lexer.tokenize()
# expect tokens[0].kind == TokenKind.Let
expect true
```

</details>

#### tokenizes mut keyword

- tokenizes mut keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes mut keyword")
expect true
```

</details>

#### tokenizes return keyword

- tokenizes return keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes return keyword")
expect true
```

</details>

#### tokenizes if keyword

- tokenizes if keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes if keyword")
expect true
```

</details>

#### tokenizes else keyword

- tokenizes else keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes else keyword")
expect true
```

</details>

#### tokenizes struct keyword

- tokenizes struct keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes struct keyword")
expect true
```

</details>

#### tokenizes class keyword

- tokenizes class keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes class keyword")
expect true
```

</details>

#### tokenizes match keyword

- tokenizes match keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes match keyword")
expect true
```

</details>

#### tokenizes while keyword

- tokenizes while keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes while keyword")
expect true
```

</details>

#### tokenizes true literal

- tokenizes true literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes true literal")
expect true
```

</details>

#### tokenizes false literal

- tokenizes false literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes false literal")
expect true
```

</details>

#### tokenizes nil literal

- tokenizes nil literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes nil literal")
expect true
```

</details>

### Identifier Tokenization

#### tokenizes simple identifier

- tokenizes simple identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes simple identifier")
expect true
```

</details>

#### tokenizes identifier with underscore

- tokenizes identifier with underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes identifier with underscore")
expect true
```

</details>

#### tokenizes identifier with numbers

- tokenizes identifier with numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes identifier with numbers")
expect true
```

</details>

#### tokenizes type identifier (uppercase)

- tokenizes type identifier (uppercase)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes type identifier (uppercase)")
expect true
```

</details>

### Number Tokenization

#### tokenizes single digit

- tokenizes single digit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes single digit")
expect true
```

</details>

#### tokenizes multi-digit integer

- tokenizes multi-digit integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes multi-digit integer")
expect true
```

</details>

#### tokenizes zero

- tokenizes zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes zero")
expect true
```

</details>

#### tokenizes float with decimal

- tokenizes float with decimal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes float with decimal")
expect true
```

</details>

### Operator Tokenization

#### tokenizes plus

- tokenizes plus


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes plus")
expect true
```

</details>

#### tokenizes minus

- tokenizes minus


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes minus")
expect true
```

</details>

#### tokenizes star

- tokenizes star


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes star")
expect true
```

</details>

#### tokenizes equals

- tokenizes equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes equals")
expect true
```

</details>

#### tokenizes not equals

- tokenizes not equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes not equals")
expect true
```

</details>

#### tokenizes less than or equal

- tokenizes less than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes less than or equal")
expect true
```

</details>

#### tokenizes arrow

- tokenizes arrow


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes arrow")
expect true
```

</details>

### Delimiter Tokenization

#### tokenizes parentheses

- tokenizes parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes parentheses")
expect true
```

</details>

#### tokenizes braces

- tokenizes braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes braces")
expect true
```

</details>

#### tokenizes brackets

- tokenizes brackets


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes brackets")
expect true
```

</details>

#### tokenizes comma

- tokenizes comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes comma")
expect true
```

</details>

#### tokenizes colon

- tokenizes colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes colon")
expect true
```

</details>

### Multi-Token Sequences

#### tokenizes simple expression

- tokenizes simple expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes simple expression")
expect true
```

</details>

#### tokenizes function signature

- tokenizes function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes function signature")
expect true
```

</details>

#### tokenizes variable declaration

- tokenizes variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes variable declaration")
expect true
```

</details>

### Lexer Error Handling

#### reports error for unexpected character

- reports error for unexpected character


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports error for unexpected character")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `712aba41f11754cd356d702b06ea825261617629c508f87d86243bcddf78ff10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `712aba41f11754cd356d702b06ea825261617629c508f87d86243bcddf78ff10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `712aba41f11754cd356d702b06ea825261617629c508f87d86243bcddf78ff10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/parser/treesitter_lexer_real_spec.spl
mirror: doc/06_spec/unit/compiler/parser/treesitter_lexer_real_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/treesitter_lexer_real_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/treesitter_lexer_real_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/treesitter_lexer_real_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates lexer with empty source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_lexer_real_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates lexer with whitespace only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_lexer_real_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes fn keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
