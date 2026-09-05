# TokenKind Real Implementation Tests

> Tests for the actual TokenKind enum and its methods

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TokenKind Real Implementation Tests

Tests for the actual TokenKind enum and its methods

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-TOKEN-001 |
| Category | Parser \| Grammar |
| Status | Planned |
| Source | `test/01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the actual TokenKind enum and its methods
in std.parser.treesitter.simple_grammar.

NOTE: Tests are skipped until std.parser.treesitter module parse errors are fixed.

## Scenarios

### TokenKind Keywords

#### Fn is a keyword

- Fn is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Fn is a keyword")
expect true
```

</details>

#### Let is a keyword

- Let is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Let is a keyword")
expect true
```

</details>

#### Mut is a keyword

- Mut is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mut is a keyword")
expect true
```

</details>

#### Return is a keyword

- Return is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Return is a keyword")
expect true
```

</details>

#### If is a keyword

- If is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("If is a keyword")
expect true
```

</details>

#### Else is a keyword

- Else is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Else is a keyword")
expect true
```

</details>

#### Struct is a keyword

- Struct is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Struct is a keyword")
expect true
```

</details>

#### Class is a keyword

- Class is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Class is a keyword")
expect true
```

</details>

#### Match is a keyword

- Match is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Match is a keyword")
expect true
```

</details>

#### While is a keyword

- While is a keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("While is a keyword")
expect true
```

</details>

### TokenKind Literals

#### Integer is a literal

- Integer is a literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Integer is a literal")
expect true
```

</details>

#### Float is a literal

- Float is a literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Float is a literal")
expect true
```

</details>

#### String is a literal

- String is a literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("String is a literal")
expect true
```

</details>

#### Bool true is a literal

- Bool true is a literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bool true is a literal")
expect true
```

</details>

#### Bool false is a literal

- Bool false is a literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bool false is a literal")
expect true
```

</details>

#### Nil is a literal

- Nil is a literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Nil is a literal")
expect true
```

</details>

### TokenKind Identifiers

#### Identifier is an identifier

- Identifier is an identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Identifier is an identifier")
expect true
```

</details>

#### TypeIdentifier is an identifier

- TypeIdentifier is an identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TypeIdentifier is an identifier")
expect true
```

</details>

#### keywords are not identifiers

- keywords are not identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keywords are not identifiers")
expect true
```

</details>

### TokenKind Operators

#### Plus is an operator

- Plus is an operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Plus is an operator")
expect true
```

</details>

#### Minus is an operator

- Minus is an operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Minus is an operator")
expect true
```

</details>

#### Star is an operator

- Star is an operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Star is an operator")
expect true
```

</details>

#### Eq is an operator

- Eq is an operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Eq is an operator")
expect true
```

</details>

#### Arrow is an operator

- Arrow is an operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Arrow is an operator")
expect true
```

</details>

### TokenKind Delimiters

#### LParen is a delimiter

- LParen is a delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LParen is a delimiter")
expect true
```

</details>

#### RParen is a delimiter

- RParen is a delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RParen is a delimiter")
expect true
```

</details>

#### LBrace is a delimiter

- LBrace is a delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LBrace is a delimiter")
expect true
```

</details>

#### Comma is a delimiter

- Comma is a delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Comma is a delimiter")
expect true
```

</details>

#### Colon is a delimiter

- Colon is a delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Colon is a delimiter")
expect true
```

</details>

### TokenKind Special

#### Indent is special

- Indent is special


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Indent is special")
expect true
```

</details>

#### Dedent is special

- Dedent is special


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Dedent is special")
expect true
```

</details>

#### Newline is special

- Newline is special


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Newline is special")
expect true
```

</details>

### TokenKind Methods

#### is_keyword returns true for keywords

- is_keyword returns true for keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_keyword returns true for keywords")
expect true
```

</details>

#### is_literal returns true for literals

- is_literal returns true for literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_literal returns true for literals")
expect true
```

</details>

#### is_identifier returns true for identifiers

- is_identifier returns true for identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_identifier returns true for identifiers")
expect true
```

</details>

#### is_operator returns true for operators

- is_operator returns true for operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_operator returns true for operators")
expect true
```

</details>

#### is_delimiter returns true for delimiters

- is_delimiter returns true for delimiters


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_delimiter returns true for delimiters")
expect true
```

</details>

#### to_string converts to readable string

- to_string converts to readable string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_string converts to readable string")
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
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

- Canonical SPipe generation for source `f69b5fdce634029d68571dfe176909fb3fd0cd6c9aa564c8953bf33cd9ea8143`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f69b5fdce634029d68571dfe176909fb3fd0cd6c9aa564c8953bf33cd9ea8143`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f69b5fdce634029d68571dfe176909fb3fd0cd6c9aa564c8953bf33cd9ea8143`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/treesitter_tokenkind_real_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/treesitter_tokenkind_real_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/treesitter_tokenkind_real_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Fn is a keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Let is a keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Mut is a keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
