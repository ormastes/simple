# Blink CSS Tokenizer Specification

> Tests for the minimal CSS Syntax Level 3 tokenizer. Covers the eight primary lexeme classes (Identifier, String, Number, AtKeyword, Hash, Delim, Comment, Eof) plus a whitespace-only empty-string sanity check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink CSS Tokenizer Specification

Tests for the minimal CSS Syntax Level 3 tokenizer. Covers the eight primary lexeme classes (Identifier, String, Number, AtKeyword, Hash, Delim, Comment, Eof) plus a whitespace-only empty-string sanity check.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/unit/lib/blink/css_tokenizer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the minimal CSS Syntax Level 3 tokenizer. Covers the eight
primary lexeme classes (Identifier, String, Number, AtKeyword, Hash,
Delim, Comment, Eof) plus a whitespace-only empty-string sanity check.

## Design notes mirrored by these tests

- Whitespace is skipped — no Whitespace token is emitted.
- Strings strip their delimiting quotes from `text`.
- AtKeywords strip the leading `@` from `text`.
- Hashes strip the leading `#` from `text`.
- Comments strip `/* ... */` delimiters from `text` and ARE emitted
  (not skipped) so downstream tooling can preserve source-map fidelity.

## Scenarios

### tokenize_css

#### empty string produces [Eof]

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty string produces [Eof]
   - Expected: tokens.len() equals `1`
   - Expected: is_eof is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string produces [Eof]")
val tokens = tokenize_css("")
expect(tokens.len()).to_equal(1)
val is_eof = tokens[0].kind == CssTokenKind.Eof
expect(is_eof).to_equal(true)
```

</details>

#### identifier \

- identifier \
   - Expected: is_ident is true
   - Expected: tokens[0].text equals `color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifier \")
val tokens = tokenize_css("color")
expect(tokens.len()).to_be_greater_than(1)
val is_ident = tokens[0].kind == CssTokenKind.Identifier
expect(is_ident).to_equal(true)
expect(tokens[0].text).to_equal("color")
```

</details>

#### number \

- number \
   - Expected: is_num is true
   - Expected: tokens[0].text equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number \")
val tokens = tokenize_css("42")
expect(tokens.len()).to_be_greater_than(1)
val is_num = tokens[0].kind == CssTokenKind.Number
expect(is_num).to_equal(true)
expect(tokens[0].text).to_equal("42")
```

</details>

#### string \

- string \
   - Expected: is_str is true
   - Expected: tokens[0].text equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string \")
val tokens = tokenize_css("'hello'")
expect(tokens.len()).to_be_greater_than(1)
val is_str = tokens[0].kind == CssTokenKind.String
expect(is_str).to_equal(true)
expect(tokens[0].text).to_equal("hello")
```

</details>

#### at-keyword \

- at-keyword \
   - Expected: is_at is true
   - Expected: tokens[0].text equals `media`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("at-keyword \")
val tokens = tokenize_css("@media")
expect(tokens.len()).to_be_greater_than(1)
val is_at = tokens[0].kind == CssTokenKind.AtKeyword
expect(is_at).to_equal(true)
expect(tokens[0].text).to_equal("media")
```

</details>

#### hash \

- hash \
   - Expected: is_hash is true
   - Expected: tokens[0].text equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hash \")
val tokens = tokenize_css("#abc")
expect(tokens.len()).to_be_greater_than(1)
val is_hash = tokens[0].kind == CssTokenKind.Hash
expect(is_hash).to_equal(true)
expect(tokens[0].text).to_equal("abc")
```

</details>

#### delim \

- delim \
   - Expected: is_delim is true
   - Expected: tokens[0].text equals `:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delim \")
val tokens = tokenize_css(":")
expect(tokens.len()).to_be_greater_than(1)
val is_delim = tokens[0].kind == CssTokenKind.Delim
expect(is_delim).to_equal(true)
expect(tokens[0].text).to_equal(":")
```

</details>

#### comment \

- comment \
   - Expected: is_comment is true
   - Expected: tokens[0].text equals ` hi `


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comment \")
val tokens = tokenize_css("/* hi */")
expect(tokens.len()).to_be_greater_than(1)
val is_comment = tokens[0].kind == CssTokenKind.Comment
expect(is_comment).to_equal(true)
expect(tokens[0].text).to_equal(" hi ")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `c3e05733e435772447bdc8defa19673257575bfb720e054c80f9737cd9246605`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3e05733e435772447bdc8defa19673257575bfb720e054c80f9737cd9246605`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3e05733e435772447bdc8defa19673257575bfb720e054c80f9737cd9246605`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/blink/css_tokenizer_spec.spl
mirror: doc/06_spec/unit/lib/blink/css_tokenizer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/blink/css_tokenizer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/css_tokenizer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/css_tokenizer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/css_tokenizer_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty string produces [Eof]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/css_tokenizer_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifier \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/css_tokenizer_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'number \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
