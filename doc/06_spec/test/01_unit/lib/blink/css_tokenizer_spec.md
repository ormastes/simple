# Blink CSS Tokenizer Specification

> Tests for the minimal CSS Syntax Level 3 tokenizer. Covers the eight primary lexeme classes (Identifier, String, Number, AtKeyword, Hash, Delim, Comment, Eof) plus a whitespace-only empty-string sanity check.

<!-- sdn-diagram:id=css_tokenizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=css_tokenizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

css_tokenizer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=css_tokenizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/blink/css_tokenizer_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize_css("")
expect(tokens.len()).to_equal(1)
val is_eof = tokens[0].kind == CssTokenKind.Eof
expect(is_eof).to_equal(true)
```

</details>

#### identifier \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize_css("color")
expect(tokens.len()).to_be_greater_than(1)
val is_ident = tokens[0].kind == CssTokenKind.Identifier
expect(is_ident).to_equal(true)
expect(tokens[0].text).to_equal("color")
```

</details>

#### number \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize_css("42")
expect(tokens.len()).to_be_greater_than(1)
val is_num = tokens[0].kind == CssTokenKind.Number
expect(is_num).to_equal(true)
expect(tokens[0].text).to_equal("42")
```

</details>

#### string \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize_css("'hello'")
expect(tokens.len()).to_be_greater_than(1)
val is_str = tokens[0].kind == CssTokenKind.String
expect(is_str).to_equal(true)
expect(tokens[0].text).to_equal("hello")
```

</details>

#### at-keyword \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize_css("@media")
expect(tokens.len()).to_be_greater_than(1)
val is_at = tokens[0].kind == CssTokenKind.AtKeyword
expect(is_at).to_equal(true)
expect(tokens[0].text).to_equal("media")
```

</details>

#### hash \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize_css("#abc")
expect(tokens.len()).to_be_greater_than(1)
val is_hash = tokens[0].kind == CssTokenKind.Hash
expect(is_hash).to_equal(true)
expect(tokens[0].text).to_equal("abc")
```

</details>

#### delim \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize_css(":")
expect(tokens.len()).to_be_greater_than(1)
val is_delim = tokens[0].kind == CssTokenKind.Delim
expect(is_delim).to_equal(true)
expect(tokens[0].text).to_equal(":")
```

</details>

#### comment \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
