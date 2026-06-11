# SkSL Tokenizer Specification

> Tests for `tokenize_sksl` — the lexical analyzer that turns SkSL source text into a token stream for the future SkRuntimeEffect frontend. Covers identifiers, keywords, int/float literals, operators, line comments, and a small end-to-end shader fragment.

<!-- sdn-diagram:id=sksl_tokenizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sksl_tokenizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sksl_tokenizer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sksl_tokenizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SkSL Tokenizer Specification

Tests for `tokenize_sksl` — the lexical analyzer that turns SkSL source text into a token stream for the future SkRuntimeEffect frontend. Covers identifiers, keywords, int/float literals, operators, line comments, and a small end-to-end shader fragment.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-SKSL-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/sksl_tokenizer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `tokenize_sksl` — the lexical analyzer that turns SkSL source
text into a token stream for the future SkRuntimeEffect frontend. Covers
identifiers, keywords, int/float literals, operators, line comments, and
a small end-to-end shader fragment.

## Scenarios

### sksl_tokenizer

#### tokenize_sksl: empty string returns [Eof]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("")
expect(toks.len()).to_equal(1)
expect(toks[0].kind == TokenKind.Eof).to_equal(true)
expect(toks[0].text).to_equal("")
```

</details>

#### tokenize_sksl: single identifier \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("foo")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == TokenKind.Identifier).to_equal(true)
expect(toks[0].text).to_equal("foo")
expect(toks[1].kind == TokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_sksl: keyword \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("uniform")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == TokenKind.Keyword).to_equal(true)
expect(toks[0].text).to_equal("uniform")
expect(toks[1].kind == TokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_sksl: integer literal \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("42")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == TokenKind.IntLiteral).to_equal(true)
expect(toks[0].text).to_equal("42")
expect(toks[1].kind == TokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_sksl: float literal \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("3.14")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == TokenKind.FloatLiteral).to_equal(true)
expect(toks[0].text).to_equal("3.14")
expect(toks[1].kind == TokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_sksl: operator \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("==")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == TokenKind.Operator).to_equal(true)
expect(toks[0].text).to_equal("==")
expect(toks[1].kind == TokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_sksl: line comment \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("// hi\nfoo")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == TokenKind.Identifier).to_equal(true)
expect(toks[0].text).to_equal("foo")
expect(toks[1].kind == TokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_sksl: simple shader \

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_sksl("void main() { return; }")
# void Keyword, main Identifier, ( Punct, ) Punct, { Punct,
# return Keyword, ; Punct, } Punct, Eof  => 9 total (>= 7 non-Eof)
expect(toks.len()).to_be_greater_than(6)
expect(toks[0].kind == TokenKind.Keyword).to_equal(true)
expect(toks[0].text).to_equal("void")
expect(toks[1].kind == TokenKind.Identifier).to_equal(true)
expect(toks[1].text).to_equal("main")
val last = toks[toks.len() - 1]
expect(last.kind == TokenKind.Eof).to_equal(true)
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
