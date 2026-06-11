# HTML Tokenizer Specification

> Tests for `tokenize_html` — the first stage of the Blink HTML parser port. Covers the happy-path WHATWG states: Data, TagOpen, EndTag, TagName, BeforeAttributeName, AttributeName, AttributeValue, Comment, and Doctype. The tree builder consumes this stream; it is out of scope for this spec.

<!-- sdn-diagram:id=html_tokenizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_tokenizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_tokenizer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_tokenizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Tokenizer Specification

Tests for `tokenize_html` — the first stage of the Blink HTML parser port. Covers the happy-path WHATWG states: Data, TagOpen, EndTag, TagName, BeforeAttributeName, AttributeName, AttributeValue, Comment, and Doctype. The tree builder consumes this stream; it is out of scope for this spec.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BLK-HTML-TOK-001 |
| Category | Browser / Blink port |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/blink/html_tokenizer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `tokenize_html` — the first stage of the Blink HTML parser port.
Covers the happy-path WHATWG states: Data, TagOpen, EndTag, TagName,
BeforeAttributeName, AttributeName, AttributeValue, Comment, and Doctype.
The tree builder consumes this stream; it is out of scope for this spec.

## Scenarios

### html_tokenizer

#### tokenize_html: empty string produces [Eof]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("")
expect(toks.len()).to_equal(1)
expect(toks[0].kind == HtmlTokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_html: plain text \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("hello")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == HtmlTokenKind.Character).to_equal(true)
expect(toks[0].data).to_equal("hello")
expect(toks[1].kind == HtmlTokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_html: \

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("<div>")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == HtmlTokenKind.StartTag).to_equal(true)
expect(toks[0].name).to_equal("div")
expect(toks[0].self_closing).to_equal(false)
expect(toks[1].kind == HtmlTokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_html: \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("</div>")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == HtmlTokenKind.EndTag).to_equal(true)
expect(toks[0].name).to_equal("div")
expect(toks[1].kind == HtmlTokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_html: \

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("<br/>")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == HtmlTokenKind.StartTag).to_equal(true)
expect(toks[0].name).to_equal("br")
expect(toks[0].self_closing).to_equal(true)
expect(toks[1].kind == HtmlTokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_html: '<a href=\

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("<a href=\"x.com\">")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == HtmlTokenKind.StartTag).to_equal(true)
expect(toks[0].name).to_equal("a")
expect(toks[0].attributes.len()).to_equal(1)
expect(toks[0].attributes[0].name).to_equal("href")
expect(toks[0].attributes[0].value).to_equal("x.com")
expect(toks[1].kind == HtmlTokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_html: \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("<!-- comment -->")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == HtmlTokenKind.Comment).to_equal(true)
expect(toks[0].data.len()).to_be_greater_than(0)
expect(toks[1].kind == HtmlTokenKind.Eof).to_equal(true)
```

</details>

#### tokenize_html: \

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val toks = tokenize_html("<!DOCTYPE html>")
expect(toks.len()).to_equal(2)
expect(toks[0].kind == HtmlTokenKind.Doctype).to_equal(true)
expect(toks[0].name).to_equal("html")
expect(toks[1].kind == HtmlTokenKind.Eof).to_equal(true)
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
