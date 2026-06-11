# Html Tokenizer Specification

> <details>

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
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Tokenizer Specification

## Scenarios

### HtmlTokenizer basic tags

#### AC-1: emits StartTag token for simple open tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = _first_start_tag("<p>hello</p>")
expect(tok.tag_name).to_equal("p")
```

</details>

#### AC-1: emits EndTag token for close tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = _first_end_tag("<p>hello</p>")
expect(tok.tag_name).to_equal("p")
```

</details>

#### AC-1: emits EOF as last token

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _has_eof("<p>text</p>")
expect(result).to_equal(true)
```

</details>

#### AC-1: tokenizes nested tags producing multiple start tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = _tokenize("<div><span>x</span></div>")
val count = _count_tokens("<div><span>x</span></div>")
expect(count).to_be_greater_than(3)
```

</details>

### HtmlTokenizer attributes

#### AC-1: parses single attribute name and value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = _first_start_tag("<a href=\"http://example.com\">")
val val_ = _attr_value(tok, "href")
expect(val_).to_equal("http://example.com")
```

</details>

#### AC-1: parses multiple attributes on one tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = _first_start_tag("<input type=\"text\" name=\"q\" value=\"\">")
val t = _attr_value(tok, "type")
expect(t).to_equal("text")
```

</details>

#### AC-1: parses boolean attribute (no value)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = _first_start_tag("<input disabled>")
val n = _attr_value(tok, "disabled")
expect(n).to_equal("")
```

</details>

### HtmlTokenizer self-closing tags

#### AC-1: sets self_closing flag for XHTML-style self-close

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = _first_start_tag("<br/>")
expect(tok.self_closing).to_equal(true)
```

</details>

#### AC-1: treats <img> as start tag regardless of no end tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tok = _first_start_tag("<img src=\"a.png\">")
expect(tok.tag_name).to_equal("img")
```

</details>

### HtmlTokenizer character data

#### AC-1: emits Character token for text content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = _has_character_token("<p>hello</p>")
expect(found).to_equal(true)
```

</details>

#### AC-1: emits Character for &amp; named entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val txt = _first_char_token_data("<p>&amp;</p>")
expect(txt).to_equal("&")
```

</details>

#### AC-1: decodes common named entities to Unicode characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_first_char_token_data("<p>&copy;</p>")).to_equal(text.from_char_code(169))
expect(_first_char_token_data("<p>&nbsp;</p>")).to_equal(text.from_char_code(160))
expect(_first_char_token_data("<p>&mdash;</p>")).to_equal(text.from_char_code(8212))
expect(_first_char_token_data("<p>&hellip;</p>")).to_equal(text.from_char_code(8230))
```

</details>

#### AC-1: decodes decimal numeric character references

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val txt = _first_char_token_data("<p>&#65;</p>")
expect(txt).to_equal("A")
```

</details>

#### AC-1: decodes hexadecimal numeric character references

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val txt = _first_char_token_data("<p>&#x41;</p>")
expect(txt).to_equal("A")
```

</details>

#### AC-1: replaces invalid numeric character references

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val txt = _first_char_token_data("<p>&#0;</p>")
expect(txt).to_equal(text.from_char_code(65533))
```

</details>

### HtmlTokenizer script and raw text states

#### AC-1: treats content of <script> as raw text not tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = _tokenize("<script>var x = '<p>';</script>")
var inner_start_count = 0
var i = 0
while i < tokens.len():
    val tok = tokens[i]
    if tok.token_kind == HtmlTokenKind.StartTag:
        if tok.tag_name == "p":
            inner_start_count = inner_start_count + 1
    i = i + 1
expect(inner_start_count).to_equal(0)
```

</details>

#### AC-1: treats content of <style> as raw text

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = _tokenize("<style>a > b { color: red; }</style>")
var gt_tag_count = 0
var i = 0
while i < tokens.len():
    val tok = tokens[i]
    if tok.token_kind == HtmlTokenKind.StartTag:
        if tok.tag_name == "b":
            gt_tag_count = gt_tag_count + 1
    i = i + 1
expect(gt_tag_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/html_tokenizer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HtmlTokenizer basic tags
- HtmlTokenizer attributes
- HtmlTokenizer self-closing tags
- HtmlTokenizer character data
- HtmlTokenizer script and raw text states

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
