# Html Tokenizer Specification

> Tests covering HtmlTokenizer basic tags, HtmlTokenizer attributes, HtmlTokenizer self-closing tags, HtmlTokenizer character data, HtmlTokenizer script and raw text states.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Tokenizer Specification

## Scenarios

### HtmlTokenizer basic tags

#### AC-1: emits StartTag token for simple open tag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-1: emits StartTag token for simple open tag
   - Expected: tok.tag_name equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: emits StartTag token for simple open tag")
val tok = _first_start_tag("<p>hello</p>")
expect(tok.tag_name).to_equal("p")
```

</details>

#### AC-1: emits EndTag token for close tag

- AC-1: emits EndTag token for close tag
   - Expected: tok.tag_name equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: emits EndTag token for close tag")
val tok = _first_end_tag("<p>hello</p>")
expect(tok.tag_name).to_equal("p")
```

</details>

#### AC-1: emits EOF as last token

- AC-1: emits EOF as last token
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: emits EOF as last token")
val result = _has_eof("<p>text</p>")
expect(result).to_equal(true)
```

</details>

#### AC-1: tokenizes nested tags producing multiple start tokens

- AC-1: tokenizes nested tags producing multiple start tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: tokenizes nested tags producing multiple start tokens")
val tokens = _tokenize("<div><span>x</span></div>")
val count = _count_tokens("<div><span>x</span></div>")
expect(count).to_be_greater_than(3)
```

</details>

### HtmlTokenizer attributes

#### AC-1: parses single attribute name and value

- AC-1: parses single attribute name and value
   - Expected: val_ equals `http://example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: parses single attribute name and value")
val tok = _first_start_tag("<a href=\"http://example.com\">")
val val_ = _attr_value(tok, "href")
expect(val_).to_equal("http://example.com")
```

</details>

#### AC-1: parses multiple attributes on one tag

- AC-1: parses multiple attributes on one tag
   - Expected: t equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: parses multiple attributes on one tag")
val tok = _first_start_tag("<input type=\"text\" name=\"q\" value=\"\">")
val t = _attr_value(tok, "type")
expect(t).to_equal("text")
```

</details>

#### AC-1: parses boolean attribute (no value)

- AC-1: parses boolean attribute (no value)
   - Expected: n equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: parses boolean attribute (no value)")
val tok = _first_start_tag("<input disabled>")
val n = _attr_value(tok, "disabled")
expect(n).to_equal("")
```

</details>

### HtmlTokenizer self-closing tags

#### AC-1: sets self_closing flag for XHTML-style self-close

- AC-1: sets self_closing flag for XHTML-style self-close
   - Expected: tok.self_closing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: sets self_closing flag for XHTML-style self-close")
val tok = _first_start_tag("<br/>")
expect(tok.self_closing).to_equal(true)
```

</details>

#### AC-1: treats <img> as start tag regardless of no end tag

- AC-1: treats <img> as start tag regardless of no end tag
   - Expected: tok.tag_name equals `img`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: treats <img> as start tag regardless of no end tag")
val tok = _first_start_tag("<img src=\"a.png\">")
expect(tok.tag_name).to_equal("img")
```

</details>

### HtmlTokenizer character data

#### AC-1: emits Character token for text content

- AC-1: emits Character token for text content
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: emits Character token for text content")
val found = _has_character_token("<p>hello</p>")
expect(found).to_equal(true)
```

</details>

#### AC-1: emits Character for &amp; named entity

- AC-1: emits Character for &amp; named entity
   - Expected: txt equals `&`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: emits Character for &amp; named entity")
val txt = _first_char_token_data("<p>&amp;</p>")
expect(txt).to_equal("&")
```

</details>

#### AC-1: decodes common named entities to Unicode characters

- AC-1: decodes common named entities to Unicode characters
   - Expected: _first_char_token_data("<p>&copy;</p>") equals `text.from_char_code(169)`
   - Expected: _first_char_token_data("<p>&nbsp;</p>") equals `text.from_char_code(160)`
   - Expected: _first_char_token_data("<p>&mdash;</p>") equals `text.from_char_code(8212)`
   - Expected: _first_char_token_data("<p>&hellip;</p>") equals `text.from_char_code(8230)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: decodes common named entities to Unicode characters")
expect(_first_char_token_data("<p>&copy;</p>")).to_equal(text.from_char_code(169))
expect(_first_char_token_data("<p>&nbsp;</p>")).to_equal(text.from_char_code(160))
expect(_first_char_token_data("<p>&mdash;</p>")).to_equal(text.from_char_code(8212))
expect(_first_char_token_data("<p>&hellip;</p>")).to_equal(text.from_char_code(8230))
```

</details>

#### AC-1: decodes decimal numeric character references

- AC-1: decodes decimal numeric character references
   - Expected: txt equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: decodes decimal numeric character references")
val txt = _first_char_token_data("<p>&#65;</p>")
expect(txt).to_equal("A")
```

</details>

#### AC-1: decodes hexadecimal numeric character references

- AC-1: decodes hexadecimal numeric character references
   - Expected: txt equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: decodes hexadecimal numeric character references")
val txt = _first_char_token_data("<p>&#x41;</p>")
expect(txt).to_equal("A")
```

</details>

#### AC-1: replaces invalid numeric character references

- AC-1: replaces invalid numeric character references
   - Expected: txt equals `text.from_char_code(65533)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: replaces invalid numeric character references")
val txt = _first_char_token_data("<p>&#0;</p>")
expect(txt).to_equal(text.from_char_code(65533))
```

</details>

### HtmlTokenizer script and raw text states

#### AC-1: treats content of <script> as raw text not tags

- AC-1: treats content of <script> as raw text not tags
   - Expected: inner_start_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: treats content of <script> as raw text not tags")
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

- AC-1: treats content of <style> as raw text
   - Expected: gt_tag_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: treats content of <style> as raw text")
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
| Source | `test/unit/browser_engine/html_tokenizer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HtmlTokenizer basic tags, HtmlTokenizer attributes, HtmlTokenizer self-closing tags, HtmlTokenizer character data, HtmlTokenizer script and raw text states.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d83bcafbf6e8fa12173044d0979ca59a3b7cbb00b1ebfbd38d0324c9a84872e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d83bcafbf6e8fa12173044d0979ca59a3b7cbb00b1ebfbd38d0324c9a84872e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d83bcafbf6e8fa12173044d0979ca59a3b7cbb00b1ebfbd38d0324c9a84872e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/browser_engine/html_tokenizer_spec.spl
mirror: doc/06_spec/unit/browser_engine/html_tokenizer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/html_tokenizer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/html_tokenizer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/html_tokenizer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/browser_engine/html_tokenizer_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: emits StartTag token for simple open tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/html_tokenizer_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: emits EndTag token for close tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/html_tokenizer_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: emits EOF as last token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
