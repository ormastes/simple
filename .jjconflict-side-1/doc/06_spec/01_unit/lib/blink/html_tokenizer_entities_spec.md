# Blink HTML Tokenizer — Character References

> A page author writes `AT&amp;T` in a paragraph and `href="?a=1&amp;b=2"` in a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink HTML Tokenizer — Character References

A page author writes `AT&amp;T` in a paragraph and `href="?a=1&amp;b=2"` in a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Implemented |
| Source | `test/01_unit/lib/blink/html_tokenizer_entities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A page author writes `AT&amp;T` in a paragraph and `href="?a=1&amp;b=2"` in a
link, and expects the rendered page to read `AT&T` and the link to point at
`?a=1&b=2`. Until now blink's tokenizer passed every reference through raw, so
readers saw the literal text `&amp;` on screen and links carried a doubled
escape. This spec covers the decoding blink now performs.

## Scope and Preconditions

WHATWG recognises character references in exactly two places, and so does
blink: text data (the coalesced `Character` tokens) and attribute values.
Comment and doctype data are NOT decoded, also per spec.

The decoding itself is not blink's own — it delegates to
`std.common.html.character_references`, so blink cannot drift away from the
other lanes that decode HTML. That module's spec covers the table and the
numeric forms exhaustively; this one covers the WIRING: that the tokenizer
calls it, in the right places, and only those places.

## Primary Workflow

A reference the shared decoder understands reaches the DOM as its character. A
reference it does not understand reaches the DOM as the literal source text —
`&bogus;` stays `&bogus;`. The tokenizer never substitutes a stand-in
character, because a wrong glyph reads as content and no pixel test can see it.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Character token | A coalesced run of text between tags; its `data` is decoded. |
| Attribute value | Decoded at the point the attribute is recorded. |
| Comment data | Left raw — a comment is not parsed content. |

## Related Specifications

- [HTML Character References](../common/html/character_references_spec.md)
- [Blink HTML tokenizer](html_tokenizer_spec.md)

## Scenarios

### reading text that contains character references

#### shows the character an author wrote a named reference for

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows the character an author wrote a named reference for
- tokenize a paragraph containing `&amp;`
   - Expected: _text_of("<p>AT&amp;T</p>") equals `AT&T`
- tokenize escaped angle brackets, which must NOT reopen as tags
   - Expected: _text_of("<p>&lt;p&gt;</p>") equals `<p>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shows the character an author wrote a named reference for")
step("tokenize a paragraph containing `&amp;`")
expect(_text_of("<p>AT&amp;T</p>")).to_equal("AT&T")
step("tokenize escaped angle brackets, which must NOT reopen as tags")
expect(_text_of("<p>&lt;p&gt;</p>")).to_equal("<p>")
```

</details>

#### shows the character an author wrote a numeric reference for

- shows the character an author wrote a numeric reference for
- tokenize decimal and hexadecimal references in text
   - Expected: _text_of("<p>caf&#233;</p>") equals `café`
   - Expected: _text_of("<p>a&#x2014;b</p>") equals `a—b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shows the character an author wrote a numeric reference for")
step("tokenize decimal and hexadecimal references in text")
expect(_text_of("<p>caf&#233;</p>")).to_equal("café")
expect(_text_of("<p>a&#x2014;b</p>")).to_equal("a—b")
```

</details>

#### decodes across a run split by tags, one run at a time

- decodes across a run split by tags, one run at a time
- tokenize two sibling elements that each contain a reference
   - Expected: _text_of("<b>&lt;</b><i>&gt;</i>") equals `<>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes across a run split by tags, one run at a time")
step("tokenize two sibling elements that each contain a reference")
expect(_text_of("<b>&lt;</b><i>&gt;</i>")).to_equal("<>")
```

</details>

#### leaves a reference it cannot decode exactly as the author wrote it

- leaves a reference it cannot decode exactly as the author wrote it
- tokenize text containing an unknown name and a bad number
   - Expected: _text_of("<p>&bogus; &#0;</p>") equals `&bogus; &#0;`
- tokenize an unterminated reference
   - Expected: _text_of("<p>a &amp b</p>") equals `a &amp b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves a reference it cannot decode exactly as the author wrote it")
step("tokenize text containing an unknown name and a bad number")
expect(_text_of("<p>&bogus; &#0;</p>")).to_equal("&bogus; &#0;")
step("tokenize an unterminated reference")
expect(_text_of("<p>a &amp b</p>")).to_equal("a &amp b")
```

</details>

#### leaves ordinary prose containing a bare ampersand readable

- leaves ordinary prose containing a bare ampersand readable
- tokenize a sentence with an ampersand used as a word
   - Expected: _text_of("<p>Tom & Jerry</p>") equals `Tom & Jerry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves ordinary prose containing a bare ampersand readable")
step("tokenize a sentence with an ampersand used as a word")
expect(_text_of("<p>Tom & Jerry</p>")).to_equal("Tom & Jerry")
```

</details>

### reading an attribute value that contains character references

#### gives a link the URL the author meant, not the escaped spelling

- gives a link the URL the author meant, not the escaped spelling
- tokenize an anchor whose query string escapes its separator
   - Expected: _attr_of("<a href=\"?a=1&amp;b=2\">x</a>", "href") equals `?a=1&b=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives a link the URL the author meant, not the escaped spelling")
step("tokenize an anchor whose query string escapes its separator")
expect(_attr_of("<a href=\"?a=1&amp;b=2\">x</a>", "href")).to_equal("?a=1&b=2")
```

</details>

#### decodes a single-quoted attribute value the same way

- decodes a single-quoted attribute value the same way
- tokenize the same attribute written with single quotes
   - Expected: _attr_of("<a href='?a=1&amp;b=2'>x</a>", "href") equals `?a=1&b=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes a single-quoted attribute value the same way")
step("tokenize the same attribute written with single quotes")
expect(_attr_of("<a href='?a=1&amp;b=2'>x</a>", "href")).to_equal("?a=1&b=2")
```

</details>

#### decodes an unquoted attribute value the same way

- decodes an unquoted attribute value the same way
- tokenize an unquoted value carrying a reference
   - Expected: _attr_of("<a href=x&amp;y>t</a>", "href") equals `x&y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes an unquoted attribute value the same way")
step("tokenize an unquoted value carrying a reference")
expect(_attr_of("<a href=x&amp;y>t</a>", "href")).to_equal("x&y")
```

</details>

#### decodes a numeric reference in an attribute value

- decodes a numeric reference in an attribute value
- tokenize a title attribute using a decimal reference
   - Expected: _attr_of("<img alt=\"caf&#233;\">", "alt") equals `café`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes a numeric reference in an attribute value")
step("tokenize a title attribute using a decimal reference")
expect(_attr_of("<img alt=\"caf&#233;\">", "alt")).to_equal("café")
```

</details>

#### leaves an undecodable attribute reference as written

- leaves an undecodable attribute reference as written
- tokenize an attribute holding an unknown name
   - Expected: _attr_of("<a title=\"&bogus;\">x</a>", "title") equals `&bogus;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves an undecodable attribute reference as written")
step("tokenize an attribute holding an unknown name")
expect(_attr_of("<a title=\"&bogus;\">x</a>", "title")).to_equal("&bogus;")
```

</details>

### reading places where references are not recognised

#### leaves comment data raw, because a comment is not parsed content

- leaves comment data raw, because a comment is not parsed content
- tokenize a comment containing what looks like a reference
   - Expected: _comment_of("<!-- a &amp; b -->") equals ` a &amp; b `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves comment data raw, because a comment is not parsed content")
step("tokenize a comment containing what looks like a reference")
expect(_comment_of("<!-- a &amp; b -->")).to_equal(" a &amp; b ")
```

</details>

#### does not decode a reference a second time

- does not decode a reference a second time
- tokenize text whose author escaped the ampersand of a reference
   - Expected: _text_of("<p>&amp;amp;</p>") equals `&amp;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not decode a reference a second time")
step("tokenize text whose author escaped the ampersand of a reference")
expect(_text_of("<p>&amp;amp;</p>")).to_equal("&amp;")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINKENT-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `767e93e7b53417cc11c6683fd77fdfcdad8090d4cb8e7a622609fae1569496f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `767e93e7b53417cc11c6683fd77fdfcdad8090d4cb8e7a622609fae1569496f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `767e93e7b53417cc11c6683fd77fdfcdad8090d4cb8e7a622609fae1569496f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/blink/html_tokenizer_entities_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/html_tokenizer_entities_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/blink/html_tokenizer_entities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/html_tokenizer_entities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/html_tokenizer_entities_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/blink/html_tokenizer_entities_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows the character an author wrote a named reference for' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/html_tokenizer_entities_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows the character an author wrote a numeric reference for' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/html_tokenizer_entities_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes across a run split by tags, one run at a time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
