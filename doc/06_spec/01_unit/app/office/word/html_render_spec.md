# html_render_spec

> Word document HTML render spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# html_render_spec

Word document HTML render spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word/html_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Word document HTML render spec.

Verifies that `render_block_html` / `render_document_html` render a rich-text
document as styled HTML using the shared office style resolver — the
"MS-Word-level expressive" slice of the LibreOffice suite. Each block's kind
maps to a resolver style tag (paragraph, heading_1..3, quote, code_block) and
gets the Word-level default styling inlined, the same theme the markdown and
slide surfaces use.

Assertions are over the produced HTML string and use enum→tag mapping (no
numeric interpolation), so they run cleanly on the test runner.

## Scenarios

### word HTML render: block styling from the shared theme

#### renders a Heading1 as a bold 2em div.heading_1

- renders a Heading1 as a bold 2em div.heading_1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a Heading1 as a bold 2em div.heading_1")
val html = render_block_html(_block(BlockKind.Heading1, "Title"), [], [])
expect(html).to_contain("class=\"heading_1\"")
expect(html).to_contain("font-size: 2em;")
expect(html).to_contain("font-weight: bold;")
expect(html).to_contain(">Title</div>")
```

</details>

#### renders a Paragraph with the resolver line-height

- renders a Paragraph with the resolver line-height


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a Paragraph with the resolver line-height")
val html = render_block_html(_block(BlockKind.Paragraph, "Body text"), [], [])
expect(html).to_contain("class=\"paragraph\"")
expect(html).to_contain("line-height: 1.5;")
expect(html).to_contain(">Body text</div>")
```

</details>

#### renders a Quote with an italic border-left style

- renders a Quote with an italic border-left style


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a Quote with an italic border-left style")
val html = render_block_html(_block(BlockKind.Quote, "Quoted"), [], [])
expect(html).to_contain("class=\"quote\"")
expect(html).to_contain("font-style: italic;")
expect(html).to_contain("border-left: 4px solid #cccccc;")
```

</details>

#### HTML-escapes block content so documents cannot inject markup

- HTML-escapes block content so documents cannot inject markup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HTML-escapes block content so documents cannot inject markup")
val html = render_block_html(_block(BlockKind.Paragraph, "<script>alert(1)</script> & \"x\""), [], [])
expect(html).to_contain("&lt;script&gt;")
expect(html).to_contain("&amp; &quot;x&quot;")
expect(html.contains("<script>")).to_be(false)
```

</details>

### word HTML render: tables and images
_Consecutive |cell| paragraphs render as one table; ![alt](src) as <img>._

#### renders consecutive table-row paragraphs as one styled table

- renders consecutive table-row paragraphs as one styled table


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders consecutive table-row paragraphs as one styled table")
val doc = RichDocument(title: "T", blocks: [
    _block(BlockKind.Paragraph, "| Name | Qty |"),
    _block(BlockKind.Paragraph, "|---|---|"),
    _block(BlockKind.Paragraph, "| Apples | 4 |")
], comments: [], revisions: [])
val html = render_document_html(doc)
expect(html).to_contain("<table")
expect(html).to_contain(">Name</th>")
expect(html).to_contain(">Apples</td>")
```

</details>

#### renders an image paragraph as an img tag and escapes alt

- renders an image paragraph as an img tag and escapes alt


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an image paragraph as an img tag and escapes alt")
val doc = RichDocument(title: "I", blocks: [_block(BlockKind.Paragraph, "![a <b>](pic.png)")], comments: [], revisions: [])
val html = render_document_html(doc)
expect(html).to_contain("<img src=\"pic.png\"")
expect(html).to_contain("alt=\"a &lt;b&gt;\"")
```

</details>

#### refuses img srcs containing quote or angle characters

- refuses img srcs containing quote or angle characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses img srcs containing quote or angle characters")
val doc = RichDocument(title: "I", blocks: [_block(BlockKind.Paragraph, "![x](j\"onerror.png)")], comments: [], revisions: [])
val html = render_document_html(doc)
expect(html.contains("<img")).to_be(false)
```

</details>

### word HTML render: whole document
_A document renders as a styled <article> wrapping each block._

#### wraps blocks in a document article

- wraps blocks in a document article


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps blocks in a document article")
val doc = RichDocument(title: "Doc", blocks: [_block(BlockKind.Heading1, "H"), _block(BlockKind.Paragraph, "P")], comments: [], revisions: [])
val html = render_document_html(doc)
expect(html).to_start_with("<article class=\"document\">")
expect(html).to_end_with("</article>")
expect(html).to_contain("class=\"heading_1\"")
expect(html).to_contain("class=\"paragraph\"")
```

</details>

### word HTML render: ordered lists
_Consecutive OrderedItem blocks render as one real <ol><li> list._

#### renders consecutive OrderedItem blocks as one <ol> with <li> items

- renders consecutive OrderedItem blocks as one <ol> with <li> items


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders consecutive OrderedItem blocks as one <ol> with <li> items")
val doc = RichDocument(title: "OL", blocks: [
    _block(BlockKind.OrderedItem, "First"),
    _block(BlockKind.OrderedItem, "Second"),
    _block(BlockKind.OrderedItem, "Third")
], comments: [], revisions: [])
val html = render_document_html(doc)
expect(html).to_contain("<ol><li>First</li><li>Second</li><li>Third</li></ol>")
```

</details>

### word HTML render: comments

#### renders a commented span with a dotted underline and title attribute

- renders a commented span with a dotted underline and title attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a commented span with a dotted underline and title attribute")
val span = TextSpan(text: "flagged text", style: InlineStyle.Normal, link_url: "", footnote_id: "", comment_id: "1", revision_id: "")
val doc = RichDocument(title: "C", blocks: [DocBlock(kind: BlockKind.Paragraph, spans: [span])], comments: [CommentDef(id: "1", author: "Alice", text: "please check this")], revisions: [])
val html = render_document_html(doc)
expect(html).to_contain("border-bottom: 1px dotted #888;")
expect(html).to_contain("title=\"Alice: please check this\"")
expect(html).to_contain(">flagged text</span>")
```

</details>

#### lists every comment in a trailing comments section

- lists every comment in a trailing comments section


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists every comment in a trailing comments section")
val span = TextSpan(text: "x", style: InlineStyle.Normal, link_url: "", footnote_id: "", comment_id: "1", revision_id: "")
val doc = RichDocument(title: "C", blocks: [DocBlock(kind: BlockKind.Paragraph, spans: [span])], comments: [CommentDef(id: "1", author: "Bob", text: "a note")], revisions: [])
val html = render_document_html(doc)
expect(html).to_contain("<div class=\"comments\"><ul>")
expect(html).to_contain("<li>Bob: a note</li>")
expect(html).to_end_with("</article>")
```

</details>

### word HTML render: track changes

#### renders an insert-revision span as <ins> with a data-author attribute

- renders an insert-revision span as <ins> with a data-author attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an insert-revision span as <ins> with a data-author attribute")
val span = TextSpan(text: "added text", style: InlineStyle.Normal, link_url: "", footnote_id: "", comment_id: "", revision_id: "1")
val doc = RichDocument(title: "R", blocks: [DocBlock(kind: BlockKind.Paragraph, spans: [span])], comments: [], revisions: [RevisionDef(id: "1", author: "Alice", kind: "insert", timestamp_text: "")])
val html = render_document_html(doc)
expect(html).to_contain("<ins")
expect(html).to_contain("text-decoration: underline;")
expect(html).to_contain("data-author=\"Alice\"")
expect(html).to_contain(">added text</ins>")
```

</details>

#### renders a delete-revision span as <del> with a data-author attribute

- renders a delete-revision span as <del> with a data-author attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a delete-revision span as <del> with a data-author attribute")
val span = TextSpan(text: "removed text", style: InlineStyle.Normal, link_url: "", footnote_id: "", comment_id: "", revision_id: "2")
val doc = RichDocument(title: "R", blocks: [DocBlock(kind: BlockKind.Paragraph, spans: [span])], comments: [], revisions: [RevisionDef(id: "2", author: "Bob", kind: "delete", timestamp_text: "")])
val html = render_document_html(doc)
expect(html).to_contain("<del")
expect(html).to_contain("text-decoration: line-through;")
expect(html).to_contain("data-author=\"Bob\"")
expect(html).to_contain(">removed text</del>")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `abae45183b94c1367bd7a07b71ed8ef6314b35edb9d70ce6189e1a5faeb4f865`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abae45183b94c1367bd7a07b71ed8ef6314b35edb9d70ce6189e1a5faeb4f865`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abae45183b94c1367bd7a07b71ed8ef6314b35edb9d70ce6189e1a5faeb4f865`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/word/html_render_spec.spl
mirror: doc/06_spec/01_unit/app/office/word/html_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/word/html_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/word/html_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/word/html_render_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a Heading1 as a bold 2em div.heading_1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/word/html_render_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a Paragraph with the resolver line-height' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/word/html_render_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a Quote with an italic border-left style' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
