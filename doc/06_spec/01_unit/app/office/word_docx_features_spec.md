# word_docx_features_spec

> DOCX hyperlinks, images, and headers/footers — full-pipeline spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# word_docx_features_spec

DOCX hyperlinks, images, and headers/footers — full-pipeline spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_docx_features_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DOCX hyperlinks, images, and headers/footers — full-pipeline spec.

Covers the three MS Word gap features through model -> .docx export ->
.docx import -> markdown, plus the header/footer sibling writer:

  - Hyperlinks: markdown `[text](url)` is a first-class TextSpan (link_url),
    exported as `<w:hyperlink r:id="rIdN">` + an external relationship in
    word/_rels/document.xml.rels, imported back by resolving r:id, and
    serialized back to `[text](url)`.
  - Images: markdown `![alt](path)` (whole-paragraph convention, same as the
    html renderer) embeds the PNG bytes as word/media/imageN.png + a minimal
    wp:inline DrawingML picture when the file exists; a missing (or non-PNG)
    path falls back to a plain alt-text run instead of crashing. alt/src are
    stashed on wp:docPr name/descr so import reconstructs the exact
    `![alt](src)` reference losslessly.
  - Headers/footers: `document_to_docx_bytes_hf(doc, header, footer)` is a
    sibling of `document_to_docx_bytes` (which stays byte-identical when
    called with header_text/footer_text both "") that adds
    word/header1.xml + word/footer1.xml, wired via sectPr headerReference/
    footerReference + rels + content types; the footer always carries a
    PAGE field (`<w:fldSimple w:instr=" PAGE "/>`).

## Scenarios

### DOCX hyperlinks: markdown [text](url) round trip

#### round-trips a link mixed with other inline styles exactly

- round-trips a link mixed with other inline styles exactly
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a link mixed with other inline styles exactly")
val md = "See [details](http://example.com/x) for **more** info."
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### emits word/_rels/document.xml.rels with the URL as an External target

- emits word/_rels/document.xml.rels with the URL as an External target


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits word/_rels/document.xml.rels with the URL as an External target")
val doc = parse_markdown_document("[go](http://example.org/page)", "d")
val docx = document_to_docx_bytes(doc)
val rels = zip_extract_text(docx, "word/_rels/document.xml.rels")
expect(rels).to_contain("http://example.org/page")
expect(rels).to_contain("TargetMode=\"External\"")
expect(rels).to_contain("relationships/hyperlink")
```

</details>

#### wraps the run in <w:hyperlink r:id=...> in word/document.xml

- wraps the run in <w:hyperlink r:id=...> in word/document.xml


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps the run in <w:hyperlink r:id=...> in word/document.xml")
val doc = parse_markdown_document("[go](http://example.org/page)", "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:hyperlink r:id=\"")
expect(document_xml).to_contain("</w:hyperlink>")
```

</details>

#### round-trips a paragraph with two different links

- round-trips a paragraph with two different links
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a paragraph with two different links")
val md = "[one](http://a.example/1) and [two](http://b.example/2)."
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
```

</details>

### DOCX images: markdown ![alt](path) round trip

#### embeds an existing PNG and round-trips the ![alt](src) reference

- embeds an existing PNG and round-trips the ![alt](src) reference
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("embeds an existing PNG and round-trips the ![alt](src) reference")
val png_path = "/tmp/word_docx_features_spec_tiny.png"
rt_file_write_bytes(png_path, _tiny_png_bytes())
val md = "![a tiny dot]({png_path})"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
expect(_has_entry(docx, "word/media/image1.png")).to_be(true)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:drawing>")
expect(document_xml).to_contain("a:blip r:embed=\"")
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
rt_file_delete(png_path)
```

</details>

#### falls back to the alt text when the image file is missing (no crash)

- falls back to the alt text when the image file is missing (no crash)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to the alt text when the image file is missing (no crash)")
val md = "![missing pic](/no/such/path/does-not-exist.png)"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml.contains("<w:drawing>")).to_be(false)
expect(document_xml).to_contain("missing pic")
expect(_has_entry(docx, "word/media/image1.png")).to_be(false)
```

</details>

#### falls back to the alt text for a non-PNG path even if it exists

- falls back to the alt text for a non-PNG path even if it exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to the alt text for a non-PNG path even if it exists")
val jpg_path = "/tmp/word_docx_features_spec_tiny.jpg"
rt_file_write_bytes(jpg_path, _tiny_png_bytes())
val md = "![a jpeg]({jpg_path})"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml.contains("<w:drawing>")).to_be(false)
expect(document_xml).to_contain("a jpeg")
rt_file_delete(jpg_path)
```

</details>

### DOCX headers/footers: document_to_docx_bytes_hf

#### document_to_docx_bytes is byte-identical to the _hf sibling called with empty header/footer

- document_to_docx_bytes is byte-identical to the _hf sibling called with empty header/footer
   - Expected: plain equals `hf_empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("document_to_docx_bytes is byte-identical to the _hf sibling called with empty header/footer")
val doc = parse_markdown_document("# Report\n\nBody text.", "d")
val plain = document_to_docx_bytes(doc)
val hf_empty = document_to_docx_bytes_hf(doc, "", "")
expect(plain).to_equal(hf_empty)
```

</details>

#### emits word/header1.xml and word/footer1.xml, wired into sectPr and content types

- emits word/header1.xml and word/footer1.xml, wired into sectPr and content types


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits word/header1.xml and word/footer1.xml, wired into sectPr and content types")
val doc = parse_markdown_document("# Report\n\nBody text.", "d")
val docx = document_to_docx_bytes_hf(doc, "Acme Corp", "Confidential")
expect(_has_entry(docx, "word/header1.xml")).to_be(true)
expect(_has_entry(docx, "word/footer1.xml")).to_be(true)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:headerReference w:type=\"default\" r:id=\"")
expect(document_xml).to_contain("<w:footerReference w:type=\"default\" r:id=\"")
val types = zip_extract_text(docx, "[Content_Types].xml")
expect(types).to_contain("/word/header1.xml")
expect(types).to_contain("/word/footer1.xml")
val rels = zip_extract_text(docx, "word/_rels/document.xml.rels")
expect(rels).to_contain("relationships/header")
expect(rels).to_contain("relationships/footer")
```

</details>

#### footer includes a PAGE field

- footer includes a PAGE field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("footer includes a PAGE field")
val doc = parse_markdown_document("Body.", "d")
val docx = document_to_docx_bytes_hf(doc, "H", "F")
val footer_xml = zip_extract_text(docx, "word/footer1.xml")
expect(footer_xml).to_contain("<w:fldSimple w:instr=\" PAGE \"/>")
```

</details>

#### header/footer text reads back via docx_bytes_to_header_footer

- header/footer text reads back via docx_bytes_to_header_footer
   - Expected: hf.header_text equals `Acme Corp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("header/footer text reads back via docx_bytes_to_header_footer")
val doc = parse_markdown_document("Body.", "d")
val docx = document_to_docx_bytes_hf(doc, "Acme Corp", "Confidential")
val hf = docx_bytes_to_header_footer(docx)
expect(hf.header_text).to_equal("Acme Corp")
expect(hf.footer_text.contains("Confidential")).to_be(true)
```

</details>

#### docx_bytes_to_header_footer returns empty strings for a header/footer-less docx

- docx_bytes_to_header_footer returns empty strings for a header/footer-less docx
   - Expected: hf.header_text equals ``
   - Expected: hf.footer_text equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("docx_bytes_to_header_footer returns empty strings for a header/footer-less docx")
val doc = parse_markdown_document("Body.", "d")
val docx = document_to_docx_bytes(doc)
val hf = docx_bytes_to_header_footer(docx)
expect(hf.header_text).to_equal("")
expect(hf.footer_text).to_equal("")
```

</details>

### DOCX footnotes: markdown [^1] / [^1]: note round trip

#### round-trips a single footnote reference + definition exactly

- round-trips a single footnote reference + definition exactly
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a single footnote reference + definition exactly")
val md = "See the note.[^1]\n\n[^1]: This is the note text."
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### emits word/footnotes.xml with the two mandatory separators and the real footnote

- emits word/footnotes.xml with the two mandatory separators and the real footnote


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits word/footnotes.xml with the two mandatory separators and the real footnote")
val md = "Ref here.[^1]\n\n[^1]: Note body."
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
expect(_has_entry(docx, "word/footnotes.xml")).to_be(true)
val footnotes_xml = zip_extract_text(docx, "word/footnotes.xml")
expect(footnotes_xml).to_contain("w:type=\"separator\"")
expect(footnotes_xml).to_contain("w:type=\"continuationSeparator\"")
expect(footnotes_xml).to_contain("<w:footnote w:id=\"1\">")
expect(footnotes_xml).to_contain("Note body.")
```

</details>

#### emits a <w:footnoteReference w:id=...> run in word/document.xml

- emits a <w:footnoteReference w:id=...> run in word/document.xml


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a <w:footnoteReference w:id=...> run in word/document.xml")
val md = "Ref here.[^1]\n\n[^1]: Note body."
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:footnoteReference w:id=\"1\"/>")
```

</details>

#### wires word/footnotes.xml into content types and document.xml.rels

- wires word/footnotes.xml into content types and document.xml.rels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires word/footnotes.xml into content types and document.xml.rels")
val md = "Ref here.[^1]\n\n[^1]: Note body."
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val types = zip_extract_text(docx, "[Content_Types].xml")
expect(types).to_contain("/word/footnotes.xml")
val rels = zip_extract_text(docx, "word/_rels/document.xml.rels")
expect(rels).to_contain("relationships/footnotes")
```

</details>

#### round-trips two footnote references with two definitions

- round-trips two footnote references with two definitions
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips two footnote references with two definitions")
val md = "First.[^1] Second.[^2]\n\n[^1]: One.\n[^2]: Two."
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### a footnote-less document has no footnotes.xml part (plain-doc byte identity)

- a footnote-less document has no footnotes.xml part (plain-doc byte identity)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a footnote-less document has no footnotes.xml part (plain-doc byte identity)")
val doc = parse_markdown_document("# Report\n\nBody text.", "d")
val docx = document_to_docx_bytes(doc)
expect(_has_entry(docx, "word/footnotes.xml")).to_be(false)
```

</details>

### DOCX ordered lists: markdown `1. item` round trip

#### round-trips a 3-item ordered list exactly

- round-trips a 3-item ordered list exactly
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a 3-item ordered list exactly")
val md = "1. First\n2. Second\n3. Third"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### emits w:numPr with numId 1 and a minimal word/numbering.xml

- emits w:numPr with numId 1 and a minimal word/numbering.xml


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits w:numPr with numId 1 and a minimal word/numbering.xml")
val md = "1. First\n2. Second"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:numPr><w:ilvl w:val=\"0\"/><w:numId w:val=\"1\"/></w:numPr>")
expect(_has_entry(docx, "word/numbering.xml")).to_be(true)
val numbering_xml = zip_extract_text(docx, "word/numbering.xml")
expect(numbering_xml).to_contain("w:numFmt w:val=\"decimal\"")
```

</details>

#### wires word/numbering.xml into content types and document.xml.rels

- wires word/numbering.xml into content types and document.xml.rels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires word/numbering.xml into content types and document.xml.rels")
val md = "1. First\n2. Second"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val types = zip_extract_text(docx, "[Content_Types].xml")
expect(types).to_contain("/word/numbering.xml")
val rels = zip_extract_text(docx, "word/_rels/document.xml.rels")
expect(rels).to_contain("relationships/numbering")
```

</details>

#### an ordered-list-less document has no numbering.xml part (plain-doc byte identity)

- an ordered-list-less document has no numbering.xml part (plain-doc byte identity)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an ordered-list-less document has no numbering.xml part (plain-doc byte identity)")
val doc = parse_markdown_document("# Report\n\nBody text.", "d")
val docx = document_to_docx_bytes(doc)
expect(_has_entry(docx, "word/numbering.xml")).to_be(false)
```

</details>

#### a plain document with no new features is byte-identical to a header/footer-empty call

- a plain document with no new features is byte-identical to a header/footer-empty call
   - Expected: plain equals `hf_empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a plain document with no new features is byte-identical to a header/footer-empty call")
val doc = parse_markdown_document("# Report\n\n- a bullet\n\nBody text.", "d")
val plain = document_to_docx_bytes(doc)
val hf_empty = document_to_docx_bytes_hf(doc, "", "")
expect(plain).to_equal(hf_empty)
```

</details>

### DOCX comments: markdown [>>author: text<<] round trip

#### round-trips a single comment exactly

- round-trips a single comment exactly
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a single comment exactly")
val md = "Please check this claim.[>>Alice: needs a citation<<]"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### emits word/comments.xml with the author attribute and a fixed w:date

- emits word/comments.xml with the author attribute and a fixed w:date


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits word/comments.xml with the author attribute and a fixed w:date")
val md = "Flagged text.[>>Alice: needs a citation<<]"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
expect(_has_entry(docx, "word/comments.xml")).to_be(true)
val comments_xml = zip_extract_text(docx, "word/comments.xml")
expect(comments_xml).to_contain("w:author=\"Alice\"")
expect(comments_xml).to_contain("w:date=\"2026-01-01T00:00:00Z\"")
expect(comments_xml).to_contain("needs a citation")
```

</details>

#### wraps the commented run in commentRangeStart/End + commentReference in word/document.xml

- wraps the commented run in commentRangeStart/End + commentReference in word/document.xml


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps the commented run in commentRangeStart/End + commentReference in word/document.xml")
val md = "Flagged text.[>>Alice: needs a citation<<]"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:commentRangeStart w:id=\"")
expect(document_xml).to_contain("<w:commentRangeEnd w:id=\"")
expect(document_xml).to_contain("<w:commentReference w:id=\"")
```

</details>

#### wires word/comments.xml into content types and document.xml.rels

- wires word/comments.xml into content types and document.xml.rels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires word/comments.xml into content types and document.xml.rels")
val md = "Flagged text.[>>Alice: needs a citation<<]"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val types = zip_extract_text(docx, "[Content_Types].xml")
expect(types).to_contain("/word/comments.xml")
val rels = zip_extract_text(docx, "word/_rels/document.xml.rels")
expect(rels).to_contain("relationships/comments")
```

</details>

#### round-trips two comments by different authors exactly

- round-trips two comments by different authors exactly
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips two comments by different authors exactly")
val md = "First point.[>>Alice: check this<<] Second point.[>>Bob: and this too<<]"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
val comments_xml = zip_extract_text(docx, "word/comments.xml")
expect(comments_xml).to_contain("w:author=\"Alice\"")
expect(comments_xml).to_contain("w:author=\"Bob\"")
```

</details>

#### a comment-less document has no comments.xml part (plain-doc byte identity)

- a comment-less document has no comments.xml part (plain-doc byte identity)
   - Expected: plain equals `hf_empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a comment-less document has no comments.xml part (plain-doc byte identity)")
val doc = parse_markdown_document("# Report\n\nBody text.", "d")
val docx = document_to_docx_bytes(doc)
expect(_has_entry(docx, "word/comments.xml")).to_be(false)
val plain = document_to_docx_bytes(doc)
val hf_empty = document_to_docx_bytes_hf(doc, "", "")
expect(plain).to_equal(hf_empty)
```

</details>

#### renders a dotted underline and a trailing comments section in HTML

- renders a dotted underline and a trailing comments section in HTML


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a dotted underline and a trailing comments section in HTML")
val md = "Flagged text.[>>Alice: needs a citation<<]"
val doc = parse_markdown_document(md, "d")
val html = render_document_html(doc)
expect(html).to_contain("border-bottom: 1px dotted #888;")
expect(html).to_contain("title=\"Alice: needs a citation\"")
expect(html).to_contain("<div class=\"comments\"><ul>")
expect(html).to_contain("<li>Alice: needs a citation</li>")
```

</details>

### DOCX named paragraph styles: catalog + heading/blockquote/code round trip

#### emits the full named-style catalog in word/styles.xml

- emits the full named-style catalog in word/styles.xml


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the full named-style catalog in word/styles.xml")
val doc = parse_markdown_document("# Report\n\nBody.", "d")
val docx = document_to_docx_bytes(doc)
val styles_xml = zip_extract_text(docx, "word/styles.xml")
expect(styles_xml).to_contain("w:styleId=\"Normal\"")
expect(styles_xml).to_contain("w:styleId=\"Heading1\"")
expect(styles_xml).to_contain("w:styleId=\"Heading2\"")
expect(styles_xml).to_contain("w:styleId=\"Heading3\"")
expect(styles_xml).to_contain("w:styleId=\"Quote\"")
expect(styles_xml).to_contain("w:styleId=\"Code\"")
expect(styles_xml).to_contain("w:styleId=\"ListParagraph\"")
expect(styles_xml).to_contain("w:sz w:val=\"32\"")
expect(styles_xml).to_contain("w:sz w:val=\"26\"")
expect(styles_xml).to_contain("w:sz w:val=\"22\"")
expect(styles_xml).to_contain("<w:i/>")
expect(styles_xml).to_contain("Courier New")
```

</details>

#### Heading1-3 are basedOn Normal and bold

- Heading1-3 are basedOn Normal and bold


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Heading1-3 are basedOn Normal and bold")
val doc = parse_markdown_document("# Report\n\nBody.", "d")
val docx = document_to_docx_bytes(doc)
val styles_xml = zip_extract_text(docx, "word/styles.xml")
expect(styles_xml).to_contain("<w:basedOn w:val=\"Normal\"/>")
expect(styles_xml).to_contain("<w:b/>")
```

</details>

#### exports a Heading1 paragraph with w:pStyle Heading1 in the body

- exports a Heading1 paragraph with w:pStyle Heading1 in the body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports a Heading1 paragraph with w:pStyle Heading1 in the body")
val doc = parse_markdown_document("# Title", "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:pStyle w:val=\"Heading1\"/>")
```

</details>

#### round-trips a blockquote through docx exactly (was silently lost before this change)

- round-trips a blockquote through docx exactly (was silently lost before this change)
   - Expected: doc.blocks[0].kind equals `BlockKind.Quote`
   - Expected: back.blocks[0].kind equals `BlockKind.Quote`
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a blockquote through docx exactly (was silently lost before this change)")
val md = "> A wise quote."
val doc = parse_markdown_document(md, "d")
expect(doc.blocks[0].kind).to_equal(BlockKind.Quote)
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:pStyle w:val=\"Quote\"/>")
val back = docx_bytes_to_document(docx, "d2")
expect(back.blocks[0].kind).to_equal(BlockKind.Quote)
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### round-trips a fenced code block through docx exactly (was silently lost before this change)

- round-trips a fenced code block through docx exactly (was silently lost before this change)
   - Expected: doc.blocks[0].kind equals `BlockKind.CodeBlock`
   - Expected: back.blocks[0].kind equals `BlockKind.CodeBlock`
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a fenced code block through docx exactly (was silently lost before this change)")
val md = "```\nlet x = 1\nlet y = 2\n```"
val doc = parse_markdown_document(md, "d")
expect(doc.blocks[0].kind).to_equal(BlockKind.CodeBlock)
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:pStyle w:val=\"Code\"/>")
val back = docx_bytes_to_document(docx, "d2")
expect(back.blocks[0].kind).to_equal(BlockKind.CodeBlock)
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### round-trips headings + blockquote + code together, md -> docx -> md exact

- round-trips headings + blockquote + code together, md -> docx -> md exact
   - Expected: document_to_markdown(back) equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips headings + blockquote + code together, md -> docx -> md exact")
val md = "# Title\n\n## Sub\n\n### Detail\n\n> Quoted line\n\nBody paragraph.\n\n```\ncode line one\ncode line two\n```"
val doc = parse_markdown_document(md, "d")
val docx = document_to_docx_bytes(doc)
val back = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(back)).to_equal(md)
```

</details>

#### an unrecognized w:pStyle value falls back to a plain Paragraph on import

- an unrecognized w:pStyle value falls back to a plain Paragraph on import
   - Expected: back.blocks[0].kind equals `BlockKind.Paragraph`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unrecognized w:pStyle value falls back to a plain Paragraph on import")
val document_xml = "<w:body><w:p><w:pPr><w:pStyle w:val=\"SomeOtherAppsStyle\"/></w:pPr><w:r><w:t>Text</w:t></w:r></w:p></w:body>"
val back = docx_document_xml_to_document(document_xml, "d")
expect(back.blocks[0].kind).to_equal(BlockKind.Paragraph)
```

</details>

#### a document with no headings/quote/code is byte-identical to a header/footer-empty call

- a document with no headings/quote/code is byte-identical to a header/footer-empty call
   - Expected: plain equals `hf_empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a document with no headings/quote/code is byte-identical to a header/footer-empty call")
val doc = parse_markdown_document("Just a plain paragraph.", "d")
val plain = document_to_docx_bytes(doc)
val hf_empty = document_to_docx_bytes_hf(doc, "", "")
expect(plain).to_equal(hf_empty)
```

</details>

#### renders a Quote block as a real <blockquote> and a CodeBlock as <pre><code> in HTML

- renders a Quote block as a real <blockquote> and a CodeBlock as <pre><code> in HTML


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a Quote block as a real <blockquote> and a CodeBlock as <pre><code> in HTML")
val md = "> Quoted line\n\n```\ncode here\n```"
val doc = parse_markdown_document(md, "d")
val html = render_document_html(doc)
expect(html).to_contain("<blockquote class=\"quote\"")
expect(html).to_contain("</blockquote>")
expect(html).to_contain("<pre class=\"code_block\"")
expect(html).to_contain("<code>code here</code>")
expect(html).to_contain("</pre>")
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

- Canonical SPipe generation for source `38ef166a9579acd89b2ac76c93139979cd08534ee7cabe8d1f807f34222dd830`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38ef166a9579acd89b2ac76c93139979cd08534ee7cabe8d1f807f34222dd830`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38ef166a9579acd89b2ac76c93139979cd08534ee7cabe8d1f807f34222dd830`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/word_docx_features_spec.spl
mirror: doc/06_spec/01_unit/app/office/word_docx_features_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/word_docx_features_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/word_docx_features_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/word_docx_features_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a link mixed with other inline styles exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/word_docx_features_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits word/_rels/document.xml.rels with the URL as an External target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/word_docx_features_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps the run in <w:hyperlink r:id=...> in word/document.xml' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
