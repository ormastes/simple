# word_docx_revisions_spec

> DOCX track-changes serialization — Word's w:ins/w:del round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# word_docx_revisions_spec

DOCX track-changes serialization — Word's w:ins/w:del round-trip.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_docx_revisions_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

DOCX track-changes serialization — Word's w:ins/w:del round-trip.

An insert-revision span serializes wrapped in
<w:ins w:id=".." w:author=".." w:date="..">...runs...</w:ins>; a
delete-revision span serializes wrapped in <w:del ...> with the run's text
as <w:delText> instead of <w:t> (OOXML requirement — Word rejects a plain
<w:t> inside w:del). Author/date come from the doc-level RevisionDef the
span's revision_id points at (see attributed_text.spl/track_changes.spl);
w:date is the same fixed constant the rest of odf_ooxml.spl's writer uses
("2026-01-01T00:00:00Z"), keeping export deterministic.

On import, every <w:ins>/<w:del> wrapper becomes revision-marked spans plus
one fresh RevisionDef in `doc.revisions` (see `_docx_para_spans` in
odf_ooxml.spl) — ids are RENUMBERED sequentially per import, never the
original document's w:id values, so round-trip comparisons below are over
"<author>|<kind>|<text>" triples (revisions_summary minus the id column),
not the raw summary lines.

Ceilings (see odf_ooxml.spl docstrings): revision ids renumbered on read;
a <w:del> nested inside a <w:ins> (or vice versa) is not modeled; w:date is
a fixed constant on write and read back as free text, no format validation.

## Scenarios

### DOCX track changes: w:ins insert-revision round trip

#### wraps the inserted run in <w:ins w:id=.. w:author=.. w:date=..> in word/document.xml

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _doc1([_plain_span("Hello world")])
val d1 = tracked_insert(doc, 0, 5, " there", "Alice")
val docx = document_to_docx_bytes(d1)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:ins w:id=\"")
expect(document_xml).to_contain("w:author=\"Alice\"")
expect(document_xml).to_contain("w:date=\"2026-01-01T00:00:00Z\"")
expect(document_xml).to_contain("</w:ins>")
expect(document_xml).to_contain(" there")
```

</details>

#### round-trips the insert-revision summary (author|kind|text) and final_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _doc1([_plain_span("Hello world")])
val d1 = tracked_insert(doc, 0, 5, " there", "Alice")
val before = _summary_triples(d1)
expect(before.len()).to_equal(1)
expect(before[0]).to_equal("Alice|insert| there")
val docx = document_to_docx_bytes(d1)
val back = docx_bytes_to_document(docx, "d2")
val after = _summary_triples(back)
expect(after.len()).to_equal(1)
expect(after[0]).to_equal("Alice|insert| there")
expect(final_text(back)).to_equal(final_text(d1))
```

</details>

### DOCX track changes: w:del delete-revision round trip

#### wraps the deleted run in <w:del ...> with <w:delText> (not <w:t>) in word/document.xml

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _doc1([_plain_span("Hello world")])
val d1 = tracked_delete(doc, 0, 0, 5, "Bob")
val docx = document_to_docx_bytes(d1)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("<w:del w:id=\"")
expect(document_xml).to_contain("w:author=\"Bob\"")
expect(document_xml).to_contain("</w:del>")
expect(document_xml).to_contain("<w:delText xml:space=\"preserve\">Hello</w:delText>")
```

</details>

#### round-trips the delete-revision summary (author|kind|text) and final_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _doc1([_plain_span("Hello world")])
val d1 = tracked_delete(doc, 0, 0, 5, "Bob")
val before = _summary_triples(d1)
expect(before.len()).to_equal(1)
expect(before[0]).to_equal("Bob|delete|Hello")
val docx = document_to_docx_bytes(d1)
val back = docx_bytes_to_document(docx, "d2")
val after = _summary_triples(back)
expect(after.len()).to_equal(1)
expect(after[0]).to_equal("Bob|delete|Hello")
expect(final_text(back)).to_equal(final_text(d1))
expect(final_text(back)).to_equal(" world")
```

</details>

### DOCX track changes: two-author mixed insert + delete round trip

#### round-trips both revisions' summaries and final_text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _doc1([_plain_span("Hello world")])
val d1 = tracked_insert(doc, 0, 0, "Hi ", "Alice")
val d2 = tracked_delete(d1, 0, 3, 8, "Bob")
val before = _summary_triples(d2)
expect(before.len()).to_equal(2)
expect(before[0]).to_equal("Alice|insert|Hi ")
expect(before[1]).to_equal("Bob|delete|Hello")
val docx = document_to_docx_bytes(d2)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml).to_contain("w:author=\"Alice\"")
expect(document_xml).to_contain("w:author=\"Bob\"")
val back = docx_bytes_to_document(docx, "d2")
val after = _summary_triples(back)
expect(after.len()).to_equal(2)
expect(after[0]).to_equal("Alice|insert|Hi ")
expect(after[1]).to_equal("Bob|delete|Hello")
expect(final_text(back)).to_equal(final_text(d2))
```

</details>

### DOCX track changes: no-revision regression guard

#### a revision-less document has no w:ins/w:del in word/document.xml

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = parse_markdown_document("# Report\n\nBody text.", "d")
val docx = document_to_docx_bytes(doc)
val document_xml = zip_extract_text(docx, "word/document.xml")
expect(document_xml.contains("<w:ins ")).to_be(false)
expect(document_xml.contains("<w:del ")).to_be(false)
expect(document_xml.contains("<w:delText")).to_be(false)
```

</details>

#### a revision-less document's bytes are unaffected by the revisions feature (double-export stability)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = parse_markdown_document("# Report\n\n- a bullet\n\nBody text.", "d")
val first = document_to_docx_bytes(doc)
val second = document_to_docx_bytes(doc)
expect(first).to_equal(second)
expect(_has_entry(first, "word/document.xml")).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
