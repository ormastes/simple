# Word Mail Merge Specification

> Tests covering merge_fields: discover placeholders, merge_document: substitute one data row, merge_all: one document per data row, merge_all_markdown: rendered batch output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Word Mail Merge Specification

## Scenarios

### merge_fields: discover placeholders
_Distinct {field} names in document order, first occurrence wins._

#### returns distinct field names in document order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val fields = merge_fields(doc)
expect(fields.len()).to_equal(3)
expect(fields.get(0)).to_equal("Name")
expect(fields.get(1)).to_equal("City")
expect(fields.get(2)).to_equal("Zip")
```

</details>

#### returns empty list for a document with no placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = parse_markdown_document("Plain text, no fields here.", "plain")
val fields = merge_fields(doc)
expect(fields.len()).to_equal(0)
```

</details>

### merge_document: substitute one data row
_Row N (1-based data row) reads sheet row N+1; row 1 = sheet row 2._

#### substitutes every field for row 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
val merged = merge_document(doc, sheet, 1)
val md = document_to_markdown(merged)
expect(md).to_equal(_row1_expected)
```

</details>

#### substitutes independently for row 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
val merged = merge_document(doc, sheet, 2)
val md = document_to_markdown(merged)
expect(md).to_equal(_row2_expected)
```

</details>

#### preserves bold styling around a merged placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
val merged = merge_document(doc, sheet, 1)
val block1 = merged.blocks.get(1)
val span0 = block1.spans.get(0)
expect(span0.text).to_equal("Paris")
expect(span0.style).to_equal(InlineStyle.Bold)
val span1 = block1.spans.get(1)
expect(span1.text).to_equal(" awaits you, Alice!")
expect(span1.style).to_equal(InlineStyle.Normal)
```

</details>

#### substitutes missing-column field with empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
val merged = merge_document(doc, sheet, 1)
val block2 = merged.blocks.get(2)
val span0 = block2.spans.get(0)
expect(span0.text).to_equal("Your code: ")
```

</details>

#### does not mutate the original template document

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
merge_document(doc, sheet, 1)
val original_md = document_to_markdown(doc)
expect(original_md).to_equal(_template_md())
```

</details>

### merge_all: one document per data row
_Batch merges every data row (sheet rows below the header)._

#### returns one merged document per data row

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
val docs = merge_all(doc, sheet)
expect(docs.len()).to_equal(2)
```

</details>

#### each merged document matches the per-row merge_document result

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
val docs = merge_all(doc, sheet)
val md0 = document_to_markdown(docs.get(0))
val md1 = document_to_markdown(docs.get(1))
expect(md0).to_equal(_row1_expected)
expect(md1).to_equal(_row2_expected)
```

</details>

### merge_all_markdown: rendered batch output
_Merged docs rendered to markdown, joined by a '---' separator line._

#### joins merged documents with the separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _template_doc()
val sheet = _data_sheet()
val out = merge_all_markdown(doc, sheet)
val expected = _row1_expected + "\n\n---\n\n" + _row2_expected
expect(out).to_equal(expected)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_mail_merge_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering merge_fields: discover placeholders, merge_document: substitute one data row, merge_all: one document per data row, merge_all_markdown: rendered batch output.
- merge_fields: discover placeholders
- merge_document: substitute one data row
- merge_all: one document per data row
- merge_all_markdown: rendered batch output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
