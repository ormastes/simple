# odf_export_spec

> Flat ODF export spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# odf_export_spec

Flat ODF export spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/odf_export_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Flat ODF export spec.

Writer documents export as .fodt and Calc sheets as .fods — flat OpenDocument
XML that LibreOffice opens directly (no zip container needed). Numbers are
typed, formulas use ODF `of:=` syntax, and content is XML-escaped.

## Scenarios

### flat ODF: Writer .fodt

#### wraps blocks in a valid flat ODF text document

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = parse_markdown_document("# Title\n\nHello.\n\n- item", "d")
val xml = document_to_fodt(doc)
expect(xml).to_start_with("<?xml version=\"1.0\"")
expect(xml).to_contain("office:mimetype=\"application/vnd.oasis.opendocument.text\"")
expect(xml).to_contain("<text:h text:outline-level=\"1\">Title</text:h>")
expect(xml).to_contain("<text:p>Hello.</text:p>")
expect(xml).to_contain("<text:list><text:list-item>")
expect(xml).to_end_with("</office:document>")
```

</details>

#### XML-escapes document content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = parse_markdown_document("a < b & \"c\"", "d")
val xml = document_to_fodt(doc)
expect(xml).to_contain("a &lt; b &amp; &quot;c&quot;")
```

</details>

### flat ODF: Calc .fods

#### types numbers and preserves formulas in ODF syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,Q1\nRevenue,1200\nProfit,=B1-100", "s")
val xml = sheet_to_fods(sheet)
expect(xml).to_contain("office:mimetype=\"application/vnd.oasis.opendocument.spreadsheet\"")
expect(xml).to_contain("office:value-type=\"float\" office:value=\"1200\"")
expect(xml).to_contain("table:formula=\"of:=B1-100\"")
expect(xml).to_contain("office:value-type=\"string\"")
expect(xml).to_contain("table:name=\"s\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
