# odf_ooxml_spec

> ODT/DOCX container interop spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# odf_ooxml_spec

ODT/DOCX container interop spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/odf_ooxml_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

ODT/DOCX container interop spec.

Pure-Simple zip (reader incl. dynamic-Huffman deflate, stored writer) plus
document import: real .odt round-trips through our own zip container, and
OOXML word/document.xml parses headings and concatenated w:t runs.

## Scenarios

### zip: stored write + read round-trip

#### writes a zip our reader and the central directory agree on

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var files: [ZipFile] = []
files.push(zip_text_file("mimetype", "application/x-test"))
files.push(zip_text_file("content.xml", "<x>hi</x>"))
val bytes = zip_write_stored(files)
val entries = zip_entries(bytes)
expect(entries.len()).to_equal(2)
expect(entries[0].name).to_equal("mimetype")
expect(zip_extract_text(bytes, "content.xml")).to_equal("<x>hi</x>")
```

</details>

#### returns empty for a missing entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = zip_write_stored([zip_text_file("a", "1")])
expect(zip_extract_text(bytes, "missing")).to_equal("")
```

</details>

### ODT: real container round-trip

#### writes .odt bytes our importer reads back with structure intact

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Annual Report\n\nStrong growth.\n\n- Expand team"
val doc = parse_markdown_document(md, "d")
val odt = document_to_odt_bytes(doc)
val doc2 = odt_bytes_to_document(odt, "d2")
val out = document_to_markdown(doc2)
expect(out).to_contain("# Annual Report")
expect(out).to_contain("Strong growth.")
expect(out).to_contain("- Expand team")
```

</details>

#### unescapes XML entities on import

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xml = "<office:text><text:p>a &amp; b &lt;c&gt;</text:p></office:text>"
val doc = odt_content_to_document(xml, "t")
expect(document_to_markdown(doc)).to_contain("a & b <c>")
```

</details>

### ODS: spreadsheet container round-trip

#### writes .ods bytes our importer reads back with values and formulas

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,42\nRevenue,1200\nProfit,=B2-100", "s")
val ods = sheet_to_ods_bytes(sheet)
val sheet2 = ods_bytes_to_sheet(ods, "s2")
expect(cell_display_text(sheet2.get_cell("A1"))).to_equal("Item")
expect(cell_display_text(sheet2.get_cell("B2"))).to_equal("1200")
expect(cell_display_text(sheet2.get_cell("B3"))).to_equal("1100")
```

</details>

### XLSX: worksheet import

#### resolves shared strings and numeric cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shared = _xlsx_shared_strings("<sst><si><t>Item</t></si><si><t>Revenue</t></si></sst>")
expect(shared.len()).to_equal(2)
val xml = "<sheetData><row><c r=\"A1\" t=\"s\"><v>0</v></c><c r=\"B1\"><v>99</v></c></row><row><c r=\"A2\" t=\"s\"><v>1</v></c><c r=\"B2\"><v>1200</v></c></row></sheetData>"
val sheet = xlsx_sheet_xml_to_sheet(xml, shared, "x")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("Item")
expect(cell_display_text(sheet.get_cell("A2"))).to_equal("Revenue")
expect(cell_display_text(sheet.get_cell("B2"))).to_equal("1200")
```

</details>

### XLSX: full container round-trip

#### writes .xlsx bytes our importer reads back (inline strings + numbers)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,42\nRevenue,1200", "s")
val xlsx = sheet_to_xlsx_bytes(sheet)
val entries = zip_entries(xlsx)
expect(entries.len()).to_equal(5)
val sheet2 = xlsx_bytes_to_sheet(xlsx, "s2")
expect(cell_display_text(sheet2.get_cell("A1"))).to_equal("Item")
expect(cell_display_text(sheet2.get_cell("B1"))).to_equal("42")
expect(cell_display_text(sheet2.get_cell("B2"))).to_equal("1200")
```

</details>

### DOCX: full container round-trip

#### round-trips styled markdown through a real .docx byte-identically

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Report\n\nGrowth was **strong** and *steady*.\n\n- Ship v2"
val docx = document_to_docx_bytes(parse_markdown_document(md, "d"))
val doc2 = docx_bytes_to_document(docx, "d2")
expect(document_to_markdown(doc2)).to_equal(md)
```

</details>

### DOCX: OOXML paragraph import

#### parses Heading1 styles and concatenates w:t runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xml = "<w:body><w:p><w:pPr><w:pStyle w:val=\"Heading1\"/></w:pPr><w:r><w:t>Title</w:t></w:r></w:p><w:p><w:r><w:t>Hello </w:t></w:r><w:r><w:t>runs.</w:t></w:r></w:p></w:body>"
val doc = docx_document_xml_to_document(xml, "t")
val out = document_to_markdown(doc)
expect(out).to_contain("# Title")
expect(out).to_contain("Hello runs.")
```

</details>

#### imports bold and italic run properties as styled spans

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xml = "<w:body><w:p><w:r><w:t>plain </w:t></w:r><w:r><w:rPr><w:b/></w:rPr><w:t>bold</w:t></w:r><w:r><w:t> and </w:t></w:r><w:r><w:rPr><w:i/></w:rPr><w:t>italic</w:t></w:r></w:p></w:body>"
val doc = docx_document_xml_to_document(xml, "t")
val out = document_to_markdown(doc)
expect(out).to_contain("plain **bold** and *italic*")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
