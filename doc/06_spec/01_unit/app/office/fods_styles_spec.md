# fods_styles_spec

> Flat ODF styled export spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fods_styles_spec

Flat ODF styled export spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/fods_styles_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Flat ODF styled export spec.

sheet_to_fods_formatted mirrors the xlsx styling work for LibreOffice: it
emits an <office:automatic-styles> block with one table-cell style per
distinct FormatSpec (bold / fo:color / fo:background-color), ODF data styles
for the supported Excel number formats (0.00 / #,##0.00 / 0.0% / yyyy-mm-dd)
wired via style:data-style-name, and tags formatted cells with
table:style-name. The plain sheet_to_fods writer stays unchanged.

## Scenarios

### flat ODF: styled .fods automatic styles

#### emits automatic-styles with bold, color, and background properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_start_with("<?xml version=\"1.0\"")
expect(xml).to_contain("office:mimetype=\"application/vnd.oasis.opendocument.spreadsheet\"")
expect(xml).to_contain("<office:automatic-styles>")
expect(xml).to_contain("</office:automatic-styles>")
expect(xml).to_contain("<style:style style:family=\"table-cell\" style:name=\"ce1\"")
expect(xml).to_contain("fo:font-weight=\"bold\"")
expect(xml).to_contain("fo:color=\"#7a2e00\"")
expect(xml).to_contain("<style:table-cell-properties fo:background-color=\"#ffe4b5\"/>")
```

</details>

#### declares the style, number, and fo namespaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_contain("xmlns:style=\"urn:oasis:names:tc:opendocument:xmlns:style:1.0\"")
expect(xml).to_contain("xmlns:number=\"urn:oasis:names:tc:opendocument:xmlns:datastyle:1.0\"")
expect(xml).to_contain("xmlns:fo=\"urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0\"")
```

</details>

### flat ODF: styled .fods number formats

#### maps 0.00 to a number-style with two decimal places

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_contain("<number:number-style style:name=\"nf1\">")
expect(xml).to_contain("number:decimal-places=\"2\" number:min-integer-digits=\"1\"")
```

</details>

#### maps 0.0% to a percentage-style with a percent text node

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_contain("<number:percentage-style style:name=\"nf2\">")
expect(xml).to_contain("number:decimal-places=\"1\"")
expect(xml).to_contain("<number:text>%</number:text>")
```

</details>

#### maps yyyy-mm-dd to a date-style with year/month/day elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_contain("<number:date-style style:name=\"nf3\">")
expect(xml).to_contain("<number:year number:style=\"long\"/>")
expect(xml).to_contain("<number:month number:style=\"long\"/>")
expect(xml).to_contain("<number:day number:style=\"long\"/>")
```

</details>

#### maps #,##0.00 to a grouped number-style

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_contain("<number:number-style style:name=\"nf4\">")
expect(xml).to_contain("number:grouping=\"true\"")
```

</details>

#### skips the data-style for unknown formats but keeps the styling

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
var formats = empty_sheet_formats()
formats = formats_set(formats, "B2", FormatSpec(num_fmt: "??weird??", bold: true, bg: "", fg: ""))
val xml = sheet_to_fods_formatted(sheet, formats)
assert_false(xml.contains("style:data-style-name"))
expect(xml).to_contain("<style:style style:family=\"table-cell\" style:name=\"ce1\">")
expect(xml).to_contain("fo:font-weight=\"bold\"")
expect(xml).to_contain("table:style-name=\"ce1\"")
```

</details>

### flat ODF: styled .fods cell references

#### tags formatted cells with table:style-name and wires the data style

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_contain("style:data-style-name=\"nf1\"")
expect(xml).to_contain("table:style-name=\"ce1\" office:value-type=\"float\" office:value=\"12.5\"")
expect(xml).to_contain("table:style-name=\"ce2\"")
expect(xml).to_contain("table:style-name=\"ce3\"")
expect(xml).to_contain("table:style-name=\"ce4\"")
```

</details>

#### leaves unformatted cells without a style name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
expect(xml).to_contain("<table:table-cell office:value-type=\"string\"><text:p>Item</text:p></table:table-cell>")
```

</details>

### flat ODF: styled .fods structural validation

#### writes a formatted .fods that xmllint accepts as well-formed XML

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val formats = _sample_formats()
val xml = sheet_to_fods_formatted(sheet, formats)
val out_path = "/tmp/claude-1000/-home-ormastes-dev-pub-simple/de80534b-2c68-466d-a211-9ec2529fed18/scratchpad/fods_styles_spec.fods"
val wrote = rt_file_write_text(out_path, xml)
assert_true(wrote)
val lint_result = run("xmllint", ["--noout", out_path])
expect(lint_result.exit_code).to_equal(0)
```

</details>

### flat ODF: unformatted writer stays unchanged

#### sheet_to_fods keeps its original namespaces and no styles block

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _sample_sheet()
val xml = sheet_to_fods(sheet)
expect(xml).to_contain("<office:document xmlns:office=\"urn:oasis:names:tc:opendocument:xmlns:office:1.0\" xmlns:text=\"urn:oasis:names:tc:opendocument:xmlns:text:1.0\" xmlns:table=\"urn:oasis:names:tc:opendocument:xmlns:table:1.0\" office:version=\"1.2\" office:mimetype=\"application/vnd.oasis.opendocument.spreadsheet\">")
expect(xml).to_contain("office:value-type=\"float\" office:value=\"12.5\"")
assert_false(xml.contains("office:automatic-styles"))
assert_false(xml.contains("table:style-name"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
