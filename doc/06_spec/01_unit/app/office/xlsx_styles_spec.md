# xlsx_styles_spec

> XLSX styles.xml spec: per-cell number formats + bold/bg/fg carried into

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# xlsx_styles_spec

XLSX styles.xml spec: per-cell number formats + bold/bg/fg carried into

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/xlsx_styles_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

XLSX styles.xml spec: per-cell number formats + bold/bg/fg carried into
the .xlsx container.

Verification ceiling: no LibreOffice/Excel is available in this environment.
Acceptance here is structural (zip integrity via the system `unzip -t`,
well-formed styles.xml inspected via `unzip -p`) plus our own importer
reading the bytes back into an equal SheetFormats. Rendering in a real
spreadsheet app was NOT verified.

## Scenarios

### XLSX: styles.xml round-trip

#### writes distinct numFmts/fonts/fills and references them via s= on cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,42\nRevenue,1200", "s")
val formats = _sample_formats()
val xlsx = sheet_to_xlsx_bytes_formatted(sheet, formats)
val entries = zip_entries(xlsx)
expect(entries.len()).to_equal(6)
var found_styles = false
for entry in entries:
    if entry.name == "xl/styles.xml":
        found_styles = true
expect(found_styles).to_equal(true)
```

</details>

#### round-trips num_fmt/bold/bg/fg on formatted cells and defaults elsewhere

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,42\nRevenue,1200", "s")
val formats = _sample_formats()
val xlsx = sheet_to_xlsx_bytes_formatted(sheet, formats)
val result = xlsx_bytes_to_sheet_formatted(xlsx, "s2")

expect(cell_display_text(result.sheet.get_cell("A1"))).to_equal("Item")
expect(cell_display_text(result.sheet.get_cell("B1"))).to_equal("42")
expect(cell_display_text(result.sheet.get_cell("B2"))).to_equal("1200")

val spec_a1 = formats_get(result.formats, "A1")
expect(spec_a1.num_fmt).to_equal("0.00")
expect(spec_a1.bold).to_equal(true)
expect(spec_a1.bg).to_equal("#ffe4b5")
expect(spec_a1.fg).to_equal("#7a2e00")

val spec_b2 = formats_get(result.formats, "B2")
expect(spec_b2.num_fmt).to_equal("0%")
expect(spec_b2.bold).to_equal(false)
expect(spec_b2.bg).to_equal("")
expect(spec_b2.fg).to_equal("")

val spec_a2 = formats_get(result.formats, "A2")
val default_spec = default_format_spec()
expect(spec_a2.num_fmt).to_equal(default_spec.num_fmt)
expect(spec_a2.bold).to_equal(default_spec.bold)
expect(spec_a2.bg).to_equal(default_spec.bg)
expect(spec_a2.fg).to_equal(default_spec.fg)
```

</details>

#### produces styles.xml the system unzip tool accepts and can print

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,42\nRevenue,1200", "s")
val formats = _sample_formats()
val xlsx = sheet_to_xlsx_bytes_formatted(sheet, formats)
val out_path = "/tmp/claude-1000/-home-ormastes-dev-pub-simple/de80534b-2c68-466d-a211-9ec2529fed18/scratchpad/xlsx_styles_spec.xlsx"
File.write_bytes(out_path, xlsx)

val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)

val print_result = run("unzip", ["-p", out_path, "xl/styles.xml"])
expect(print_result.exit_code).to_equal(0)
val styles_xml = print_result.stdout
expect(styles_xml).to_contain("<numFmts")
expect(styles_xml).to_contain("numFmtId=\"164\"")
expect(styles_xml).to_contain("<fonts")
expect(styles_xml).to_contain("<b/>")
expect(styles_xml).to_contain("<fills")
expect(styles_xml).to_contain("patternType=\"solid\"")
expect(styles_xml).to_contain("<cellXfs")
expect(styles_xml).to_end_with("</styleSheet>")
```

</details>

### XLSX: unformatted writer stays unchanged

#### sheet_to_xlsx_bytes still emits 5 parts with no styles.xml

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,42\nRevenue,1200", "s")
val xlsx = sheet_to_xlsx_bytes(sheet)
val entries = zip_entries(xlsx)
expect(entries.len()).to_equal(5)
var found_styles = false
for entry in entries:
    if entry.name == "xl/styles.xml":
        found_styles = true
expect(found_styles).to_equal(false)
```

</details>

#### is deterministic (byte-identical across calls) and still importer-readable

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Item,42\nRevenue,1200", "s")
val bytes1 = sheet_to_xlsx_bytes(sheet)
val bytes2 = sheet_to_xlsx_bytes(sheet)
expect(bytes1).to_equal(bytes2)
val sheet2 = xlsx_bytes_to_sheet(bytes1, "s2")
expect(cell_display_text(sheet2.get_cell("A1"))).to_equal("Item")
expect(cell_display_text(sheet2.get_cell("B2"))).to_equal("1200")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
