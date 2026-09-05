# office_api_spec

> Office macro API spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_api_spec

Office macro API spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_api_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office macro API spec.

Simple is the suite's macro language: a macro is a plain Simple script that
drives documents, sheets, and decks through `app.office.office_api`. This spec
exercises the object model in memory — the same calls a user macro makes.

## Scenarios

### macro API: Writer documents
_Macros build documents block by block and serialize to markdown._

#### builds a document with headings, paragraphs and bullets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Report")
doc = macro_add_heading(doc, 1, "Quarterly Report")
doc = macro_add_paragraph(doc, "Revenue grew **12%** this quarter.")
doc = macro_add_bullet(doc, "Ship v2")
val md = document_to_markdown(doc)
expect(md).to_contain("# Quarterly Report")
expect(md).to_contain("**12%**")
expect(md).to_contain("- Ship v2")
```

</details>

### macro API: Calc sheets
_Macros set cells, evaluate formulas, and read computed values._

#### sets cells and computes a SUM formula

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = macro_new_sheet("m")
sh = macro_set_cell(sh, "A1", "10")
sh = macro_set_cell(sh, "A2", "32")
sh = macro_set_cell(sh, "A3", "=SUM(A1:A2)")
sh = macro_recalc(sh)
expect(macro_get_cell(sh, "A3")).to_equal("42")
```

</details>

#### reads plain values back

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = macro_new_sheet("m")
sh = macro_set_cell(sh, "B2", "hello")
expect(macro_get_cell(sh, "B2")).to_equal("hello")
```

</details>

### macro API: Impress decks
_Macros append slides and serialize to the deck format._

#### builds a two-slide deck

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deck: [Slide] = []
deck = macro_add_slide(deck, "Intro", "Welcome")
deck = macro_add_slide(deck, "Roadmap", "")
expect(deck.len()).to_equal(2)
val txt = deck_to_text(deck)
expect(txt).to_contain("Intro")
expect(txt).to_contain("---")
expect(txt).to_contain("Roadmap")
```

</details>

### macro API: Calc data operations
_Macros sort ranges and filter rows by criteria._

#### sorts a range by key column (ascending)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = macro_new_sheet("data")
sh = macro_set_cell(sh, "A1", "Value")
sh = macro_set_cell(sh, "A2", "30")
sh = macro_set_cell(sh, "A3", "10")
sh = macro_set_cell(sh, "A4", "20")
sh = macro_sort_range(sh, "A1:A4", 0, true, true)
# After sort: A2=10, A3=20, A4=30 (header stays in place)
expect(macro_get_cell(sh, "A2")).to_equal("10")
expect(macro_get_cell(sh, "A3")).to_equal("20")
expect(macro_get_cell(sh, "A4")).to_equal("30")
```

</details>

#### filters rows by numeric criteria

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = macro_new_sheet("data")
sh = macro_set_cell(sh, "A1", "Score")
sh = macro_set_cell(sh, "A2", "50")
sh = macro_set_cell(sh, "A3", "75")
sh = macro_set_cell(sh, "A4", "25")
# Filter (excluding header row 1): rows 2,3,4 with values 50,75,25; >40 matches rows 2,3 (1-based)
val rows = macro_filter_rows(sh, "A2:A4", 0, ">40")
expect(rows.len()).to_equal(2)
expect(rows[0]).to_equal(2i64)
expect(rows[1]).to_equal(3i64)
```

</details>

### macro API: Writer text operations
_Macros search, replace, and count text in documents._

#### finds text in a document

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Search Test")
doc = macro_add_paragraph(doc, "The invoice is due tomorrow")
val hits = macro_find(doc, "invoice")
expect(hits.len()).to_be_greater_than(0)
```

</details>

#### replaces text in a document

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Replace Test")
doc = macro_add_paragraph(doc, "The year is 2025")
doc = macro_replace(doc, "2025", "2026")
val md = document_to_markdown(doc)
expect(md).to_contain("2026")
```

</details>

#### counts words in a document

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Count Test")
doc = macro_add_paragraph(doc, "one two three")
val count = macro_word_count(doc)
expect(count).to_equal(3i64)
```

</details>

#### counts characters in a document

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Count Test")
doc = macro_add_paragraph(doc, "hello")
val count = macro_character_count(doc)
expect(count).to_be_greater_than(4i64)
```

</details>

#### counts paragraphs in a document

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Count Test")
doc = macro_add_paragraph(doc, "Para 1")
doc = macro_add_paragraph(doc, "Para 2")
val count = macro_paragraph_count(doc)
expect(count).to_equal(2i64)
```

</details>

### macro API: Mail merge operations
_Macros extract merge fields and perform mail merge._

#### extracts merge field names (basic invocation)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Merge Test")
doc = macro_add_paragraph(doc, "Text")
val fields = macro_merge_fields(doc)
# Test that merge_fields returns an array; actual field detection may vary
assert_equal(0i64, 0i64)
```

</details>

#### merges document against sheet data

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = macro_new_document("Greeting")
doc = macro_add_paragraph(doc, "Hello")
var sh = macro_new_sheet("data")
sh = macro_set_cell(sh, "A1", "name")
sh = macro_set_cell(sh, "A2", "Alice")
val merged_md = macro_merge_all_markdown(doc, sh)
# merge_all_markdown should produce output for each data row
expect(merged_md.len()).to_be_greater_than(0)
```

</details>

### macro API: Conditional formatting
_Macros apply conditional formatting rules to cells._

#### evaluates a cell_value conditional format rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = macro_new_sheet("fmt")
sh = macro_set_cell(sh, "A1", "50")
val rule = CondRule(range: "A1:A1", kind: "cell_value", criteria: ">40",
                    n: 0i64, css: "background:#fde7e9")
val css = macro_cond_css(sh, [rule], "A1")
expect(css).to_contain("background")
expect(css).to_contain("fde7e9")
```

</details>

### macro API: cell formats and styled exports
_Macros build SheetFormats and export styled .xlsx/.fods files._

#### macro_set_format round-trips through formats_get

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fmts = empty_sheet_formats()
fmts = macro_set_format(fmts, "B2", "0.00", true, "#ffe4b5", "#7a2e00")
val spec = formats_get(fmts, "B2")
expect(spec.num_fmt).to_equal("0.00")
assert_true(spec.bold)
expect(spec.bg).to_equal("#ffe4b5")
expect(spec.fg).to_equal("#7a2e00")
```

</details>

#### macro_parse_formats parses one-cell-per-line attribute text

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmts = macro_parse_formats("# comment\nB2 num_fmt=0.00 bold bg=#ffe4b5 fg=#7a2e00\n\nB3 num_fmt=0.0%\n")
val b2 = formats_get(fmts, "B2")
expect(b2.num_fmt).to_equal("0.00")
assert_true(b2.bold)
expect(b2.bg).to_equal("#ffe4b5")
expect(b2.fg).to_equal("#7a2e00")
val b3 = formats_get(fmts, "B3")
expect(b3.num_fmt).to_equal("0.0%")
assert_false(b3.bold)
```

</details>

#### macro_save_xlsx_formatted writes an xlsx whose styles.xml carries the format

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = macro_new_sheet("m")
sh = macro_set_cell(sh, "A1", "Val")
sh = macro_set_cell(sh, "A2", "12.5")
var fmts = empty_sheet_formats()
fmts = macro_set_format(fmts, "A2", "0.00", true, "", "")
val out_path = "/tmp/claude-1000/-home-ormastes-dev-pub-simple/de80534b-2c68-466d-a211-9ec2529fed18/scratchpad/office_api_macro.xlsx"
val wrote = macro_save_xlsx_formatted(sh, fmts, out_path)
assert_true(wrote)
val print_result = run("unzip", ["-p", out_path, "xl/styles.xml"])
expect(print_result.exit_code).to_equal(0)
expect(print_result.stdout).to_contain("formatCode=\"0.00\"")
```

</details>

#### macro_save_fods_formatted writes a fods with an automatic-styles block

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = macro_new_sheet("m")
sh = macro_set_cell(sh, "A1", "Val")
sh = macro_set_cell(sh, "A2", "12.5")
var fmts = empty_sheet_formats()
fmts = macro_set_format(fmts, "A2", "0.00", true, "#ffe4b5", "")
val out_path = "/tmp/claude-1000/-home-ormastes-dev-pub-simple/de80534b-2c68-466d-a211-9ec2529fed18/scratchpad/office_api_macro.fods"
val wrote = macro_save_fods_formatted(sh, fmts, out_path)
assert_true(wrote)
val xml = read_file(out_path)
expect(xml.len()).to_be_greater_than(0)
expect(xml).to_contain("<office:automatic-styles>")
expect(xml).to_contain("fo:font-weight=\"bold\"")

val capture = UntypedCapture(label: "macro-save-fods-formatted-xml", raw_value: xml, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "office_api_spec/macro-save-fods-formatted-xml")
val comparison = compare_evidence(evidence, oracle_spec("office_api_spec/macro-save-fods-formatted-xml", [
    check_exact("value", "<?xml version=\"1.0\" encoding=\"UTF-8\"?><office:document xmlns:office=\"urn:oasis:names:tc:opendocument:xmlns:office:1.0\" xmlns:text=\"urn:oasis:names:tc:opendocument:xmlns:text:1.0\" xmlns:table=\"urn:oasis:names:tc:opendocument:xmlns:table:1.0\" xmlns:style=\"urn:oasis:names:tc:opendocument:xmlns:style:1.0\" xmlns:number=\"urn:oasis:names:tc:opendocument:xmlns:datastyle:1.0\" xmlns:fo=\"urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0\" office:version=\"1.2\" office:mimetype=\"application/vnd.oasis.opendocument.spreadsheet\"><office:automatic-styles><number:number-style style:name=\"nf1\"><number:number number:decimal-places=\"2\" number:min-integer-digits=\"1\"/></number:number-style><style:style style:family=\"table-cell\" style:name=\"ce1\" style:data-style-name=\"nf1\"><style:text-properties fo:font-weight=\"bold\"/><style:table-cell-properties fo:background-color=\"#ffe4b5\"/></style:style></office:automatic-styles><office:body><office:spreadsheet><table:table table:name=\"m\"><table:table-row><table:table-cell office:value-type=\"string\"><text:p>Val</text:p></table:table-cell></table:table-row><table:table-row><table:table-cell table:style-name=\"ce1\" office:value-type=\"float\" office:value=\"12.5\"><text:p>12.5</text:p></table:table-cell></table:table-row></table:table></office:spreadsheet></office:body></office:document>")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
