# pptx_tables_spec

> PPTX tables: deck markdown-table blocks through export/import/HTML render.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pptx_tables_spec

PPTX tables: deck markdown-table blocks through export/import/HTML render.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/pptx_tables_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

PPTX tables: deck markdown-table blocks through export/import/HTML render.

Ground truth is structural, on a 3-column table (header + 2 data rows):
slide1.xml carries `<a:tbl>` inside a `<p:graphicFrame>` (graphicData uri
".../drawingml/2006/table") with 3 a:gridCol and 3 a:tr — checked with our
own zip reader AND cross-checked with the system unzip (-p) on a scratchpad
file; `unzip -t` exits 0; and deck -> pptx -> deck preserves the table block
exactly IN POSITION between body lines. Header row = bold run + light tcPr
solidFill (direct formatting; no tblStyleLst, so `firstRow="1"` has no style
list to bind to — documented ceiling). HTML render emits a border-collapse
`<table>` with a bold `<th>` header row.

Lives in its own spec file: pptx_export_spec.spl already runs near the
per-file time budget (see pptx_layout_spec.spl's note).

## Scenarios

### PPTX tables: export emits a:tbl in a graphicFrame

#### emits a p:graphicFrame with a:tbl, 3 a:gridCol and 3 a:tr for a 3x(1+2) table

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck(_DECK_SRC)
val pptx = deck_to_pptx_bytes(deck)
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1).to_contain("<p:graphicFrame>")
expect(slide1).to_contain("uri=\"http://schemas.openxmlformats.org/drawingml/2006/table\"")
expect(slide1).to_contain("<a:tbl>")
expect(_count_occurrences(slide1, "<a:gridCol ")).to_equal(3)
expect(_count_occurrences(slide1, "<a:tr ")).to_equal(3)
# every row is full: 9 cells, txBody-before-tcPr order
expect(_count_occurrences(slide1, "<a:tc>")).to_equal(9)
# header styling: bold run + light solid fill on the 3 header cells
expect(_count_occurrences(slide1, "<a:rPr b=\"1\"/>")).to_equal(3)
expect(_count_occurrences(slide1, "<a:srgbClr val=\"D9E2F3\"/>")).to_equal(3)
# cell texts land in a:t runs
expect(slide1).to_contain("<a:t>h1</a:t>")
expect(slide1).to_contain("<a:t>f</a:t>")
# persist for the system-unzip cross-check (ground truth)
val out_path = "{_SCRATCH}/pptx_tables_spec_3col.pptx"
File.write_bytes(out_path, pptx)
val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)
```

</details>

#### escapes cell text and system unzip validates the archive

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Esc\n| A&B | <ok> |\n| --- | --- |\n| x | y |")
val pptx = deck_to_pptx_bytes(deck)
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1).to_contain("<a:t>A&amp;B</a:t>")
expect(slide1).to_contain("<a:t>&lt;ok&gt;</a:t>")
val out_path = "{_SCRATCH}/pptx_tables_spec.pptx"
File.write_bytes(out_path, pptx)
val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)
# system cross-check: unzip -p shows the a:tbl in the slide part
val cat_result = run("unzip", ["-p", out_path, "ppt/slides/slide1.xml"])
expect(cat_result.stdout).to_contain("<a:tbl>")
expect(cat_result.stdout).to_contain("<a:gridCol ")
```

</details>

### PPTX tables: import round-trip

#### preserves the table block in position through deck -> pptx -> deck

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck(_DECK_SRC)
expect(deck_to_text(deck)).to_equal(_DECK_SRC)
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck2.len()).to_equal(1)
expect(deck_to_text(deck2)).to_equal(_DECK_SRC)
```

</details>

#### round-trips escaped cell text through the pptx package

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "Esc\n| A&B | <ok> |\n| --- | --- |\n| x | y |"
val deck = parse_deck(src)
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck_to_text(deck2)).to_equal(src)
```

</details>

### PPTX tables: HTML render

#### renders a border-collapse table with a bold th header row

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck(_DECK_SRC)
val html = render_slide_html(deck[0])
expect(html).to_contain("<table style=\"border-collapse: collapse;")
expect(_count_occurrences(html, "<th ")).to_equal(3)
expect(_count_occurrences(html, "<td ")).to_equal(6)
expect(html).to_contain("font-weight: bold")
expect(html).to_contain(">h1</th>")
expect(html).to_contain(">f</td>")
# separator row is deck notation — never rendered
expect(html.contains("---")).to_be(false)
```

</details>

#### escapes cell text in the rendered table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = parse_deck("Esc\n| A&B | <ok> |\n| --- | --- |\n| x | y |")
val html = render_slide_html(deck[0])
expect(html).to_contain(">A&amp;B</th>")
expect(html).to_contain(">&lt;ok&gt;</th>")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
