# Editor Markdown Office Layout Specification

> <details>

<!-- sdn-diagram:id=editor_markdown_office_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_markdown_office_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_markdown_office_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_markdown_office_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Markdown Office Layout Specification

## Scenarios

### markdown office-style layout

#### parses layout mode for paper documents

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decor = md_document_decor_parse("---\nlayout: paper\npage_view: true\nheader: Memo\n---\n# Title")
expect(decor.layout).to_equal("paper")
expect(decor.page_view).to_equal(true)
expect(decor.header).to_equal("Memo")
```

</details>

#### splits ppt pages at level-two headings and preserves slide css labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slides = md_document_split_ppt_pages("---\nlayout: ppt\n---\n# Deck\n\n## Intro @title\nWelcome\n\n## Data\nNumbers")
expect(slides.len()).to_equal(2)
expect(slides[0].index).to_equal(1)
expect(slides[0].title).to_equal("Intro @title")
expect(slides[0].content).to_equal("Welcome")
expect(slides[0].css).to_equal("title")
expect(slides[1].title).to_equal("Data")
expect(slides[1].content).to_equal("Numbers")
```

</details>

#### renders ppt pages as a css-aware deck

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = md_document_render_ppt_html("---\nlayout: ppt\ncss_file: ./deck.css\n---\n\n```css\n.md-ppt-slide { color: red; }\n```\n\n## Intro @title\nWelcome")
expect(html).to_contain("class=\"md-ppt-deck\"")
expect(html).to_contain("href=\"./deck.css\"")
expect(html).to_contain("class=\"md-inline-css\"")
expect(html).to_contain("class=\"md-ppt-slide md-css-title\"")
expect(html).to_contain("<h2>Intro @title</h2>")
expect(html).to_contain("<p>Welcome</p>")
```

</details>

#### maps markdown tables to spreadsheet cells and evaluates simple formulas

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = md_document_sheet_cells("| Name | Q1 | Q2 | Total |\n|---|---:|---:|---:|\n| Sales | 2 | 3 | =B2+C2 |")
expect(cells.len()).to_equal(8)
expect(cells[0].address).to_equal("A1")
expect(cells[4].address).to_equal("A2")
expect(cells[7].address).to_equal("D2")
expect(cells[7].raw).to_equal("=B2+C2")
expect(cells[7].value).to_equal("5")
```

</details>

#### renders spreadsheet tables with calculated values and raw formula metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = md_document_render_sheet_html("| Name | Q1 | Q2 | Total |\n|---|---:|---:|---:|\n| Sales | 2 | 3 | =B2+C2 |")
expect(html).to_contain("class=\"md-sheet\"")
expect(html).to_contain("data-cell=\"D2\"")
expect(html).to_contain("data-raw=\"=B2+C2\"")
expect(html).to_contain(">5</td>")
```

</details>

#### extracts and safely renders simple script embeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embeds = md_document_script_embeds("# Note\n\n```simple\nprint \"hi\"\n```\n\n```script\nx = 1\n```")
expect(embeds.len()).to_equal(2)
expect(embeds[0].language).to_equal("simple")
expect(embeds[0].code).to_equal("print \"hi\"")
expect(embeds[1].language).to_equal("script")
val html = md_document_render_script_embeds_html("# Note\n\n```simple\nprint \"hi\"\n```")
expect(html).to_contain("class=\"md-script-embed\"")
expect(html).to_contain("data-language=\"simple\"")
expect(html).to_contain("print &quot;hi&quot;")
```

</details>

#### dispatches office HTML rendering by document layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paper = md_document_render_office_html("---\nlayout: paper\nheader: Memo\nfooter: End\n---\n# Title\n\nBody")
expect(paper).to_contain("class=\"md-paper-layout\"")
expect(paper).to_contain("class=\"md-page-header\"")
expect(paper).to_contain("<p># Title</p>")

val deck = md_document_render_office_html("---\nlayout: ppt\n---\n## Slide\nBody")
expect(deck).to_contain("class=\"md-ppt-deck\"")
expect(deck).to_contain("class=\"md-ppt-slide\"")

val sheet = md_document_render_office_html("---\nlayout: excel\n---\n| A | B |\n|---|---:|\n| 2 | =A2+3 |")
expect(sheet).to_contain("class=\"md-sheet-layout\"")
expect(sheet).to_contain("data-cell=\"B2\"")
expect(sheet).to_contain(">5</td>")
```

</details>

#### rewrites a ppt page body while preserving slide boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = md_document_replace_ppt_page("---\nlayout: ppt\n---\n## First\nOld\n\n## Second\nKeep", 1, "New\nBody")
expect(updated).to_contain("## First\nNew\nBody\n## Second")
expect(updated).to_contain("Keep")
expect(updated.contains("Old")).to_equal(false)
```

</details>

#### rewrites a spreadsheet cell and recalculates through the sheet model

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = md_document_replace_sheet_cell_value("| Name | Q1 | Q2 | Total |\n|---|---:|---:|---:|\n| Sales | 2 | 3 | =B2+C2 |", "B2", "7")
expect(updated).to_contain("| Sales | 7 | 3 | =B2+C2 |")
val cells = md_document_sheet_cells(updated)
expect(cells[7].value).to_equal("10")
```

</details>

### markdown sgrid embedding

#### scans hidden and fenced sgrid carriers without parsing full markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "| item:Str | qty:i64 | price:i64 | total:i64 |\n| :--- | --: | --: | --: |\n| Bread | 2 | 5 | 10 |\n\n<!-- sgrid\nid: invoice\ntable: previous\nf:\n    D2 = B2+C2\n-->\n\n```sgrid\nid: visible\ntable: 1\nfmt:\n    C:D = money(USD)\n```"
val blocks = md_sgrid_scan(md)
expect(blocks.len()).to_equal(2)
expect(blocks[0].carrier).to_equal("html")
expect(blocks[0].line).to_be_greater_than(0)
expect(blocks[0].id).to_equal("invoice")
expect(blocks[0].table_ref).to_equal("previous")
expect(blocks[0].formulas[0].target).to_equal("D2")
expect(blocks[1].carrier).to_equal("fence")
expect(blocks[1].formats[0].expr).to_equal("money(USD)")
```

</details>

#### binds sgrid metadata to the target markdown table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Sheet\n\n| A | B |\n|---|---:|\n| 1 | 2 |\n\n<!-- sgrid\nid: invoice\ntable: previous\n-->"
val bindings = md_sgrid_bind_tables(md)
expect(bindings.len()).to_equal(1)
expect(bindings[0].id).to_equal("invoice")
expect(bindings[0].table_start).to_equal(2)
expect(bindings[0].table_end).to_equal(4)
```

</details>

#### binds sgrid metadata to next and named tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "<!-- sgrid\nid: next_sheet\ntable: next\n-->\n\n## invoice\n| A | B |\n|---|---:|\n| 1 | 2 |\n\n```sgrid\nid: named\ntable: #invoice\n```"
val bindings = md_sgrid_bind_tables(md)
expect(bindings.len()).to_equal(2)
expect(bindings[0].table_start).to_equal(6)
expect(bindings[1].table_start).to_equal(6)
```

</details>

#### applies canonical sgrid formulas to markdown table cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "| item:Str | qty:i64 | price:i64 | total:i64 |\n| :--- | --: | --: | --: |\n| Bread | 2 | 5 | 0 |\n| Wine | 1 | 15 | 0 |\n| Sum | | | 0 |\n\n<!-- sgrid\nid: invoice\ntable: previous\nf:\n    D2:D3 = B * C\n    D4 = sum(D2:D3)\n-->"
val cells = md_sgrid_apply(md)
expect(cells[7].address).to_equal("D2")
expect(cells[7].value).to_equal("10")
expect(cells[11].value).to_equal("15")
expect(cells[15].value).to_equal("25")
```

</details>

#### supports inline formula and header type sugar for small sheets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "| item:Str | qty:i64 | price:i64 | total:i64 |\n| :--- | --: | --: | --: |\n| Bread | 2 | 5 | 10 `=B2*C2` |"
val formulas = md_sgrid_inline_annotations(md)
val types = md_sgrid_header_types(md)
expect(formulas.len()).to_equal(1)
expect(formulas[0].target).to_equal("D2")
expect(formulas[0].expr).to_equal("B2*C2")
expect(types.len()).to_equal(4)
expect(types[1].expr).to_equal("type(i64)")
```

</details>

#### provides selection sum and copy helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "| A | B |\n|---|---:|\n| 2 | 3 |\n| 4 | 5 |"
expect(md_sgrid_selection_sum(md, "A2:B3")).to_equal("14")
expect(md_sgrid_copy_selection(md, "A2:B3")).to_equal("2\t3\n4\t5")
```

</details>

#### provides pivot sum and common library names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "| item | qty |\n|---|---:|\n| Bread | 2 |\n| Wine | 1 |\n| Bread | 3 |"
val pivot = md_sgrid_pivot_sum(md, "A", "B")
expect(pivot.len()).to_equal(2)
expect(pivot[0].key).to_equal("Bread")
expect(pivot[0].value).to_equal("5")
expect(md_sgrid_common_libraries().join(",")).to_contain("pivot_sum")
```

</details>

#### evaluates common sgrid range libraries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "| value | out |\n|---:|---:|\n| 2 | 0 |\n| 4 | 0 |\n| 6 | 0 |\n| 0 | 0 |\n| 0 | 0 |\n\n<!-- sgrid\nf:\n    B2 = sum(A2:A4)\n    B3 = avg(A2:A4)\n    B4 = min(A2:A4)\n    B5 = max(A2:A4)\n    B6 = count(A2:A4)\n-->"
val cells = md_sgrid_apply(md)
expect(cells[3].value).to_equal("12")
expect(cells[5].value).to_equal("4")
expect(cells[7].value).to_equal("2")
expect(cells[9].value).to_equal("6")
expect(cells[11].value).to_equal("3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_markdown_office_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown office-style layout
- markdown sgrid embedding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
