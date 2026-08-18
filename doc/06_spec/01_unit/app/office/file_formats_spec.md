# file_formats_spec

> Office file formats spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# file_formats_spec

Office file formats spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/file_formats_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office file formats spec.

Verifies real open/save round-trips: Markdown <-> RichDocument (Writer) and
CSV <-> Sheet (Calc), plus that opened files render through the HTML adapter.

## Scenarios

### Writer markdown round-trip
_Parsing then serializing markdown preserves structure._

#### parses headings, bullets, quotes and code fences into blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Title\n\nBody text.\n\n## Sub\n\n- a\n- b\n\n> quote\n\n```\ncode line\n```"
val doc = parse_markdown_document(md, "Doc")
expect(doc.title).to_equal("Doc")
expect(doc.blocks.len()).to_equal(7)
```

</details>

#### round-trips headings and a bullet back to markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# My Report\n\nHello.\n\n## Section\n\n- item one"
val doc = parse_markdown_document(md, "r")
val out = document_to_markdown(doc)
expect(out).to_contain("# My Report")
expect(out).to_contain("## Section")
expect(out).to_contain("- item one")
```

</details>

#### renders an opened markdown file to a full HTML page

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_render_source("word", "r.md", "# Hi\n\nWorld.")
expect(result.html_output).to_start_with("<!DOCTYPE html>")
expect(result.html_output).to_contain("Hi")
expect(result.html_output).to_contain("World.")
```

</details>

#### parses **bold**, *italic* and `code` into styled inline HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_render_source("word", "s.md", "Mix **bold** and *ital* and `code` here.")
expect(result.html_output).to_contain("<strong>bold</strong>")
expect(result.html_output).to_contain("<em>ital</em>")
expect(result.html_output).to_contain(">code</code>")
```

</details>

#### round-trips inline styles back to markdown markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = parse_markdown_document("Mix **bold** and *ital* and `code`.", "s")
val out = document_to_markdown(doc)
expect(out).to_contain("**bold**")
expect(out).to_contain("*ital*")
expect(out).to_contain("`code`")
```

</details>

### Calc CSV round-trip
_Parsing then serializing CSV preserves the grid._

#### parses a CSV grid into cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("Name,Q1\nRevenue,1200\nCosts,800", "s")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("Name")
expect(cell_display_text(sheet.get_cell("B2"))).to_equal("1200")
expect(cell_display_text(sheet.get_cell("A3"))).to_equal("Costs")
```

</details>

#### round-trips a CSV grid back to CSV text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csv = "Name,Q1,Q2\nRevenue,1200,1488\nCosts,800,920"
val sheet = parse_csv_sheet(csv, "s")
expect(sheet_to_csv(sheet)).to_equal(csv)
```

</details>

#### honors double-quoted fields containing commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("\"Smith, John\",42", "s")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("Smith, John")
expect(cell_display_text(sheet.get_cell("B1"))).to_equal("42")
```

</details>

#### renders an opened CSV file to a full HTML table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = office_render_source("sheets", "s.csv", "Name,Q1\nRevenue,1200")
expect(result.html_output).to_contain("<table")
expect(result.html_output).to_contain("Revenue")
expect(result.html_output).to_contain("1200")
```

</details>

#### computes formulas loaded from CSV (=A1+B2 -> sum)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = parse_csv_sheet("10,20\n30,40\n=A1+B2,=A1+A2", "s")
expect(cell_display_text(sheet.get_cell("A3"))).to_equal("50")
expect(cell_display_text(sheet.get_cell("B3"))).to_equal("40")
```

</details>

### parse_inline_spans returns its declared result

#### returns spans for a plain line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_inline_spans("hello", 1)
expect(r.spans.len() > 0).to_equal(true)
expect(r.comments.len()).to_equal(0)
```

</details>

#### returns a span even for an empty line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_inline_spans("", 1)
expect(r.spans.len()).to_equal(1)
```

</details>

#### returns the comments it collected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_inline_spans("hi [>>ana: check this<<]", 1)
expect(r.comments.len()).to_equal(1)
expect(r.comments[0].author).to_equal("ana")
```

</details>

### markdown parse covers every inline construct (defect class)

#### parses every block kind without faulting

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# H1\n\n## H2\n\n### H3\n\n- bullet\n\n1. ordered\n\n> quote\n\nplain para\n\n```\ncode\n```"
val doc = parse_markdown_document(md, "d")
# 8 blocks: H1, H2, H3, bullet, ordered, quote, paragraph, code fence
expect(doc.blocks.len()).to_equal(8)
for block in doc.blocks:
    expect(block.spans.len() > 0).to_equal(true)
```

</details>

#### parses every inline style without faulting

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for line in ["**bold**", "*italic*", "`code`", "[text](http://x)",
        "foot[^1]", "plain", "**bold** and *italic* and `code`"]:
    val doc = parse_markdown_document(line, "d")
    expect(doc.blocks.len()).to_equal(1)
    expect(doc.blocks[0].spans.len() > 0).to_equal(true)
```

</details>

#### round-trips a document mixing blocks and inline styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Report\n\nGrowth was **strong** and *steady*.\n\n- Ship v2"
expect(document_to_markdown(parse_markdown_document(md, "d"))).to_equal(md)
```

</details>

#### threads comment ids document-wide across lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "a [>>ana: one<<]\n\nb [>>bo: two<<]"
val doc = parse_markdown_document(md, "d")
expect(doc.comments.len()).to_equal(2)
expect(doc.comments[0].id).to_not_equal(doc.comments[1].id)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
