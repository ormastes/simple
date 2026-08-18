# render_adapter_spec

> Office render adapter spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# render_adapter_spec

Office render adapter spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/render_adapter_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office render adapter spec.

Verifies the unified render adapter routes each surface (Writer / Calc /
Impress) to its real model->HTML renderer wrapped in a complete, styled HTML5
page, and that unknown/empty adapter names fall back to the suite index.

## Scenarios

### office render adapter: full-page HTML export
_Each surface renders a complete, self-contained HTML document._

#### renders Writer with a doctype, title bar, and document article

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("word")
expect(html).to_start_with("<!DOCTYPE html>")
expect(html).to_contain("LibreOffice Writer")
expect(html).to_contain("<article class=\"document\">")
expect(html).to_contain("Quarterly Business Review")
expect(html).to_end_with("</html>")
```

</details>

#### renders Calc as a styled HTML table with the budget grid

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("sheets")
expect(html).to_contain("LibreOffice Calc")
expect(html).to_contain("<table")
expect(html).to_contain("Revenue")
expect(html).to_contain("Profit")
```

</details>

#### renders Impress as a slide section

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("slides")
expect(html).to_contain("LibreOffice Impress")
expect(html).to_contain("<section class=\"slide\"")
expect(html).to_contain("Simple Office")
```

</details>

#### falls back to the suite index for unknown adapter names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("")
expect(html).to_contain("LibreOffice Suite")
expect(html).to_contain("Writer")
expect(html).to_contain("Calc")
expect(html).to_contain("Impress")
```

</details>

#### accepts LibreOffice aliases (writer/calc/impress)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_render("writer")).to_contain("LibreOffice Writer")
expect(_render("calc")).to_contain("LibreOffice Calc")
expect(_render("impress")).to_contain("LibreOffice Impress")
```

</details>

#### renders Mail as a Gmail-like mailbox page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("mail")
expect(html).to_contain("LibreOffice Mail")
expect(html).to_contain("mailbox")
```

</details>

#### renders Planner as a kanban board page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("planner")
expect(html).to_contain("LibreOffice Planner")
expect(html).to_contain("kanban-lane")
```

</details>

#### renders Draw as SVG, Base as a table, Math as MathML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_render("draw")).to_contain("<svg")
val base_html = _render("base")
expect(base_html).to_contain("LibreOffice Base")
expect(base_html).to_contain("Ada Lovelace")
expect(_render("math")).to_contain("<math")
```

</details>

#### gives Calc spreadsheet chrome: column letters and row numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("sheets")
expect(html).to_contain(">A</th>")
expect(html).to_contain(">B</th>")
expect(html).to_contain(">1</th>")
expect(html).to_contain(">4</th>")
```

</details>

#### shows a menubar strip on every page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _render("word")
expect(html).to_contain("<nav")
expect(html).to_contain("Format")
```

</details>

#### renders a deck file's slides through office_render_source

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = "Intro\nWelcome\n---\nRoadmap\nQ3 goals"
val result = office_render_source("slides", "d.deck", deck)
expect(result.html_output).to_contain("Intro")
expect(result.html_output).to_contain("Roadmap")
expect(result.html_output).to_contain("<section class=\"slide\"")
```

</details>

### office render adapter: surface renderers reuse real models
_The demo models feed the same renderers the live surfaces use._

#### renders the demo sheet table from cell display values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = render_sheet_html(office_demo_sheet())
expect(table).to_start_with("<table")
expect(table).to_contain("<th")
expect(table).to_contain("1200")
```

</details>

#### produces a non-empty document and slide from the demo builders

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_document_html(office_demo_document())).to_contain("Highlights")
expect(render_slide_html(office_demo_slide())).to_contain("production-ready")
```

</details>

### office render adapter: conditional formatting and charts
_Calc feature modules (cond_format, chart) wired into the sheet grid render._

#### merges a matching rule's CSS into that cell's td and leaves non-matching cells unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Demo")
sheet.set_value("A1", "50")
sheet.set_value("A2", "150")
val css = "background:#fde7e9;color:#c00"
val rules = [CondRule(range: "A1:A2", kind: "cell_value", criteria: ">100", n: 0, css: css)]
val html = render_sheet_html_with_rules(sheet, rules)
val cells = html.split("<td")
var matched_td = ""
var unmatched_td = ""
for part in cells:
    if part.contains(">150<"):
        matched_td = part
    if part.contains(">50<"):
        unmatched_td = part
expect(matched_td).to_contain(css)
expect(unmatched_td).to_contain("border: 1px solid")
assert_false(unmatched_td.contains(css))
```

</details>

#### renders no CSS on any cell when no rule matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Demo")
sheet.set_value("A1", "5")
val rules = [CondRule(range: "A1:A1", kind: "cell_value", criteria: ">100", n: 0, css: "background:#fde7e9")]
val html = render_sheet_html_with_rules(sheet, rules)
expect(html).to_contain(">5<")
assert_false(html.contains("background:#fde7e9"))
```

</details>

#### embeds a chart SVG below the sheet grid in a titled section

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Demo")
sheet.set_value("A1", "Q1")
sheet.set_value("A2", "Q2")
sheet.set_value("B1", "10")
sheet.set_value("B2", "20")
val svg = sheet_bar_chart_svg(sheet, "A1:A2", "B1:B2", "Quarterly Totals")
val section = render_chart_section_html(svg, "Quarterly Totals")
expect(section).to_contain("<svg")
expect(section).to_contain("Quarterly Totals")
```

</details>

#### wires conditional formatting and a chart into the Calc surface export

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = RenderConfig.html_export()
cfg.adapter_name = "sheets"
val result = office_render(cfg)
val html = result.html_output
expect(html).to_contain("<svg")
expect(html).to_contain("Q1 Revenue vs Costs")
expect(html).to_contain("background:#d1fae5")
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
