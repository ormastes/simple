# chart_spec

> Purpose: Prove that Calc charts: series and SVG.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chart_spec

Purpose: Prove that Calc charts: series and SVG.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/chart_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Calc charts: series and SVG.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Calc charts: series and SVG

#### collects labels and values, including computed formulas

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects labels and values, including computed formulas
- Verify: collects labels and values, including computed formulas
   - Expected: series.labels.len() equals `3`
   - Expected: series.labels[2] equals `Profit`
   - Expected: series.values[0] equals `1200.0`
   - Expected: series.values[2] equals `400.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("collects labels and values, including computed formulas")
step("Verify: collects labels and values, including computed formulas")
# @req: REQ-APP-OFFICE-001
val sh = _chart_sheet()
val series = chart_series_from_ranges(sh, "A1:A3", "B1:B3")
expect(series.labels.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(series.labels[2]).to_equal("Profit")
expect(series.values[0]).to_equal(1200.0)  # oracle: 1200.0 — named expected value from the requirement
expect(series.values[2]).to_equal(400.0)  # oracle: 400.0 — named expected value from the requirement
```

</details>

#### renders a self-contained SVG with a bar and value per row

- renders a self-contained SVG with a bar and value per row
- Verify: renders a self-contained SVG with a bar and value per row


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a self-contained SVG with a bar and value per row")
step("Verify: renders a self-contained SVG with a bar and value per row")
val sh = _chart_sheet()
val svg = sheet_bar_chart_svg(sh, "A1:A3", "B1:B3", "Q1 Budget")
expect(svg).to_start_with("<svg xmlns=")
expect(svg).to_contain("Q1 Budget")
expect(svg).to_contain("<rect")
expect(svg).to_contain(">Profit</text>")
expect(svg).to_contain(">400</text>")
```

</details>

#### escapes hostile labels and titles

- escapes hostile labels and titles
- Verify: escapes hostile labels and titles


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes hostile labels and titles")
step("Verify: escapes hostile labels and titles")
var sh = Sheet.new("c")
sh.set_value("A1", "<b>bad</b>")
sh.set_value("B1", "5")
val svg = sheet_bar_chart_svg(sh, "A1:A1", "B1:B1", "T<i>")
expect(svg).to_contain("&lt;b&gt;bad&lt;/b&gt;")
expect(svg).to_contain("T&lt;i&gt;")
expect(svg.contains("<b>")).to_be(false)
```

</details>

#### renders a no-data placeholder for empty ranges

- renders a no-data placeholder for empty ranges
- Verify: renders a no-data placeholder for empty ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a no-data placeholder for empty ranges")
step("Verify: renders a no-data placeholder for empty ranges")
val sh = Sheet.new("c")
val svg = sheet_bar_chart_svg(sh, "A1:A1", "B1:B1", "Empty")
expect(svg).to_contain("<svg")
```

</details>

#### renders a line chart with a polyline and x labels

- renders a line chart with a polyline and x labels
- Verify: renders a line chart with a polyline and x labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a line chart with a polyline and x labels")
step("Verify: renders a line chart with a polyline and x labels")
val sh = _chart_sheet()
val svg = sheet_line_chart_svg(sh, "A1:A3", "B1:B3", "Trend")
expect(svg).to_contain("<polyline")
expect(svg).to_contain("Trend")
expect(svg).to_contain("Profit")
```

</details>

#### renders a pie chart with donut segments and a value legend

- renders a pie chart with donut segments and a value legend
- Verify: renders a pie chart with donut segments and a value legend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a pie chart with donut segments and a value legend")
step("Verify: renders a pie chart with donut segments and a value legend")
val sh = _chart_sheet()
val svg = sheet_pie_chart_svg(sh, "A1:A3", "B1:B3", "Share")
expect(svg).to_contain("stroke-dasharray")
expect(svg).to_contain("Costs: 800")
```

</details>

### Calc charts: axis ticks, legend, area, scatter

#### puts nice Y-axis tick labels on the column chart

- puts nice Y-axis tick labels on the column chart
- Verify: puts nice Y-axis tick labels on the column chart


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("puts nice Y-axis tick labels on the column chart")
step("Verify: puts nice Y-axis tick labels on the column chart")
# values 1200/800/400 -> nice step 500 -> ticks 0,500,1000,1500
val sh = _chart_sheet()
val svg = sheet_bar_chart_svg(sh, "A1:A3", "B1:B3", "Q1 Budget")
expect(svg).to_contain(">0</text>")
expect(svg).to_contain(">500</text>")
expect(svg).to_contain(">1000</text>")
expect(svg).to_contain(">1500</text>")
```

</details>

#### draws a series legend with a swatch and name

- draws a series legend with a swatch and name
- Verify: draws a series legend with a swatch and name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("draws a series legend with a swatch and name")
step("Verify: draws a series legend with a swatch and name")
val sh = _chart_sheet()
val svg = sheet_bar_chart_svg(sh, "A1:A3", "B1:B3", "Q1 Budget")
expect(svg).to_contain("class=\"legend\"")
expect(svg).to_contain(">Series 1</text>")
```

</details>

#### renders an area chart with a fill polygon over a Y axis

- renders an area chart with a fill polygon over a Y axis
- Verify: renders an area chart with a fill polygon over a Y axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders an area chart with a fill polygon over a Y axis")
step("Verify: renders an area chart with a fill polygon over a Y axis")
val sh = _chart_sheet()
val svg = sheet_area_chart_svg(sh, "A1:A3", "B1:B3", "Trend")
expect(svg).to_contain("<polygon")
expect(svg).to_contain("fill-opacity")
expect(svg).to_contain("<polyline")
expect(svg).to_contain(">1000</text>")
expect(svg).to_contain(">Profit</text>")
```

</details>

#### renders a scatter chart with one circle per row and both axes

- renders a scatter chart with one circle per row and both axes
- Verify: renders a scatter chart with one circle per row and both axes
   - Expected: _count(svg, "<circle") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a scatter chart with one circle per row and both axes")
step("Verify: renders a scatter chart with one circle per row and both axes")
# X 1..4 -> ticks 1,2,3,4 ; Y max 80 -> nice step 20 -> ticks 0..80
val sh = _scatter_sheet()
val svg = sheet_scatter_chart_svg(sh, "C1:C4", "D1:D4", "XY")
expect(_count(svg, "<circle")).to_equal(4)
expect(svg).to_contain(">20</text>")
expect(svg).to_contain(">80</text>")
expect(svg).to_contain(">3</text>")
expect(svg).to_contain("class=\"legend\"")
```

</details>

#### renders a no-data placeholder for an empty scatter range

- renders a no-data placeholder for an empty scatter range
- Verify: renders a no-data placeholder for an empty scatter range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a no-data placeholder for an empty scatter range")
step("Verify: renders a no-data placeholder for an empty scatter range")
val sh = Sheet.new("s")
val svg = sheet_scatter_chart_svg(sh, "C1:C1", "D1:D1", "Empty")
expect(svg).to_contain("<svg")
```

</details>

### Calc charts: stacked bar, horizontal bar, donut

#### stacks series segments with Y ticks at the max stacked total

- stacks series segments with Y ticks at the max stacked total
- Verify: stacks series segments with Y ticks at the max stacked total
   - Expected: _count(svg, "class=\"seg\"") equals `4`
   - Expected: _count(svg, "class=\"legend\"") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stacks series segments with Y ticks at the max stacked total")
step("Verify: stacks series segments with Y ticks at the max stacked total")
# A=[10,20], B=[30,40] -> totals 40/60 -> nice step 20 -> ticks 0/20/40/60
# plot_h=222: Q2 segments 20/60*222=74 and 40/60*222=148 (exactly 2:1,
# i.e. proportional to 20:40); Q1 segments 37 and 111.
val sh = _stacked_sheet()
val svg = sheet_stacked_bar_chart_svg(sh, "A1:A2", "B1:B2,C1:C2", "Stacked")
expect(_count(svg, "class=\"seg\"")).to_equal(4)
expect(_count(svg, "class=\"legend\"")).to_equal(2)
expect(svg).to_contain(">20</text>")
expect(svg).to_contain(">40</text>")
expect(svg).to_contain(">60</text>")
expect(svg).to_contain("height=\"74\"")
expect(svg).to_contain("height=\"148\"")
expect(svg).to_contain("height=\"37\"")
expect(svg).to_contain("height=\"111\"")
expect(svg).to_contain(">Series 1</text>")
expect(svg).to_contain(">Series 2</text>")
expect(svg).to_contain(">Q2</text>")
```

</details>

#### renders horizontal bars growing rightward with left labels and X ticks

- renders horizontal bars growing rightward with left labels and X ticks
- Verify: renders horizontal bars growing rightward with left labels and X ticks
   - Expected: _count(svg, "class=\"hbar\"") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders horizontal bars growing rightward with left labels and X ticks")
step("Verify: renders horizontal bars growing rightward with left labels and X ticks")
# values [5,15] -> ticks 0/5/10/15; plot_w=255 -> widths 85 and 255
# (255 = 3*85: the 15-bar is exactly 3x the 5-bar)
val sh = _stacked_sheet()
val svg = sheet_hbar_chart_svg(sh, "A1:A2", "E1:E2", "HBar")
expect(_count(svg, "class=\"hbar\"")).to_equal(2)
expect(svg).to_contain("width=\"85\"")
expect(svg).to_contain("width=\"255\"")
# the 5-bar (Q1) comes before the 15-bar (Q2) in document order
val parts = svg.split("width=\"85\"")
expect(parts[0].contains("width=\"255\"")).to_be(false)
# horizontal orientation: category labels sit left of the axis
expect(svg).to_contain("text-anchor=\"end\">Q1</text>")
expect(svg).to_contain("text-anchor=\"end\">Q2</text>")
# value ticks live on the X axis
expect(svg).to_contain(">15</text>")
expect(svg).to_contain(">10</text>")
```

</details>

#### renders a donut with dasharray segments and the total in the center

- renders a donut with dasharray segments and the total in the center
- Verify: renders a donut with dasharray segments and the total in the center
   - Expected: _count(svg, "stroke-dasharray") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a donut with dasharray segments and the total in the center")
step("Verify: renders a donut with dasharray segments and the total in the center")
# values [5,15] -> total 20 in the donut hole; thin stroke = big hole
val sh = _stacked_sheet()
val svg = sheet_donut_chart_svg(sh, "A1:A2", "E1:E2", "Donut")
expect(_count(svg, "stroke-dasharray")).to_equal(2)
expect(svg).to_contain("stroke-width=\"30\"")
expect(svg).to_contain("text-anchor=\"middle\">20</text>")
expect(svg).to_contain("Q2: 15")
```

</details>

#### renders a no-data placeholder for empty stacked ranges

- renders a no-data placeholder for empty stacked ranges
- Verify: renders a no-data placeholder for empty stacked ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a no-data placeholder for empty stacked ranges")
step("Verify: renders a no-data placeholder for empty stacked ranges")
val sh = Sheet.new("st")
val svg = sheet_stacked_bar_chart_svg(sh, "A1:A1", "B1:B1", "Empty")
expect(svg).to_contain("<svg")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-OFFICE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `93de50b24f7755451105b1fbc1dd0a2837e5c68f50da2c57bbf721a691ad7b04`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93de50b24f7755451105b1fbc1dd0a2837e5c68f50da2c57bbf721a691ad7b04`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93de50b24f7755451105b1fbc1dd0a2837e5c68f50da2c57bbf721a691ad7b04`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/office/sheets/chart_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/chart_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/chart_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/chart_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/chart_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/sheets/chart_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects labels and values, including computed formulas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/chart_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a self-contained SVG with a bar and value per row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/chart_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes hostile labels and titles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
