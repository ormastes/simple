# cell_format_spec

> Office sheets cell number-format and styling spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cell_format_spec

Office sheets cell number-format and styling spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/cell_format_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets cell number-format and styling spec.

Comprehensive tests for per-cell number formats and bold/bg/fg styling.
Tests formats_set/formats_get round-trip, format_cell_display's Excel
number-format subset, format_cell_css, and the render_sheet_html_formatted
render path (number format + style css + conditional-format rules).

## Scenarios

### formats_set / formats_get: round-trip

#### returns the general/default spec for a cell with no format set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formats = empty_sheet_formats()
val spec = formats_get(formats, "A1")
expect(spec.num_fmt).to_equal("")
expect(spec.bold).to_equal(false)
expect(spec.bg).to_equal("")
expect(spec.fg).to_equal("")
```

</details>

#### round-trips a set format

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "B2", FormatSpec(num_fmt: "0.00", bold: true, bg: "#ffe4b5", fg: "#7a2e00"))
val spec = formats_get(formats, "B2")
expect(spec.num_fmt).to_equal("0.00")
expect(spec.bold).to_equal(true)
expect(spec.bg).to_equal("#ffe4b5")
expect(spec.fg).to_equal("#7a2e00")
```

</details>

#### is case-insensitive on the cell reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "c3", FormatSpec(num_fmt: "0%", bold: false, bg: "", fg: ""))
val spec = formats_get(formats, "C3")
expect(spec.num_fmt).to_equal("0%")
```

</details>

#### overwrites an existing entry in place instead of appending

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "A1", FormatSpec(num_fmt: "0.00", bold: false, bg: "", fg: ""))
formats = formats_set(formats, "A1", FormatSpec(num_fmt: "0", bold: true, bg: "", fg: ""))
expect(formats.keys.len()).to_equal(1)
val spec = formats_get(formats, "A1")
expect(spec.num_fmt).to_equal("0")
expect(spec.bold).to_equal(true)
```

</details>

#### keeps distinct entries for distinct cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "A1", FormatSpec(num_fmt: "0.00", bold: false, bg: "", fg: ""))
formats = formats_set(formats, "A2", FormatSpec(num_fmt: "0%", bold: false, bg: "", fg: ""))
expect(formats.keys.len()).to_equal(2)
expect(formats_get(formats, "A1").num_fmt).to_equal("0.00")
expect(formats_get(formats, "A2").num_fmt).to_equal("0%")
```

</details>

### format_cell_display: number formats
_Excel TEXT()-style number format subset applied to numeric cells._

#### formats with two fixed decimals

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "1234.567")
var formats = empty_sheet_formats()
formats = formats_set(formats, "A1", FormatSpec(num_fmt: "0.00", bold: false, bg: "", fg: ""))
# 1234.567 * 100 = 123456.7 -> round half up -> 123457 -> 1234.57
val display = format_cell_display(sheet, formats, "A1")
expect(display).to_equal("1234.57")
```

</details>

#### formats with thousands grouping and two decimals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A2", "1234567.89")
var formats = empty_sheet_formats()
formats = formats_set(formats, "A2", FormatSpec(num_fmt: "#,##0.00", bold: false, bg: "", fg: ""))
val display = format_cell_display(sheet, formats, "A2")
expect(display).to_equal("1,234,567.89")
```

</details>

#### formats a percentage with one decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A3", "0.4567")
var formats = empty_sheet_formats()
formats = formats_set(formats, "A3", FormatSpec(num_fmt: "0.0%", bold: false, bg: "", fg: ""))
# 0.4567 * 100 = 45.67 -> round half up to 1 decimal -> 45.7%
val display = format_cell_display(sheet, formats, "A3")
expect(display).to_equal("45.7%")
```

</details>

#### formats an Excel date serial as yyyy-mm-dd

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
# Serial 46206 = days_from_civil(2026,7,3) [20637] + 25569 = 2026-07-03
sheet.set_value("A4", "46206")
var formats = empty_sheet_formats()
formats = formats_set(formats, "A4", FormatSpec(num_fmt: "yyyy-mm-dd", bold: false, bg: "", fg: ""))
val display = format_cell_display(sheet, formats, "A4")
expect(display).to_equal("2026-07-03")
```

</details>

#### falls back to the sheet's default general display when unformatted

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A5", "42")
val formats = empty_sheet_formats()
val display = format_cell_display(sheet, formats, "A5")
expect(display).to_equal("42")
```

</details>

#### falls back to general display for text cells even with a num_fmt set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A6", "hello")
var formats = empty_sheet_formats()
formats = formats_set(formats, "A6", FormatSpec(num_fmt: "0.00", bold: false, bg: "", fg: ""))
val display = format_cell_display(sheet, formats, "A6")
expect(display).to_equal("hello")
```

</details>

### format_cell_css: bold/bg/fg styling
_Inline CSS fragment generation, only present properties emitted._

#### returns empty css for the default (unset) spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formats = empty_sheet_formats()
val css = format_cell_css(formats, "A1")
expect(css).to_equal("")
```

</details>

#### emits bold only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "A1", FormatSpec(num_fmt: "", bold: true, bg: "", fg: ""))
val css = format_cell_css(formats, "A1")
expect(css).to_equal("font-weight:bold")
```

</details>

#### emits bold, background, and color in order, exact string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "A1", FormatSpec(num_fmt: "", bold: true, bg: "#ffe4b5", fg: "#7a2e00"))
val css = format_cell_css(formats, "A1")
expect(css).to_equal("font-weight:bold;background:#ffe4b5;color:#7a2e00")
```

</details>

#### emits only background when bold is false and fg is unset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "A1", FormatSpec(num_fmt: "", bold: false, bg: "#d1fae5", fg: ""))
val css = format_cell_css(formats, "A1")
expect(css).to_equal("background:#d1fae5")
```

</details>

### render_sheet_html_formatted: number format + style css + cond-format rules

#### renders a formatted number and its bold/bg style into the cell's td

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A1 is the bold "header" row per the grid convention (render_sheet_html*
# treats the first data row as a header); put the formatted value on A2
# so it's rendered as a real <td> data cell.
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Amount")
sheet.set_value("A2", "1234.567")
var formats = empty_sheet_formats()
formats = formats_set(formats, "A2", FormatSpec(num_fmt: "0.00", bold: true, bg: "#ffe4b5", fg: ""))
val html = render_sheet_html_formatted(sheet, formats, [])
expect(html).to_contain("1234.57")
expect(html).to_contain("font-weight:bold;background:#ffe4b5")
```

</details>

#### merges conditional-format css after the static format css

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Amount")
sheet.set_value("A2", "150")
var formats = empty_sheet_formats()
formats = formats_set(formats, "A2", FormatSpec(num_fmt: "0.00", bold: false, bg: "#111111", fg: ""))
val rule = CondRule(range: "A2:A10", kind: "cell_value", criteria: ">100", n: 0, css: "background:#fde7e9")
val html = render_sheet_html_formatted(sheet, formats, [rule])
expect(html).to_contain("150.00")
# static bg first, cond-format bg appended after (wins on conflict)
expect(html).to_contain("background:#111111;background:#fde7e9")
```

</details>

#### renders an unformatted cell with plain display and no extra style

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Amount")
sheet.set_value("A2", "42")
val formats = empty_sheet_formats()
val html = render_sheet_html_formatted(sheet, formats, [])
expect(html).to_contain("<td style=\"border: 1px solid #d0d7de; padding: 6px 12px;\">42</td>")
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
