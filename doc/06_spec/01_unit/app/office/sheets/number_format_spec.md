# number_format_spec

> Office sheets number-format-code spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# number_format_spec

Office sheets number-format-code spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/number_format_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets number-format-code spec.

Hand-verified cases for `format_number` (Excel Format-Cells number-code
subset: fixed decimals, thousands grouping, percent, generic currency
prefix, scientific notation, date serials, "@" text passthrough, general
fallback, negative numbers), the `sheet_set_number_format` registry helper,
and the `cell_display_formatted` end-to-end display path.

## Scenarios

### format_number: fixed decimals
_"0.00"-style codes: round-half-away-from-zero, zero-padded._

#### rounds 1234.567 to two decimals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1234.567 * 100 = 123456.7 -> +0.5 -> 123457.2 -> floor -> 1234.57
expect(format_number(1234.567, "0.00")).to_equal("1234.57")
```

</details>

#### rounds to three decimals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "0.000")).to_equal("1234.500")
```

</details>

#### rounds to a whole number with no decimal point

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "0")).to_equal("1235")
```

</details>

### format_number: thousands grouping
_"#,##0"-style codes._

#### groups thousands with two decimals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.567, "#,##0.00")).to_equal("1,234.57")
```

</details>

#### groups millions with no decimals, rounding up

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1234567.891 -> +0.5 -> 1234568.391 -> floor -> 1,234,568
expect(format_number(1234567.891, "#,##0")).to_equal("1,234,568")
```

</details>

### format_number: percent
_"0%"-style codes: value * 100 with a trailing '%'._

#### formats a percentage with one decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0.4567 * 100 = 45.67 -> round half up to 1 decimal -> 45.7%
expect(format_number(0.4567, "0.0%")).to_equal("45.7%")
```

</details>

#### formats a percentage with no decimals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(0.5, "0%")).to_equal("50%")
```

</details>

### format_number: currency / generic literal prefix

#### formats dollars with a currency prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "$#,##0.00")).to_equal("$1,234.50")
```

</details>

#### keeps a multi-character literal prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "USD #,##0.00")).to_equal("USD 1,234.50")
```

</details>

### format_number: scientific notation
_"0.00E+00"-style codes: mantissa in [1,10) + 2-digit signed exponent._

#### formats 12345.6789 in scientific notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 12345.6789 = 1.23456789e4 -> mantissa rounds to 1.23, exponent 4
expect(format_number(12345.6789, "0.00E+00")).to_equal("1.23E+04")
```

</details>

### format_number: dates

#### formats an Excel date serial as yyyy-mm-dd

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "yyyy-mm-dd")).to_equal("2023-06-30")
```

</details>

#### formats the same serial as mm/dd/yyyy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "mm/dd/yyyy")).to_equal("06/30/2023")
```

</details>

#### formats the same serial as dd.mm.yyyy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "dd.mm.yyyy")).to_equal("30.06.2023")
```

</details>

### format_number: negative numbers
_A plain '-' prefix ahead of the formatted magnitude._

#### prefixes a minus sign for a negative grouped value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(-1234.5, "#,##0.00")).to_equal("-1,234.50")
```

</details>

#### prefixes a minus sign ahead of a currency literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(-1234.5, "$#,##0.00")).to_equal("-$1,234.50")
```

</details>

### format_number: fallbacks
_"@"/'' and unknown codes never error the display path._

#### falls back to general for an empty code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(42.0, "")).to_equal("42")
```

</details>

#### trims a whole-number value under general display

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(3.0, "")).to_equal("3")
```

</details>

#### keeps a fractional value under general display

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(3.5, "")).to_equal("3.5")
```

</details>

#### falls back to general for an unrecognized code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(42.5, "???")).to_equal("42.5")
```

</details>

### sheet_set_number_format: registry
_Sets only the number-format code, preserving existing bold/bg/fg._

#### sets a number format on a cell with no prior format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "B2", "0.00")
val spec = formats_get(formats, "B2")
expect(spec.num_fmt).to_equal("0.00")
expect(spec.bold).to_equal(false)
```

</details>

#### preserves existing bold/bg/fg when only the number format changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var formats = empty_sheet_formats()
formats = formats_set(formats, "B2", FormatSpec(num_fmt: "0", bold: true, bg: "#ffe4b5", fg: "#7a2e00"))
formats = sheet_set_number_format(formats, "B2", "#,##0.00")
val spec = formats_get(formats, "B2")
expect(spec.num_fmt).to_equal("#,##0.00")
expect(spec.bold).to_equal(true)
expect(spec.bg).to_equal("#ffe4b5")
expect(spec.fg).to_equal("#7a2e00")
```

</details>

### cell_display_formatted: end-to-end display

#### formats a plain numeric cell with a set number format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "1234.567")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "A1", "0.00")
expect(cell_display_formatted(sheet, formats, "A1")).to_equal("1234.57")
```

</details>

#### formats a formula cell's numeric result

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("B1", "2")
sheet.set_value("B2", "3")
sheet.set_value("B3", "=B1+B2")
sheet = recalculate_formula_cells(sheet)
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "B3", "0.00")
expect(cell_display_formatted(sheet, formats, "B3")).to_equal("5.00")
```

</details>

#### passes a text cell through unchanged regardless of any code

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("C1", "hello")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "C1", "@")
expect(cell_display_formatted(sheet, formats, "C1")).to_equal("hello")
```

</details>

#### falls back to plain display when no format is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("D1", "42")
val formats = empty_sheet_formats()
expect(cell_display_formatted(sheet, formats, "D1")).to_equal("42")
```

</details>

### format_number: multi-section codes -- 2 sections (positive+zero / negative)

#### uses section 1 for a positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "#,##0.00;-#,##0.00")).to_equal("1,234.50")
```

</details>

#### uses section 1 for a zero value (positive+zero share section 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(0.0, "#,##0.00;(#,##0.00)")).to_equal("0.00")
```

</details>

#### applies section 2's own literal minus to the absolute value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(-1234.5, "#,##0.00;-#,##0.00")).to_equal("-1,234.50")
```

</details>

#### wraps a negative value in parentheses per the parenthesized negative section

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hand-verified: Excel's classic accounting negative style.
expect(format_number(-1234.5, "#,##0.00;(#,##0.00)")).to_equal("(1,234.50)")
```

</details>

### format_number: multi-section codes -- 3 sections (positive/negative/zero)

#### uses section 1 for a positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "#,##0.00;(#,##0.00);\"-\"")).to_equal("1,234.50")
```

</details>

#### uses section 2 (parens) for a negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(-1234.5, "#,##0.00;(#,##0.00);\"-\"")).to_equal("(1,234.50)")
```

</details>

#### uses section 3 (a quoted literal) for a zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hand-verified: a common accounting idiom -- render zero as a dash.
expect(format_number(0.0, "#,##0.00;(#,##0.00);\"-\"")).to_equal("-")
```

</details>

### format_number: multi-section codes -- 4 sections (+ text, numeric side)

#### still uses section 1 for a positive value when a 4th section is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "#,##0.00;(#,##0.00);\"-\";\"txt\"")).to_equal("1,234.50")
```

</details>

### format_text_with_code: the text (4th) section

#### substitutes '@' with the text value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_text_with_code("abc", "#,##0.00;(#,##0.00);\"-\";\"Value: \"@")).to_equal("Value: abc")
```

</details>

#### substitutes '@' with no surrounding literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_text_with_code("hello", "0;0;0;@")).to_equal("hello")
```

</details>

#### passes text through unchanged when the code has fewer than 4 sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_text_with_code("hi", "0.00")).to_equal("hi")
```

</details>

### format_number: color tags are stripped and ignored

#### strips a [Red] tag ahead of a negative section's literal minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(-1234.5, "#,##0.00;[Red]-#,##0.00")).to_equal("-1,234.50")
```

</details>

#### strips a [Blue] tag ahead of the positive section

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "[Blue]#,##0.00;-#,##0.00")).to_equal("1,234.50")
```

</details>

### format_number: quote-aware section splitting

#### does not split on a ';' that appears inside a quoted literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If splitting were quote-BLIND this would wrongly become 3
# sections ("x, "\"x", "y\"0.00", "-0.00") instead of 2.
expect(format_number(1234.5, "\"x;y\"0.00;-0.00")).to_equal("x;y1234.50")
```

</details>

### format_number: dates -- dd/mm vs mm/dd distinction

#### renders dd/mm/yyyy with the day first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "dd/mm/yyyy")).to_equal("30/06/2023")
```

</details>

#### renders mm/dd/yyyy with the month first (unchanged regression)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "mm/dd/yyyy")).to_equal("06/30/2023")
```

</details>

#### renders a 2-digit year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "dd/mm/yy")).to_equal("30/06/23")
```

</details>

#### renders single-digit day/month with no zero-padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Serial 45082 = 2023-06-05 (25 days before serial 45107's 2023-06-30).
expect(format_number(45082.0, "d/m/yyyy")).to_equal("5/6/2023")
```

</details>

### format_number: dates -- month names

#### renders the abbreviated month name (mmm)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "dd-mmm-yyyy")).to_equal("30-Jun-2023")
```

</details>

#### renders the full month name (mmmm)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(45107.0, "mmmm dd, yyyy")).to_equal("June 30, 2023")
```

</details>

### format_number: thousands-scaling commas

#### scales by one million with two trailing commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hand-verified: 12,345,678 / 1,000,000 = 12.345678 -> 1 decimal -> 12.3
expect(format_number(12345678.0, "0.0,,")).to_equal("12.3")
```

</details>

#### scales by one thousand with a single trailing comma, still grouped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 12,345,678 / 1,000 = 12345.678 -> round to int -> 12,346
expect(format_number(12345678.0, "#,##0,")).to_equal("12,346")
```

</details>

#### does not confuse a mid-pattern grouping comma with a scaling comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "#,##0.00")).to_equal("1,234.50")
```

</details>

### format_number: '?' digit placeholder

#### extends the digit run without changing the rendered value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "#,##0.0?")).to_equal("1,234.5")
```

</details>

### format_number: quoted literal suffix/prefix

#### renders a quoted literal unit suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1.5, "0.00 \"kg\"")).to_equal("1.50 kg")
```

</details>

#### renders a quoted literal currency prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_number(1234.5, "\"USD \"#,##0.00")).to_equal("USD 1,234.50")
```

</details>

### cell_display_formatted: text cells with a 4-section code

#### applies the text section to a text cell's display

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("E1", "world")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "E1", "0;0;0;\"Hi \"@")
expect(cell_display_formatted(sheet, formats, "E1")).to_equal("Hi world")
```

</details>

#### leaves a text cell unchanged when the code has fewer than 4 sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("F1", "world")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "F1", "0.00")
expect(cell_display_formatted(sheet, formats, "F1")).to_equal("world")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
