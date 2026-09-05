# cond_format_spec

> Office sheets conditional formatting spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cond_format_spec

Office sheets conditional formatting spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/cond_format_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets conditional formatting spec.

Comprehensive tests for conditional formatting rules.
Tests cell_value criteria, top_n highlighting, color scale interpolation,
data bars, above/below average matching, and unique/duplicate matching.

## Scenarios

### cond_css_for_cell: cell_value criteria
_Match cells by numeric comparison operators and text equality._

#### matches cell value with > operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "150")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9;color:#c00"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("background:#fde7e9;color:#c00")
```

</details>

#### does not match cell value when criteria not met

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "50")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9;color:#c00"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("")
```

</details>

#### matches cell value with <= operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A2", "50")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: "<=100",
    n: 0,
    css: "background:#fff3cd"
)

val result = cond_css_for_cell(sheet, [rule], "A2")
expect(result).to_equal("background:#fff3cd")
```

</details>

#### matches text with case-insensitive equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Error")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: "error",
    n: 0,
    css: "background:#ffcccc"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("background:#ffcccc")
```

</details>

### cond_css_for_cell: first-match-wins
_When multiple rules match, return CSS of first matching rule._

#### returns first matching rule when multiple overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "150")

val rule1 = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9"
)

val rule2 = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: ">50",
    n: 0,
    css: "background:#fff3cd"
)

val result = cond_css_for_cell(sheet, [rule1, rule2], "A1")
expect(result).to_equal("background:#fde7e9")
```

</details>

### cond_css_for_cell: top_n highlighting
_Highlight cells among the top N values in a range._

#### identifies top 2 values in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
# Values: 5, 30, 10, 20
sheet.set_value("A1", "5")
sheet.set_value("A2", "30")
sheet.set_value("A3", "10")
sheet.set_value("A4", "20")

val rule = CondRule(
    range: "A1:A4",
    kind: "top_n",
    criteria: "",
    n: 2,
    css: "background:#c6efce"
)

# 30 is top 1
val result_a2 = cond_css_for_cell(sheet, [rule], "A2")
expect(result_a2).to_equal("background:#c6efce")

# 20 is top 2
val result_a4 = cond_css_for_cell(sheet, [rule], "A4")
expect(result_a4).to_equal("background:#c6efce")

# 10 is not in top 2
val result_a3 = cond_css_for_cell(sheet, [rule], "A3")
expect(result_a3).to_equal("")

# 5 is not in top 2
val result_a1 = cond_css_for_cell(sheet, [rule], "A1")
expect(result_a1).to_equal("")
```

</details>

#### top_n returns empty for non-numeric cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "text")

val rule = CondRule(
    range: "A1:A1",
    kind: "top_n",
    criteria: "",
    n: 1,
    css: "background:#c6efce"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("")
```

</details>

### cond_css_for_cell: out of range
_Rules should not apply to cells outside their range._

#### does not apply rule to cell outside range

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "150")
sheet.set_value("B1", "150")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9"
)

# A1 is in range
val result_a1 = cond_css_for_cell(sheet, [rule], "A1")
expect(result_a1).to_equal("background:#fde7e9")

# B1 is outside range A1:A10
val result_b1 = cond_css_for_cell(sheet, [rule], "B1")
expect(result_b1).to_equal("")
```

</details>

### cond_format_range_css: range formatting
_Format all cells in a range and return CSS entries for matches._

#### formats multiple cells in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "50")
sheet.set_value("A2", "150")
sheet.set_value("A3", "75")

val rule = CondRule(
    range: "A1:A3",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9"
)

val result = cond_format_range_css(sheet, [rule], "A1:A3")

# Only A2 (150) should match
expect(result.len()).to_equal(1)
if result.len() >= 1:
    expect(result[0]).to_contain("A2:")
    expect(result[0]).to_contain("background:#fde7e9")
```

</details>

#### skips cells with no matching rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "10")
sheet.set_value("A2", "20")
sheet.set_value("A3", "30")

val rule = CondRule(
    range: "A1:A3",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9"
)

val result = cond_format_range_css(sheet, [rule], "A1:A3")

# No cells match >100
expect(result.len()).to_equal(0)
```

</details>

#### returns row-major order

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
# Set up a 2x2 grid with top-left and bottom-right matching
sheet.set_value("A1", "150")
sheet.set_value("A2", "50")
sheet.set_value("B1", "50")
sheet.set_value("B2", "150")

val rule = CondRule(
    range: "A1:B2",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9"
)

val result = cond_format_range_css(sheet, [rule], "A1:B2")

# Should have 2 results
expect(result.len()).to_equal(2)

# Row-major order: A1, then A2, then B1, then B2
if result.len() >= 2:
    expect(result[0]).to_start_with("A1:")
    expect(result[1]).to_start_with("B2:")
```

</details>

### cond_css_for_cell: color_scale
_Linear color interpolation between min and max values._

#### interpolates white to green across the range

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "0")
sheet.set_value("A2", "50")
sheet.set_value("A3", "100")

val rule = CondRule(
    range: "A1:A3",
    kind: "color_scale",
    criteria: "",
    n: 0,
    css: ""  # CSS is computed per value, not static
)

# min -> white, max -> #63be7b, midpoint per-channel round half up:
# r (255+99)/2=177=b1, g (255+190)/2=222.5->223=df, b (255+123)/2=189=bd
expect(cond_css_for_cell(sheet, [rule], "A1")).to_equal("background:#ffffff")
expect(cond_css_for_cell(sheet, [rule], "A2")).to_equal("background:#b1dfbd")
expect(cond_css_for_cell(sheet, [rule], "A3")).to_equal("background:#63be7b")
```

</details>

#### gives the max color to a degenerate single-value range

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "42")

val rule = CondRule(
    range: "A1:A1",
    kind: "color_scale",
    criteria: "",
    n: 0,
    css: ""
)

expect(cond_css_for_cell(sheet, [rule], "A1")).to_equal("background:#63be7b")
```

</details>

#### skips non-numeric cells for color_scale

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "text")

val rule = CondRule(
    range: "A1:A10",
    kind: "color_scale",
    criteria: "",
    n: 0,
    css: ""
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("")
```

</details>

### cond_css_for_cell: data_bar, above/below average, unique/duplicate
_Excel-style data bars, average matchers, and text occurrence matchers._

#### data_bar computes proportional bar percentage over the range

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "10")
sheet.set_value("A2", "20")
sheet.set_value("A3", "30")
sheet.set_value("A4", "40")

val rule = CondRule(
    range: "A1:A4",
    kind: "data_bar",
    criteria: "",
    n: 0,
    css: ""  # CSS is computed per value, not static
)

# P = (value - min) / (max - min) * 100, rounded to integer.
# A3: (30-10)/30*100 = 66.67 -> 67
val a3 = cond_css_for_cell(sheet, [rule], "A3")
expect(a3).to_equal("background:linear-gradient(to right, #638ec6 67%, transparent 67%)")
expect(a3).to_contain("67%")
# A1 is the minimum -> 0%
expect(cond_css_for_cell(sheet, [rule], "A1")).to_contain(" 0%")
# A4 is the maximum -> 100%
expect(cond_css_for_cell(sheet, [rule], "A4")).to_contain("100%")
# A2: (20-10)/30*100 = 33.33 -> 33
expect(cond_css_for_cell(sheet, [rule], "A2")).to_contain("33%")
```

</details>

#### data_bar gives a full bar to a degenerate single-value range

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "42")

val rule = CondRule(
    range: "A1:A1",
    kind: "data_bar",
    criteria: "",
    n: 0,
    css: ""
)

# Degenerate range (max == min): documented as full bar, P = 100,
# mirroring color_scale's degenerate max-color rule.
val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("background:linear-gradient(to right, #638ec6 100%, transparent 100%)")
```

</details>

#### data_bar returns empty for non-numeric cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "text")
sheet.set_value("A2", "10")

val rule = CondRule(
    range: "A1:A4",
    kind: "data_bar",
    criteria: "",
    n: 0,
    css: ""
)

expect(cond_css_for_cell(sheet, [rule], "A1")).to_equal("")
# Empty cell in range also gets no bar
expect(cond_css_for_cell(sheet, [rule], "A3")).to_equal("")
```

</details>

#### keeps first-match-wins ordering with a data_bar rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "10")
sheet.set_value("A2", "40")

val rule1 = CondRule(
    range: "A1:A2",
    kind: "cell_value",
    criteria: ">30",
    n: 0,
    css: "background:#fde7e9"
)
val rule2 = CondRule(
    range: "A1:A2",
    kind: "data_bar",
    criteria: "",
    n: 0,
    css: ""
)

# A2 matches the earlier cell_value rule -> its static css wins
expect(cond_css_for_cell(sheet, [rule1, rule2], "A2")).to_equal("background:#fde7e9")
# A1 falls through to the data_bar rule
expect(cond_css_for_cell(sheet, [rule1, rule2], "A1")).to_contain("linear-gradient")
```

</details>

#### above_average matches values strictly above the mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
# Mean of 10, 20, 30, 40 is 25
sheet.set_value("A1", "10")
sheet.set_value("A2", "20")
sheet.set_value("A3", "30")
sheet.set_value("A4", "40")

val rule = CondRule(
    range: "A1:A4",
    kind: "above_average",
    criteria: "",
    n: 0,
    css: "background:#c6efce"
)

expect(cond_css_for_cell(sheet, [rule], "A3")).to_equal("background:#c6efce")
expect(cond_css_for_cell(sheet, [rule], "A4")).to_equal("background:#c6efce")
expect(cond_css_for_cell(sheet, [rule], "A1")).to_equal("")
expect(cond_css_for_cell(sheet, [rule], "A2")).to_equal("")
```

</details>

#### below_average matches values strictly below the mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "10")
sheet.set_value("A2", "20")
sheet.set_value("A3", "30")
sheet.set_value("A4", "40")

val rule = CondRule(
    range: "A1:A4",
    kind: "below_average",
    criteria: "",
    n: 0,
    css: "background:#fde7e9"
)

expect(cond_css_for_cell(sheet, [rule], "A1")).to_equal("background:#fde7e9")
expect(cond_css_for_cell(sheet, [rule], "A2")).to_equal("background:#fde7e9")
expect(cond_css_for_cell(sheet, [rule], "A3")).to_equal("")
expect(cond_css_for_cell(sheet, [rule], "A4")).to_equal("")
```

</details>

#### value equal to the mean matches neither above nor below

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
# Mean of 10, 20, 30 is exactly 20
sheet.set_value("A1", "10")
sheet.set_value("A2", "20")
sheet.set_value("A3", "30")

val above = CondRule(
    range: "A1:A3",
    kind: "above_average",
    criteria: "",
    n: 0,
    css: "background:#c6efce"
)
val below = CondRule(
    range: "A1:A3",
    kind: "below_average",
    criteria: "",
    n: 0,
    css: "background:#fde7e9"
)

expect(cond_css_for_cell(sheet, [above], "A2")).to_equal("")
expect(cond_css_for_cell(sheet, [below], "A2")).to_equal("")
```

</details>

#### excludes empty and non-numeric cells from the mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
# Range A1:A6: numbers 10, 20, 30, 40 (mean 25); A5 empty, A6 text.
sheet.set_value("A1", "10")
sheet.set_value("A2", "20")
sheet.set_value("A3", "30")
sheet.set_value("A4", "40")
sheet.set_value("A6", "note")

val rule = CondRule(
    range: "A1:A6",
    kind: "above_average",
    criteria: "",
    n: 0,
    css: "background:#c6efce"
)

# If empty/text counted, the mean would drop and 20 would match.
expect(cond_css_for_cell(sheet, [rule], "A2")).to_equal("")
expect(cond_css_for_cell(sheet, [rule], "A3")).to_equal("background:#c6efce")
# Non-numeric and empty cells never match themselves
expect(cond_css_for_cell(sheet, [rule], "A5")).to_equal("")
expect(cond_css_for_cell(sheet, [rule], "A6")).to_equal("")
```

</details>

#### duplicate matches display texts occurring more than once (case-insensitive)

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "a")
sheet.set_value("A2", "B")
sheet.set_value("A3", "A")
sheet.set_value("A4", "c")

val rule = CondRule(
    range: "A1:A4",
    kind: "duplicate",
    criteria: "",
    n: 0,
    css: "background:#ffc7ce"
)

expect(cond_css_for_cell(sheet, [rule], "A1")).to_equal("background:#ffc7ce")
expect(cond_css_for_cell(sheet, [rule], "A3")).to_equal("background:#ffc7ce")
expect(cond_css_for_cell(sheet, [rule], "A2")).to_equal("")
expect(cond_css_for_cell(sheet, [rule], "A4")).to_equal("")
```

</details>

#### unique matches display texts occurring exactly once (case-insensitive)

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "a")
sheet.set_value("A2", "B")
sheet.set_value("A3", "A")
sheet.set_value("A4", "c")

val rule = CondRule(
    range: "A1:A5",
    kind: "unique",
    criteria: "",
    n: 0,
    css: "background:#c6efce"
)

expect(cond_css_for_cell(sheet, [rule], "A2")).to_equal("background:#c6efce")
expect(cond_css_for_cell(sheet, [rule], "A4")).to_equal("background:#c6efce")
expect(cond_css_for_cell(sheet, [rule], "A1")).to_equal("")
expect(cond_css_for_cell(sheet, [rule], "A3")).to_equal("")
# Empty cell in range never matches unique
expect(cond_css_for_cell(sheet, [rule], "A5")).to_equal("")
```

</details>

### cond_css_for_cell: unknown rule kind
_Unknown rule kinds should not match._

#### returns empty for unknown rule kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "100")

val rule = CondRule(
    range: "A1:A10",
    kind: "unknown_kind",
    criteria: ">50",
    n: 0,
    css: "background:#fde7e9"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("")
```

</details>

### cond_css_for_cell: empty and missing cells
_Handle empty cells and missing references._

#### returns empty for missing cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: ">100",
    n: 0,
    css: "background:#fde7e9"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("")  # Missing cells are empty, don't match >100
```

</details>

### cond_css_for_cell: comparison operators
_Test various numeric comparison operators._

#### matches with >= operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "100")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: ">=100",
    n: 0,
    css: "background:#c6efce"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("background:#c6efce")
```

</details>

#### matches with <> (not equal) operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "50")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: "<>100",
    n: 0,
    css: "background:#fff3cd"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("background:#fff3cd")
```

</details>

#### does not match with <> when values are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "100")

val rule = CondRule(
    range: "A1:A10",
    kind: "cell_value",
    criteria: "<>100",
    n: 0,
    css: "background:#fff3cd"
)

val result = cond_css_for_cell(sheet, [rule], "A1")
expect(result).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
