# fill_series_edge_spec

> Office sheets fill-series edge-case spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fill_series_edge_spec

Office sheets fill-series edge-case spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/fill_series_edge_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets fill-series edge-case spec.

Backward fills, zero-padded labels, negative and fractional steps, mixed or
empty seeds, and every shape of malformed fill request.

## Scenarios

### sheet_fill_series: backward fills
_A target before the seed extends the series in reverse._

#### extends a numeric series upward

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("B1")
sheet.set_value("A5", "10")
sheet.set_value("A6", "12")

val written = sheet_fill_series(sheet, "A5:A6", "A3:A4")

assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("A4")) == "8")
assert_true(cell_display_text(sheet.get_cell("A3")) == "6")
```

</details>

#### extends a month cycle leftward across the list start

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("B2")
sheet.set_value("C1", "Feb")

val written = sheet_fill_series(sheet, "C1:C1", "A1:B1")

assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("B1")) == "Jan")
assert_true(cell_display_text(sheet.get_cell("A1")) == "Dec")
```

</details>

#### reverses a copy fill so the nearest cell repeats the last seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("B3")
sheet.set_value("A4", "red")
sheet.set_value("A5", "blue")

val written = sheet_fill_series(sheet, "A4:A5", "A2:A3")

assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("A3")) == "blue")
assert_true(cell_display_text(sheet.get_cell("A2")) == "red")
```

</details>

### fill_series_cells: numeric edges
_Negative and fractional steps stay linear._

#### handles a descending series through zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seed: [Cell] = [number_cell(2.0), number_cell(1.0)]
val out = fill_series_cells(seed, 3)
assert_true(cell_display_text(out[0]) == "0")
assert_true(cell_display_text(out[1]) == "-1")
assert_true(cell_display_text(out[2]) == "-2")
```

</details>

#### handles a fractional step

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seed: [Cell] = [number_cell(1.0), number_cell(1.5)]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "2")
assert_true(cell_display_text(out[1]) == "2.5")
```

</details>

### fill_series_cells: label edges
_Zero padding is preserved; non-numbered and mixed seeds copy._

#### preserves zero padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seed: [Cell] = [text_cell("Q007")]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "Q008")
assert_true(cell_display_text(out[1]) == "Q009")
```

</details>

#### keeps a bare number label as a numbered fill with an empty prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seed: [Cell] = [text_cell("41")]
val out = fill_series_cells(seed, 1)
assert_true(cell_display_text(out[0]) == "42")
```

</details>

#### copies labels whose prefixes differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seed: [Cell] = [text_cell("A1"), text_cell("B2")]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "A1")
assert_true(cell_display_text(out[1]) == "B2")
```

</details>

#### copies a seed mixing numbers and text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seed: [Cell] = [number_cell(1.0), text_cell("x")]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "1")
assert_true(cell_display_text(out[1]) == "x")
```

</details>

#### returns nothing for an empty seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seed: [Cell] = []
assert_true(fill_series_cells(seed, 3).len() == 3)
```

</details>

### sheet_fill_series: rejected requests
_Malformed or ambiguous fills write nothing and report 0._

#### rejects an unparseable range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("R1")
sheet.set_value("A1", "1")
assert_true(sheet_fill_series(sheet, "A1:A2", "not-a-range") == 0)
```

</details>

#### rejects a target in a different column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("R2")
sheet.set_value("A1", "1")
sheet.set_value("A2", "2")
assert_true(sheet_fill_series(sheet, "A1:A2", "B3:B4") == 0)
assert_true(cell_display_text(sheet.get_cell("B3")) == "")
```

</details>

#### rejects a target overlapping the seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("R3")
sheet.set_value("A1", "1")
sheet.set_value("A2", "2")
assert_true(sheet_fill_series(sheet, "A1:A2", "A2:A4") == 0)
```

</details>

#### rejects a rectangular target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("R4")
sheet.set_value("A1", "1")
assert_true(sheet_fill_series(sheet, "A1:A1", "B2:C3") == 0)
```

</details>

#### fills empty seed cells as an empty copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("R5")
val written = sheet_fill_series(sheet, "A1:A1", "A2:A3")
assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("A2")) == "")
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
