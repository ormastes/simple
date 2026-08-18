# sheet_gui_view_spec

> Sheet GUI grid view spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheet_gui_view_spec

Sheet GUI grid view spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheet_gui_view_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet GUI grid view spec.

sheet_gui_view(sheet, max_rows, max_cols) builds the first real spreadsheet
UI surface: a WidgetNode table (rendered for real pixels by the CLI) plus a
plain-text pipe-separated grid dump (for testability without parsing
HTML/widget trees). The dump's first line is the header row ("|A|B|C|...");
each following line is "{row_num}|{cell1}|{cell2}|...". Rows in
sheet.hidden_rows are skipped entirely, so a filtered sheet renders
filtered.

## Scenarios

### sheet_gui_view: column headers and row numbers
_The grid dump always starts with a header line of column letters._

#### the header line lists column letters A, B, C in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val view = sheet_gui_view(sheet, 2, 3)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("|A|B|C")
```

</details>

#### each data row starts with its 1-based row number

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "x")
val view = sheet_gui_view(sheet, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("1|x")
```

</details>

### sheet_gui_view: cell display text
_Non-formula cell values show up verbatim in the grid dump._

#### contains a plain text cell's value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Hello")
val view = sheet_gui_view(sheet, 1, 1)
expect(view.text_dump).to_contain("Hello")
```

</details>

#### contains a numeric cell's display value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("B2", "42")
val view = sheet_gui_view(sheet, 2, 2)
expect(view.text_dump).to_contain("42")
```

</details>

### sheet_gui_view: formula cells show computed values

#### shows the computed SUM result, not the raw formula text

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "3")
sheet.set_value("A2", "4")
sheet.set_value("A3", "=SUM(A1:A2)")
sheet = recalculate_formula_cells(sheet)
val view = sheet_gui_view(sheet, 3, 1)
expect(view.text_dump).to_contain("7")
assert_false(_dump_contains(view.text_dump, "=SUM(A1:A2)"))
```

</details>

### sheet_gui_view: hidden rows are skipped

#### a hidden row's line is absent from the dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "keep-1")
sheet.set_value("A2", "hide-me")
sheet.set_value("A3", "keep-3")
sheet.hide_row(2)
val view = sheet_gui_view(sheet, 3, 1)
val lines = view.text_dump.split("\n")
var found_hidden = false
for line in lines:
    if line == "2|hide-me":
        found_hidden = true
expect(found_hidden).to_equal(false)
expect(view.text_dump).to_contain("keep-1")
expect(view.text_dump).to_contain("keep-3")
```

</details>

#### surrounding visible rows still render when a middle row is hidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "keep-1")
sheet.set_value("A2", "hide-me")
sheet.set_value("A3", "keep-3")
sheet.hide_row(2)
val view = sheet_gui_view(sheet, 3, 1)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("1|keep-1")
expect(lines[2]).to_equal("3|keep-3")
```

</details>

### sheet_gui_view: empty sheet

#### renders headers only when max_rows is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Empty")
val view = sheet_gui_view(sheet, 0, 3)
expect(view.text_dump).to_equal("|A|B|C")
```

</details>

#### an empty sheet's requested rows still render (blank cells, no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Empty")
val view = sheet_gui_view(sheet, 2, 2)
val lines = view.text_dump.split("\n")
expect(lines.len()).to_equal(3)
expect(lines[1]).to_equal("1||")
expect(lines[2]).to_equal("2||")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
