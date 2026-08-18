# Data Ops2 Specification

> Tests covering sheet_remove_duplicates: basic dedupe, sheet_remove_duplicates: keys and edge cases, sheet_text_to_columns: splitting, sheet_subtotals: grouping and sums.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Data Ops2 Specification

## Scenarios

### sheet_remove_duplicates: basic dedupe
_Keeps FIRST occurrence per key combination; case-insensitive keys._

#### removes case-insensitive duplicates and clears the tail

<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ground truth: (a,1),(b,2),(a,3),(A,4) key col 0 ->
# keeps (a,1),(b,2); A dup of a (case-insensitive); rows 3-4 cleared
var sheet = Sheet.new("S1")
sheet.set_value("A1", "a")
sheet.set_value("B1", "1")
sheet.set_value("A2", "b")
sheet.set_value("B2", "2")
sheet.set_value("A3", "a")
sheet.set_value("B3", "3")
sheet.set_value("A4", "A")
sheet.set_value("B4", "4")

val out = sheet_remove_duplicates(sheet, "A1:B4", "0", false)

val a1 = out.get_cell("A1")
val a1_text = cell_display_text(a1)
assert_true(a1_text == "a")
val b1 = out.get_cell("B1")
match b1.value:
    CellValue.NumberVal(v):
        assert_true(v == 1.0)
    _:
        assert_true(false)
val a2 = out.get_cell("A2")
val a2_text = cell_display_text(a2)
assert_true(a2_text == "b")
val b2 = out.get_cell("B2")
match b2.value:
    CellValue.NumberVal(v):
        assert_true(v == 2.0)
    _:
        assert_true(false)
# Rows 3 and 4 cleared
val a3 = out.get_cell("A3")
match a3.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
val b3 = out.get_cell("B3")
match b3.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
val a4 = out.get_cell("A4")
match a4.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
val b4 = out.get_cell("B4")
match b4.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### leaves a range with no duplicates unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S2")
sheet.set_value("A1", "x")
sheet.set_value("A2", "y")
sheet.set_value("A3", "z")

val out = sheet_remove_duplicates(sheet, "A1:A3", "0", false)

val a1 = out.get_cell("A1")
val a1_text = cell_display_text(a1)
assert_true(a1_text == "x")
val a2 = out.get_cell("A2")
val a2_text = cell_display_text(a2)
assert_true(a2_text == "y")
val a3 = out.get_cell("A3")
val a3_text = cell_display_text(a3)
assert_true(a3_text == "z")
```

</details>

#### preserves the header row when has_header is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S3")
sheet.set_value("A1", "key")
sheet.set_value("B1", "val")
sheet.set_value("A2", "a")
sheet.set_value("B2", "1")
sheet.set_value("A3", "a")
sheet.set_value("B3", "2")

val out = sheet_remove_duplicates(sheet, "A1:B3", "0", true)

# Header intact
val a1 = out.get_cell("A1")
val a1_text = cell_display_text(a1)
assert_true(a1_text == "key")
val b1 = out.get_cell("B1")
val b1_text = cell_display_text(b1)
assert_true(b1_text == "val")
# First data row kept, second (duplicate key) cleared
val a2 = out.get_cell("A2")
val a2_text = cell_display_text(a2)
assert_true(a2_text == "a")
val b2 = out.get_cell("B2")
match b2.value:
    CellValue.NumberVal(v):
        assert_true(v == 1.0)
    _:
        assert_true(false)
val a3 = out.get_cell("A3")
match a3.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

### sheet_remove_duplicates: keys and edge cases
_Multi-column keys, empty-cell keys, invalid key_cols._

#### dedupes on multi-column keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# (a,1),(a,1),(a,2) keys "0,1" -> keeps (a,1),(a,2)
var sheet = Sheet.new("S4")
sheet.set_value("A1", "a")
sheet.set_value("B1", "1")
sheet.set_value("A2", "a")
sheet.set_value("B2", "1")
sheet.set_value("A3", "a")
sheet.set_value("B3", "2")

val out = sheet_remove_duplicates(sheet, "A1:B3", "0,1", false)

val b1 = out.get_cell("B1")
match b1.value:
    CellValue.NumberVal(v):
        assert_true(v == 1.0)
    _:
        assert_true(false)
val b2 = out.get_cell("B2")
match b2.value:
    CellValue.NumberVal(v):
        assert_true(v == 2.0)
    _:
        assert_true(false)
val a3 = out.get_cell("A3")
match a3.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### treats empty key cells as equal keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A1 empty + B1=1, A2 empty + B2=2, key col 0 -> row 2 is a duplicate
var sheet = Sheet.new("S5")
sheet.set_value("B1", "1")
sheet.set_value("B2", "2")

val out = sheet_remove_duplicates(sheet, "A1:B2", "0", false)

val b1 = out.get_cell("B1")
match b1.value:
    CellValue.NumberVal(v):
        assert_true(v == 1.0)
    _:
        assert_true(false)
val b2 = out.get_cell("B2")
match b2.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### returns the sheet unchanged on invalid key_cols

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S6")
sheet.set_value("A1", "a")
sheet.set_value("A2", "a")

# Out-of-range column index
val out1 = sheet_remove_duplicates(sheet, "A1:A2", "5", false)
val a2a = out1.get_cell("A2")
val a2a_text = cell_display_text(a2a)
assert_true(a2a_text == "a")

# Non-numeric key_cols
val out2 = sheet_remove_duplicates(sheet, "A1:A2", "x", false)
val a2b = out2.get_cell("A2")
val a2b_text = cell_display_text(a2b)
assert_true(a2b_text == "a")
```

</details>

### sheet_text_to_columns: splitting
_Split display text on delimiter into adjacent columns rightward._

#### splits pieces into adjacent columns, first piece in place

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ground truth: ["x,y","p,q,r"] delim "," -> B gets y/q, C gets r
var sheet = Sheet.new("T1")
sheet.set_value("A1", "x,y")
sheet.set_value("A2", "p,q,r")

val out = sheet_text_to_columns(sheet, "A1:A2", ",")

val a1 = out.get_cell("A1")
val a1_text = cell_display_text(a1)
assert_true(a1_text == "x")
val b1 = out.get_cell("B1")
val b1_text = cell_display_text(b1)
assert_true(b1_text == "y")
val a2 = out.get_cell("A2")
val a2_text = cell_display_text(a2)
assert_true(a2_text == "p")
val b2 = out.get_cell("B2")
val b2_text = cell_display_text(b2)
assert_true(b2_text == "q")
val c2 = out.get_cell("C2")
val c2_text = cell_display_text(c2)
assert_true(c2_text == "r")
# C1 untouched (only two pieces in row 1)
val c1 = out.get_cell("C1")
match c1.value:
    CellValue.Empty:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

#### leaves cells without the delimiter untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("T2")
sheet.set_value("A1", "hello")
sheet.set_value("B1", "keep")

val out = sheet_text_to_columns(sheet, "A1:A1", ",")

val a1 = out.get_cell("A1")
val a1_text = cell_display_text(a1)
assert_true(a1_text == "hello")
val b1 = out.get_cell("B1")
val b1_text = cell_display_text(b1)
assert_true(b1_text == "keep")
```

</details>

#### overwrites existing content in adjacent columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("T3")
sheet.set_value("A1", "x,y")
sheet.set_value("B1", "OLD")

val out = sheet_text_to_columns(sheet, "A1:A1", ",")

val b1 = out.get_cell("B1")
val b1_text = cell_display_text(b1)
assert_true(b1_text == "y")
```

</details>

#### ignores multi-column ranges and empty delimiters

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("T4")
sheet.set_value("A1", "x,y")
sheet.set_value("B1", "keep")

# Multi-column range -> no-op
val out1 = sheet_text_to_columns(sheet, "A1:B1", ",")
val a1a = out1.get_cell("A1")
val a1a_text = cell_display_text(a1a)
assert_true(a1a_text == "x,y")
val b1a = out1.get_cell("B1")
val b1a_text = cell_display_text(b1a)
assert_true(b1a_text == "keep")

# Empty delimiter -> no-op
val out2 = sheet_text_to_columns(sheet, "A1:A1", "")
val a1b = out2.get_cell("A1")
val a1b_text = cell_display_text(a1b)
assert_true(a1b_text == "x,y")
```

</details>

### sheet_subtotals: grouping and sums
_Group by display text (first-seen order); numeric sums per group._

#### sums values per group with a grand total

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ground truth: (east,10),(west,20),(east,5) ->
# ["east: 15","west: 20","Grand Total: 35"]
var sheet = Sheet.new("U1")
sheet.set_value("A1", "east")
sheet.set_value("B1", "10")
sheet.set_value("A2", "west")
sheet.set_value("B2", "20")
sheet.set_value("A3", "east")
sheet.set_value("B3", "5")

val lines = sheet_subtotals(sheet, "A1:B3", 0, 1)

assert_true(lines.len() == 3)
val l0 = lines[0]
assert_true(l0 == "east: 15")
val l1 = lines[1]
assert_true(l1 == "west: 20")
val l2 = lines[2]
assert_true(l2 == "Grand Total: 35")
```

</details>

#### excludes non-numeric values from sums

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("U2")
sheet.set_value("A1", "east")
sheet.set_value("B1", "abc")
sheet.set_value("A2", "east")
sheet.set_value("B2", "5")

val lines = sheet_subtotals(sheet, "A1:B2", 0, 1)

assert_true(lines.len() == 2)
val l0 = lines[0]
assert_true(l0 == "east: 5")
val l1 = lines[1]
assert_true(l1 == "Grand Total: 5")
```

</details>

#### preserves first-seen group order

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("U3")
sheet.set_value("A1", "gamma")
sheet.set_value("B1", "1")
sheet.set_value("A2", "alpha")
sheet.set_value("B2", "2")
sheet.set_value("A3", "beta")
sheet.set_value("B3", "3")
sheet.set_value("A4", "alpha")
sheet.set_value("B4", "4")

val lines = sheet_subtotals(sheet, "A1:B4", 0, 1)

assert_true(lines.len() == 4)
val l0 = lines[0]
assert_true(l0 == "gamma: 1")
val l1 = lines[1]
assert_true(l1 == "alpha: 6")
val l2 = lines[2]
assert_true(l2 == "beta: 3")
val l3 = lines[3]
assert_true(l3 == "Grand Total: 10")
```

</details>

#### returns [] for invalid column indexes or range

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("U4")
sheet.set_value("A1", "east")
sheet.set_value("B1", "10")

val bad_col = sheet_subtotals(sheet, "A1:B1", 0, 9)
assert_true(bad_col.len() == 0)
val neg_col = sheet_subtotals(sheet, "A1:B1", -1, 1)
assert_true(neg_col.len() == 0)
val bad_range = sheet_subtotals(sheet, "not_a_range", 0, 1)
assert_true(bad_range.len() == 0)
```

</details>

#### does not mutate the sheet

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("U5")
sheet.set_value("A1", "east")
sheet.set_value("B1", "10")

val lines = sheet_subtotals(sheet, "A1:B1", 0, 1)
assert_true(lines.len() == 2)

val a1 = sheet.get_cell("A1")
val a1_text = cell_display_text(a1)
assert_true(a1_text == "east")
val b1 = sheet.get_cell("B1")
match b1.value:
    CellValue.NumberVal(v):
        assert_true(v == 10.0)
    _:
        assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/data_ops2_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sheet_remove_duplicates: basic dedupe, sheet_remove_duplicates: keys and edge cases, sheet_text_to_columns: splitting, sheet_subtotals: grouping and sums.
- sheet_remove_duplicates: basic dedupe
- sheet_remove_duplicates: keys and edge cases
- sheet_text_to_columns: splitting
- sheet_subtotals: grouping and sums

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
