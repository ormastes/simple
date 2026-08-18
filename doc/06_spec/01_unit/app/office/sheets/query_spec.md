# query_spec

> Office sheets table-query spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# query_spec

Office sheets table-query spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/query_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets table-query spec.

Covers sheet_select (project + filter), sheet_sort_by (stable multi-key
sort), sheet_join (nested-loop inner/left), sheet_group_agg (group +
aggregate), and their composability (select -> sort -> group_agg piping
plain Sheets into each other).

## Scenarios

### sheet_select

#### projects columns and filters rows by criteria

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region", "Qty"], "Region", "East")
assert_eq(cell_display_text(result.get_cell("A1")), "Region")
assert_eq(cell_display_text(result.get_cell("B1")), "Qty")
assert_eq(cell_display_text(result.get_cell("A2")), "East")
assert_eq(cell_display_text(result.get_cell("B2")), "10")
assert_eq(cell_display_text(result.get_cell("A3")), "East")
assert_eq(cell_display_text(result.get_cell("B3")), "15")
assert_eq(cell_display_text(result.get_cell("A4")), "East")
assert_eq(cell_display_text(result.get_cell("B4")), "2")
```

</details>

#### selects every row unfiltered when criteria_col is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region"], "", "")
assert_eq(cell_display_text(result.get_cell("A1")), "Region")
assert_eq(cell_display_text(result.get_cell("A2")), "East")
assert_eq(cell_display_text(result.get_cell("A3")), "West")
assert_eq(cell_display_text(result.get_cell("A4")), "East")
assert_eq(cell_display_text(result.get_cell("A5")), "West")
assert_eq(cell_display_text(result.get_cell("A6")), "East")
```

</details>

#### silently skips a column name that is not in the header

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region", "NoSuchColumn", "Qty"], "", "")
assert_eq(cell_display_text(result.get_cell("A1")), "Region")
assert_eq(cell_display_text(result.get_cell("B1")), "Qty")
```

</details>

#### returns header-only output when criteria matches nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region"], "Region", "Nowhere")
assert_eq(cell_display_text(result.get_cell("A1")), "Region")
assert_eq(cell_display_text(result.get_cell("A2")), "")
```

</details>

### sheet_sort_by

#### sorts by a single key and is stable on ties

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Region"], [true])
# East group keeps its original relative order: 10, 15, 2
assert_eq(cell_display_text(result.get_cell("A2")), "East")
assert_eq(cell_display_text(result.get_cell("C2")), "10")
assert_eq(cell_display_text(result.get_cell("A3")), "East")
assert_eq(cell_display_text(result.get_cell("C3")), "15")
assert_eq(cell_display_text(result.get_cell("A4")), "East")
assert_eq(cell_display_text(result.get_cell("C4")), "2")
# West group keeps its original relative order: 5, 8
assert_eq(cell_display_text(result.get_cell("A5")), "West")
assert_eq(cell_display_text(result.get_cell("C5")), "5")
assert_eq(cell_display_text(result.get_cell("A6")), "West")
assert_eq(cell_display_text(result.get_cell("C6")), "8")
```

</details>

#### sorts multi-key with a text primary key and numeric secondary key descending

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Region", "Qty"], [true, false])
# East (text asc) first, Qty desc within it: 15, 10, 2
assert_eq(cell_display_text(result.get_cell("A2")), "East")
assert_eq(cell_display_text(result.get_cell("C2")), "15")
assert_eq(cell_display_text(result.get_cell("A3")), "East")
assert_eq(cell_display_text(result.get_cell("C3")), "10")
assert_eq(cell_display_text(result.get_cell("A4")), "East")
assert_eq(cell_display_text(result.get_cell("C4")), "2")
# West (text asc) second, Qty desc within it: 8, 5
assert_eq(cell_display_text(result.get_cell("A5")), "West")
assert_eq(cell_display_text(result.get_cell("C5")), "8")
assert_eq(cell_display_text(result.get_cell("A6")), "West")
assert_eq(cell_display_text(result.get_cell("C6")), "5")
```

</details>

#### sorts a purely numeric column ascending

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Qty"], [true])
assert_eq(cell_display_text(result.get_cell("C2")), "2")
assert_eq(cell_display_text(result.get_cell("C3")), "5")
assert_eq(cell_display_text(result.get_cell("C4")), "8")
assert_eq(cell_display_text(result.get_cell("C5")), "10")
assert_eq(cell_display_text(result.get_cell("C6")), "15")
```

</details>

#### returns the sheet unchanged when keys and ascending lengths differ (fail closed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Region", "Qty"], [true])
# Unchanged means original row order is preserved
assert_eq(cell_display_text(result.get_cell("A2")), "East")
assert_eq(cell_display_text(result.get_cell("C2")), "10")
assert_eq(cell_display_text(result.get_cell("A4")), "East")
assert_eq(cell_display_text(result.get_cell("C4")), "15")
```

</details>

### sheet_join

#### inner-joins matched rows only, hand-verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sheet_join(_orders(), _products(), 1, "Product", "Product", "inner")
assert_eq(cell_display_text(result.get_cell("A2")), "1")
assert_eq(cell_display_text(result.get_cell("B2")), "Widget")
assert_eq(cell_display_text(result.get_cell("C2")), "10")
assert_eq(cell_display_text(result.get_cell("D2")), "5")
assert_eq(cell_display_text(result.get_cell("A3")), "2")
assert_eq(cell_display_text(result.get_cell("B3")), "Gadget")
assert_eq(cell_display_text(result.get_cell("C3")), "3")
assert_eq(cell_display_text(result.get_cell("D3")), "20")
# Gizmo (no match) is dropped under inner join
assert_eq(cell_display_text(result.get_cell("A4")), "")
```

</details>

#### excludes the right join key column from the output header

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sheet_join(_orders(), _products(), 1, "Product", "Product", "inner")
assert_eq(cell_display_text(result.get_cell("A1")), "OrderId")
assert_eq(cell_display_text(result.get_cell("B1")), "Product")
assert_eq(cell_display_text(result.get_cell("C1")), "Qty")
assert_eq(cell_display_text(result.get_cell("D1")), "Price")
# Only 4 columns total: right's "Product" key column is not repeated
assert_eq(cell_display_text(result.get_cell("E1")), "")
```

</details>

#### left-joins and fills unmatched right-side columns with empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sheet_join(_orders(), _products(), 1, "Product", "Product", "left")
assert_eq(cell_display_text(result.get_cell("A2")), "1")
assert_eq(cell_display_text(result.get_cell("D2")), "5")
assert_eq(cell_display_text(result.get_cell("A3")), "2")
assert_eq(cell_display_text(result.get_cell("D3")), "20")
# Gizmo row is kept, Price column is empty
assert_eq(cell_display_text(result.get_cell("A4")), "3")
assert_eq(cell_display_text(result.get_cell("B4")), "Gizmo")
assert_eq(cell_display_text(result.get_cell("C4")), "7")
assert_eq(cell_display_text(result.get_cell("D4")), "")
```

</details>

#### returns a header-only sheet when the join key name does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sheet_join(_orders(), _products(), 1, "NoSuchKey", "Product", "inner")
assert_eq(cell_display_text(result.get_cell("A1")), "")
assert_eq(cell_display_text(result.get_cell("A2")), "")
```

</details>

### sheet_group_agg

#### sums per group with a Total row (grand total over all values)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "sum")
assert_eq(cell_display_text(result.get_cell("A1")), "Region")
assert_eq(cell_display_text(result.get_cell("B1")), "sum")
assert_eq(cell_display_text(result.get_cell("A2")), "East")
assert_eq(cell_display_text(result.get_cell("B2")), "27")
assert_eq(cell_display_text(result.get_cell("A3")), "West")
assert_eq(cell_display_text(result.get_cell("B3")), "13")
assert_eq(cell_display_text(result.get_cell("A4")), "Total")
assert_eq(cell_display_text(result.get_cell("B4")), "40")
```

</details>

#### counts rows per group

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "count")
assert_eq(cell_display_text(result.get_cell("B2")), "3")
assert_eq(cell_display_text(result.get_cell("B3")), "2")
assert_eq(cell_display_text(result.get_cell("B4")), "5")
```

</details>

#### averages per group using the true overall average for Total (not avg-of-avgs)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "average")
assert_eq(cell_display_text(result.get_cell("B2")), "9")
assert_eq(cell_display_text(result.get_cell("B3")), "6.5")
# Overall average = 40/5 = 8, NOT (9+6.5)/2 = 7.75
assert_eq(cell_display_text(result.get_cell("B4")), "8")
```

</details>

#### takes the min per group and overall

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "min")
assert_eq(cell_display_text(result.get_cell("B2")), "2")
assert_eq(cell_display_text(result.get_cell("B3")), "5")
assert_eq(cell_display_text(result.get_cell("B4")), "2")
```

</details>

#### takes the max per group and overall

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "max")
assert_eq(cell_display_text(result.get_cell("B2")), "15")
assert_eq(cell_display_text(result.get_cell("B3")), "8")
assert_eq(cell_display_text(result.get_cell("B4")), "15")
```

</details>

#### returns a header-only sheet for an unsupported aggregate name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "median")
assert_eq(cell_display_text(result.get_cell("A1")), "Region")
assert_eq(cell_display_text(result.get_cell("B1")), "median")
assert_eq(cell_display_text(result.get_cell("A2")), "")
```

</details>

### composability pipeline

#### chains select -> sort -> group_agg and matches the direct group_agg result

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _fixture()
var piped = sheet_select(sheet, 1, ["Region", "Qty"], "", "")
piped = sheet_sort_by(piped, 1, ["Qty"], [true])
val grouped = sheet_group_agg(piped, 1, "Region", "Qty", "sum")
assert_eq(cell_display_text(grouped.get_cell("A1")), "Region")
assert_eq(cell_display_text(grouped.get_cell("B1")), "sum")
# Same sums as the direct (unchained) computation, regardless of
# first-seen group order shifting after the intermediate sort.
assert_eq(cell_display_text(grouped.get_cell("A2")), "East")
assert_eq(cell_display_text(grouped.get_cell("B2")), "27")
assert_eq(cell_display_text(grouped.get_cell("A3")), "West")
assert_eq(cell_display_text(grouped.get_cell("B3")), "13")
assert_eq(cell_display_text(grouped.get_cell("A4")), "Total")
assert_eq(cell_display_text(grouped.get_cell("B4")), "40")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
