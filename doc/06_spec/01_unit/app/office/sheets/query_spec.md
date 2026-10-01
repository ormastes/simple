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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets table-query spec.

Covers sheet_select (project + filter), sheet_sort_by (stable multi-key
sort), sheet_join (nested-loop inner/left), sheet_group_agg (group +
aggregate), and their composability (select -> sort -> group_agg piping
plain Sheets into each other).

## Scenarios

### sheet_select

#### projects columns and filters rows by criteria

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- projects columns and filters rows by criteria
   - Expected: cell_display_text(result.get_cell("A1")) equals `Region`
   - Expected: cell_display_text(result.get_cell("B1")) equals `Qty`
   - Expected: cell_display_text(result.get_cell("A2")) equals `East`
   - Expected: cell_display_text(result.get_cell("B2")) equals `10`
   - Expected: cell_display_text(result.get_cell("A3")) equals `East`
   - Expected: cell_display_text(result.get_cell("B3")) equals `15`
   - Expected: cell_display_text(result.get_cell("A4")) equals `East`
   - Expected: cell_display_text(result.get_cell("B4")) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("projects columns and filters rows by criteria")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region", "Qty"], "Region", "East")
expect(cell_display_text(result.get_cell("A1"))).to_equal("Region")
expect(cell_display_text(result.get_cell("B1"))).to_equal("Qty")
expect(cell_display_text(result.get_cell("A2"))).to_equal("East")
expect(cell_display_text(result.get_cell("B2"))).to_equal("10")
expect(cell_display_text(result.get_cell("A3"))).to_equal("East")
expect(cell_display_text(result.get_cell("B3"))).to_equal("15")
expect(cell_display_text(result.get_cell("A4"))).to_equal("East")
expect(cell_display_text(result.get_cell("B4"))).to_equal("2")
```

</details>

#### selects every row unfiltered when criteria_col is empty

- selects every row unfiltered when criteria_col is empty
   - Expected: cell_display_text(result.get_cell("A1")) equals `Region`
   - Expected: cell_display_text(result.get_cell("A2")) equals `East`
   - Expected: cell_display_text(result.get_cell("A3")) equals `West`
   - Expected: cell_display_text(result.get_cell("A4")) equals `East`
   - Expected: cell_display_text(result.get_cell("A5")) equals `West`
   - Expected: cell_display_text(result.get_cell("A6")) equals `East`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("selects every row unfiltered when criteria_col is empty")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region"], "", "")
expect(cell_display_text(result.get_cell("A1"))).to_equal("Region")
expect(cell_display_text(result.get_cell("A2"))).to_equal("East")
expect(cell_display_text(result.get_cell("A3"))).to_equal("West")
expect(cell_display_text(result.get_cell("A4"))).to_equal("East")
expect(cell_display_text(result.get_cell("A5"))).to_equal("West")
expect(cell_display_text(result.get_cell("A6"))).to_equal("East")
```

</details>

#### silently skips a column name that is not in the header

- silently skips a column name that is not in the header
   - Expected: cell_display_text(result.get_cell("A1")) equals `Region`
   - Expected: cell_display_text(result.get_cell("B1")) equals `Qty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("silently skips a column name that is not in the header")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region", "NoSuchColumn", "Qty"], "", "")
expect(cell_display_text(result.get_cell("A1"))).to_equal("Region")
expect(cell_display_text(result.get_cell("B1"))).to_equal("Qty")
```

</details>

#### returns header-only output when criteria matches nothing

- returns header-only output when criteria matches nothing
   - Expected: cell_display_text(result.get_cell("A1")) equals `Region`
   - Expected: cell_display_text(result.get_cell("A2")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns header-only output when criteria matches nothing")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_select(sheet, 1, ["Region"], "Region", "Nowhere")
expect(cell_display_text(result.get_cell("A1"))).to_equal("Region")
expect(cell_display_text(result.get_cell("A2"))).to_equal("")
```

</details>

### sheet_sort_by

#### sorts by a single key and is stable on ties

- sorts by a single key and is stable on ties
   - Expected: cell_display_text(result.get_cell("A2")) equals `East`
   - Expected: cell_display_text(result.get_cell("C2")) equals `10`
   - Expected: cell_display_text(result.get_cell("A3")) equals `East`
   - Expected: cell_display_text(result.get_cell("C3")) equals `15`
   - Expected: cell_display_text(result.get_cell("A4")) equals `East`
   - Expected: cell_display_text(result.get_cell("C4")) equals `2`
   - Expected: cell_display_text(result.get_cell("A5")) equals `West`
   - Expected: cell_display_text(result.get_cell("C5")) equals `5`
   - Expected: cell_display_text(result.get_cell("A6")) equals `West`
   - Expected: cell_display_text(result.get_cell("C6")) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sorts by a single key and is stable on ties")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Region"], [true])
# East group keeps its original relative order: 10, 15, 2
expect(cell_display_text(result.get_cell("A2"))).to_equal("East")
expect(cell_display_text(result.get_cell("C2"))).to_equal("10")
expect(cell_display_text(result.get_cell("A3"))).to_equal("East")
expect(cell_display_text(result.get_cell("C3"))).to_equal("15")
expect(cell_display_text(result.get_cell("A4"))).to_equal("East")
expect(cell_display_text(result.get_cell("C4"))).to_equal("2")
# West group keeps its original relative order: 5, 8
expect(cell_display_text(result.get_cell("A5"))).to_equal("West")
expect(cell_display_text(result.get_cell("C5"))).to_equal("5")
expect(cell_display_text(result.get_cell("A6"))).to_equal("West")
expect(cell_display_text(result.get_cell("C6"))).to_equal("8")
```

</details>

#### sorts multi-key with a text primary key and numeric secondary key descending

- sorts multi-key with a text primary key and numeric secondary key descending
   - Expected: cell_display_text(result.get_cell("A2")) equals `East`
   - Expected: cell_display_text(result.get_cell("C2")) equals `15`
   - Expected: cell_display_text(result.get_cell("A3")) equals `East`
   - Expected: cell_display_text(result.get_cell("C3")) equals `10`
   - Expected: cell_display_text(result.get_cell("A4")) equals `East`
   - Expected: cell_display_text(result.get_cell("C4")) equals `2`
   - Expected: cell_display_text(result.get_cell("A5")) equals `West`
   - Expected: cell_display_text(result.get_cell("C5")) equals `8`
   - Expected: cell_display_text(result.get_cell("A6")) equals `West`
   - Expected: cell_display_text(result.get_cell("C6")) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sorts multi-key with a text primary key and numeric secondary key descending")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Region", "Qty"], [true, false])
# East (text asc) first, Qty desc within it: 15, 10, 2
expect(cell_display_text(result.get_cell("A2"))).to_equal("East")
expect(cell_display_text(result.get_cell("C2"))).to_equal("15")
expect(cell_display_text(result.get_cell("A3"))).to_equal("East")
expect(cell_display_text(result.get_cell("C3"))).to_equal("10")
expect(cell_display_text(result.get_cell("A4"))).to_equal("East")
expect(cell_display_text(result.get_cell("C4"))).to_equal("2")
# West (text asc) second, Qty desc within it: 8, 5
expect(cell_display_text(result.get_cell("A5"))).to_equal("West")
expect(cell_display_text(result.get_cell("C5"))).to_equal("8")
expect(cell_display_text(result.get_cell("A6"))).to_equal("West")
expect(cell_display_text(result.get_cell("C6"))).to_equal("5")
```

</details>

#### sorts a purely numeric column ascending

- sorts a purely numeric column ascending
   - Expected: cell_display_text(result.get_cell("C2")) equals `2`
   - Expected: cell_display_text(result.get_cell("C3")) equals `5`
   - Expected: cell_display_text(result.get_cell("C4")) equals `8`
   - Expected: cell_display_text(result.get_cell("C5")) equals `10`
   - Expected: cell_display_text(result.get_cell("C6")) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sorts a purely numeric column ascending")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Qty"], [true])
expect(cell_display_text(result.get_cell("C2"))).to_equal("2")
expect(cell_display_text(result.get_cell("C3"))).to_equal("5")
expect(cell_display_text(result.get_cell("C4"))).to_equal("8")
expect(cell_display_text(result.get_cell("C5"))).to_equal("10")
expect(cell_display_text(result.get_cell("C6"))).to_equal("15")
```

</details>

#### returns the sheet unchanged when keys and ascending lengths differ (fail closed)

- returns the sheet unchanged when keys and ascending lengths differ (fail closed)
   - Expected: cell_display_text(result.get_cell("A2")) equals `East`
   - Expected: cell_display_text(result.get_cell("C2")) equals `10`
   - Expected: cell_display_text(result.get_cell("A4")) equals `East`
   - Expected: cell_display_text(result.get_cell("C4")) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns the sheet unchanged when keys and ascending lengths differ (fail closed)")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_sort_by(sheet, 1, ["Region", "Qty"], [true])
# Unchanged means original row order is preserved
expect(cell_display_text(result.get_cell("A2"))).to_equal("East")
expect(cell_display_text(result.get_cell("C2"))).to_equal("10")
expect(cell_display_text(result.get_cell("A4"))).to_equal("East")
expect(cell_display_text(result.get_cell("C4"))).to_equal("15")
```

</details>

### sheet_join

#### inner-joins matched rows only, hand-verified

- inner-joins matched rows only, hand-verified
   - Expected: cell_display_text(result.get_cell("A2")) equals `1`
   - Expected: cell_display_text(result.get_cell("B2")) equals `Widget`
   - Expected: cell_display_text(result.get_cell("C2")) equals `10`
   - Expected: cell_display_text(result.get_cell("D2")) equals `5`
   - Expected: cell_display_text(result.get_cell("A3")) equals `2`
   - Expected: cell_display_text(result.get_cell("B3")) equals `Gadget`
   - Expected: cell_display_text(result.get_cell("C3")) equals `3`
   - Expected: cell_display_text(result.get_cell("D3")) equals `20`
   - Expected: cell_display_text(result.get_cell("A4")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("inner-joins matched rows only, hand-verified")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val result = sheet_join(_orders(), _products(), 1, "Product", "Product", "inner")
expect(cell_display_text(result.get_cell("A2"))).to_equal("1")
expect(cell_display_text(result.get_cell("B2"))).to_equal("Widget")
expect(cell_display_text(result.get_cell("C2"))).to_equal("10")
expect(cell_display_text(result.get_cell("D2"))).to_equal("5")
expect(cell_display_text(result.get_cell("A3"))).to_equal("2")
expect(cell_display_text(result.get_cell("B3"))).to_equal("Gadget")
expect(cell_display_text(result.get_cell("C3"))).to_equal("3")
expect(cell_display_text(result.get_cell("D3"))).to_equal("20")
# Gizmo (no match) is dropped under inner join
expect(cell_display_text(result.get_cell("A4"))).to_equal("")
```

</details>

#### excludes the right join key column from the output header

- excludes the right join key column from the output header
   - Expected: cell_display_text(result.get_cell("A1")) equals `OrderId`
   - Expected: cell_display_text(result.get_cell("B1")) equals `Product`
   - Expected: cell_display_text(result.get_cell("C1")) equals `Qty`
   - Expected: cell_display_text(result.get_cell("D1")) equals `Price`
   - Expected: cell_display_text(result.get_cell("E1")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("excludes the right join key column from the output header")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val result = sheet_join(_orders(), _products(), 1, "Product", "Product", "inner")
expect(cell_display_text(result.get_cell("A1"))).to_equal("OrderId")
expect(cell_display_text(result.get_cell("B1"))).to_equal("Product")
expect(cell_display_text(result.get_cell("C1"))).to_equal("Qty")
expect(cell_display_text(result.get_cell("D1"))).to_equal("Price")
# Only 4 columns total: right's "Product" key column is not repeated
expect(cell_display_text(result.get_cell("E1"))).to_equal("")
```

</details>

#### left-joins and fills unmatched right-side columns with empty

- left-joins and fills unmatched right-side columns with empty
   - Expected: cell_display_text(result.get_cell("A2")) equals `1`
   - Expected: cell_display_text(result.get_cell("D2")) equals `5`
   - Expected: cell_display_text(result.get_cell("A3")) equals `2`
   - Expected: cell_display_text(result.get_cell("D3")) equals `20`
   - Expected: cell_display_text(result.get_cell("A4")) equals `3`
   - Expected: cell_display_text(result.get_cell("B4")) equals `Gizmo`
   - Expected: cell_display_text(result.get_cell("C4")) equals `7`
   - Expected: cell_display_text(result.get_cell("D4")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("left-joins and fills unmatched right-side columns with empty")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val result = sheet_join(_orders(), _products(), 1, "Product", "Product", "left")
expect(cell_display_text(result.get_cell("A2"))).to_equal("1")
expect(cell_display_text(result.get_cell("D2"))).to_equal("5")
expect(cell_display_text(result.get_cell("A3"))).to_equal("2")
expect(cell_display_text(result.get_cell("D3"))).to_equal("20")
# Gizmo row is kept, Price column is empty
expect(cell_display_text(result.get_cell("A4"))).to_equal("3")
expect(cell_display_text(result.get_cell("B4"))).to_equal("Gizmo")
expect(cell_display_text(result.get_cell("C4"))).to_equal("7")
expect(cell_display_text(result.get_cell("D4"))).to_equal("")
```

</details>

#### returns a header-only sheet when the join key name does not exist

- returns a header-only sheet when the join key name does not exist
   - Expected: cell_display_text(result.get_cell("A1")) equals ``
   - Expected: cell_display_text(result.get_cell("A2")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns a header-only sheet when the join key name does not exist")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val result = sheet_join(_orders(), _products(), 1, "NoSuchKey", "Product", "inner")
expect(cell_display_text(result.get_cell("A1"))).to_equal("")
expect(cell_display_text(result.get_cell("A2"))).to_equal("")
```

</details>

### sheet_group_agg

#### sums per group with a Total row (grand total over all values)

- sums per group with a Total row (grand total over all values)
   - Expected: cell_display_text(result.get_cell("A1")) equals `Region`
   - Expected: cell_display_text(result.get_cell("B1")) equals `sum`
   - Expected: cell_display_text(result.get_cell("A2")) equals `East`
   - Expected: cell_display_text(result.get_cell("B2")) equals `27`
   - Expected: cell_display_text(result.get_cell("A3")) equals `West`
   - Expected: cell_display_text(result.get_cell("B3")) equals `13`
   - Expected: cell_display_text(result.get_cell("A4")) equals `Total`
   - Expected: cell_display_text(result.get_cell("B4")) equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sums per group with a Total row (grand total over all values)")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "sum")
expect(cell_display_text(result.get_cell("A1"))).to_equal("Region")
expect(cell_display_text(result.get_cell("B1"))).to_equal("sum")
expect(cell_display_text(result.get_cell("A2"))).to_equal("East")
expect(cell_display_text(result.get_cell("B2"))).to_equal("27")
expect(cell_display_text(result.get_cell("A3"))).to_equal("West")
expect(cell_display_text(result.get_cell("B3"))).to_equal("13")
expect(cell_display_text(result.get_cell("A4"))).to_equal("Total")
expect(cell_display_text(result.get_cell("B4"))).to_equal("40")
```

</details>

#### counts rows per group

- counts rows per group
   - Expected: cell_display_text(result.get_cell("B2")) equals `3`
   - Expected: cell_display_text(result.get_cell("B3")) equals `2`
   - Expected: cell_display_text(result.get_cell("B4")) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts rows per group")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "count")
expect(cell_display_text(result.get_cell("B2"))).to_equal("3")
expect(cell_display_text(result.get_cell("B3"))).to_equal("2")
expect(cell_display_text(result.get_cell("B4"))).to_equal("5")
```

</details>

#### averages per group using the true overall average for Total (not avg-of-avgs)

- averages per group using the true overall average for Total (not avg-of-avgs)
   - Expected: cell_display_text(result.get_cell("B2")) equals `9`
   - Expected: cell_display_text(result.get_cell("B3")) equals `6.5`
   - Expected: cell_display_text(result.get_cell("B4")) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("averages per group using the true overall average for Total (not avg-of-avgs)")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "average")
expect(cell_display_text(result.get_cell("B2"))).to_equal("9")
expect(cell_display_text(result.get_cell("B3"))).to_equal("6.5")
# Overall average = 40/5 = 8, NOT (9+6.5)/2 = 7.75
expect(cell_display_text(result.get_cell("B4"))).to_equal("8")
```

</details>

#### takes the min per group and overall

- takes the min per group and overall
   - Expected: cell_display_text(result.get_cell("B2")) equals `2`
   - Expected: cell_display_text(result.get_cell("B3")) equals `5`
   - Expected: cell_display_text(result.get_cell("B4")) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("takes the min per group and overall")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "min")
expect(cell_display_text(result.get_cell("B2"))).to_equal("2")
expect(cell_display_text(result.get_cell("B3"))).to_equal("5")
expect(cell_display_text(result.get_cell("B4"))).to_equal("2")
```

</details>

#### takes the max per group and overall

- takes the max per group and overall
   - Expected: cell_display_text(result.get_cell("B2")) equals `15`
   - Expected: cell_display_text(result.get_cell("B3")) equals `8`
   - Expected: cell_display_text(result.get_cell("B4")) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("takes the max per group and overall")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "max")
expect(cell_display_text(result.get_cell("B2"))).to_equal("15")
expect(cell_display_text(result.get_cell("B3"))).to_equal("8")
expect(cell_display_text(result.get_cell("B4"))).to_equal("15")
```

</details>

#### returns a header-only sheet for an unsupported aggregate name

- returns a header-only sheet for an unsupported aggregate name
   - Expected: cell_display_text(result.get_cell("A1")) equals `Region`
   - Expected: cell_display_text(result.get_cell("B1")) equals `median`
   - Expected: cell_display_text(result.get_cell("A2")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns a header-only sheet for an unsupported aggregate name")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
val result = sheet_group_agg(sheet, 1, "Region", "Qty", "median")
expect(cell_display_text(result.get_cell("A1"))).to_equal("Region")
expect(cell_display_text(result.get_cell("B1"))).to_equal("median")
expect(cell_display_text(result.get_cell("A2"))).to_equal("")
```

</details>

### composability pipeline

#### chains select -> sort -> group_agg and matches the direct group_agg result

- chains select -> sort -> group_agg and matches the direct group_agg result
   - Expected: cell_display_text(grouped.get_cell("A1")) equals `Region`
   - Expected: cell_display_text(grouped.get_cell("B1")) equals `sum`
   - Expected: cell_display_text(grouped.get_cell("A2")) equals `East`
   - Expected: cell_display_text(grouped.get_cell("B2")) equals `27`
   - Expected: cell_display_text(grouped.get_cell("A3")) equals `West`
   - Expected: cell_display_text(grouped.get_cell("B3")) equals `13`
   - Expected: cell_display_text(grouped.get_cell("A4")) equals `Total`
   - Expected: cell_display_text(grouped.get_cell("B4")) equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("chains select -> sort -> group_agg and matches the direct group_agg result")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sheet = _fixture()
var piped = sheet_select(sheet, 1, ["Region", "Qty"], "", "")
piped = sheet_sort_by(piped, 1, ["Qty"], [true])
val grouped = sheet_group_agg(piped, 1, "Region", "Qty", "sum")
expect(cell_display_text(grouped.get_cell("A1"))).to_equal("Region")
expect(cell_display_text(grouped.get_cell("B1"))).to_equal("sum")
# Same sums as the direct (unchained) computation, regardless of
# first-seen group order shifting after the intermediate sort.
expect(cell_display_text(grouped.get_cell("A2"))).to_equal("East")
expect(cell_display_text(grouped.get_cell("B2"))).to_equal("27")
expect(cell_display_text(grouped.get_cell("A3"))).to_equal("West")
expect(cell_display_text(grouped.get_cell("B3"))).to_equal("13")
expect(cell_display_text(grouped.get_cell("A4"))).to_equal("Total")
expect(cell_display_text(grouped.get_cell("B4"))).to_equal("40")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d0c06aef4b019d4377cc9a239391f0d95923c96b318ff26f18b3f86841d5aae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d0c06aef4b019d4377cc9a239391f0d95923c96b318ff26f18b3f86841d5aae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d0c06aef4b019d4377cc9a239391f0d95923c96b318ff26f18b3f86841d5aae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/app/office/sheets/query_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/query_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
