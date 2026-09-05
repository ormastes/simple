# db_io_spec

> Database <-> Spreadsheet/CSV bridge spec — database/io.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# db_io_spec

Database <-> Spreadsheet/CSV bridge spec — database/io.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/db_io_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Database <-> Spreadsheet/CSV bridge spec — database/io.spl.

Ground truth is hand-computed against one small table:

employees_note(id, name, note):
  1, Alice, Eng
  2, Bob,   Sales, East      <- note deliberately contains a comma

Table -> Sheet -> Table and Table -> CSV text -> Table are both round-tripped
and checked cell-by-cell / string-for-string against hand-written values.

## Scenarios

### table_to_sheet

#### writes headers in row 1 and data rows below, cell-addressable A1-style

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees_note()
val sheet = table_to_sheet(t)
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("id")
expect(cell_display_text(sheet.get_cell("B1"))).to_equal("name")
expect(cell_display_text(sheet.get_cell("C1"))).to_equal("note")
expect(cell_display_text(sheet.get_cell("A2"))).to_equal("1")
expect(cell_display_text(sheet.get_cell("B2"))).to_equal("Alice")
expect(cell_display_text(sheet.get_cell("C3"))).to_equal("Sales, East")
```

</details>

### table_from_sheet

#### round-trips Table -> Sheet -> Table preserving dims and a specific cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees_note()
val sheet = table_to_sheet(t)
val back = table_from_sheet(sheet, "employees_note_rt", 3, 2)
expect(table_row_count(back)).to_equal(2)
expect(table_col_index(back, "note")).to_equal(2)
expect(table_get(back, 0, "name")).to_equal("Alice")
expect(table_get(back, 1, "note")).to_equal("Sales, East")
expect(table_get(back, 1, "id")).to_equal("2")
```

</details>

### table_to_csv_text

#### produces the exact hand-written CSV string, quoting the comma-bearing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees_note()
val csv_text = table_to_csv_text(t)
val expected = "id,name,note\n1,Alice,Eng\n2,Bob,\"Sales, East\""
expect(csv_text).to_equal(expected)
```

</details>

### table_from_csv_text

#### parses the CSV text back into a Table with the comma-bearing field intact

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees_note()
val csv_text = table_to_csv_text(t)
val back = table_from_csv_text(csv_text, "employees_note_csv")
expect(table_row_count(back)).to_equal(2)
expect(table_col_index(back, "note")).to_equal(2)
expect(table_get(back, 0, "id")).to_equal("1")
expect(table_get(back, 1, "name")).to_equal("Bob")
expect(table_get(back, 1, "note")).to_equal("Sales, East")
```

</details>

### tail execution probe

#### confirms the final describe block actually runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
