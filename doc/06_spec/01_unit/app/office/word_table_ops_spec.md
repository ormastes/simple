# Word Table Ops Specification

> Tests covering table_dims: get table dimensions, table_insert_row: insert a row at given index, table_delete_row: delete a row at given index, table_insert_col: insert a column at given index, table_delete_col: delete a column at given index, table_set_cell: set a cell value, combined operations: insert row, dims, delete row.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Word Table Ops Specification

## Scenarios

### table_dims: get table dimensions
_Returns [rows, cols] for body rows and columns._

#### returns [2, 2] for a 2x2 table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val dims = table_dims(doc, 0)
expect(dims.len()).to_equal(2)
expect(dims.get(0)).to_equal(2)  # 2 body rows
expect(dims.get(1)).to_equal(2)  # 2 cols
```

</details>

#### returns [0, 0] for out-of-range block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |"
val doc = _table_doc(table_md, "test")
val dims = table_dims(doc, 5)
expect(dims.get(0)).to_equal(0)
expect(dims.get(1)).to_equal(0)
```

</details>

#### returns [0, 0] for empty block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = RichDocument.new("test")
val dims = table_dims(doc, 0)
expect(dims.get(0)).to_equal(0)
expect(dims.get(1)).to_equal(0)
```

</details>

### table_insert_row: insert a row at given index
_Insert row in table body (after separator). Row index is 0-based._

#### inserts a row and dims increase to [3, 2]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_row(doc, 0, 0, ["C1", "C2"])
val dims = table_dims(new_doc, 0)
expect(dims.get(0)).to_equal(3)
expect(dims.get(1)).to_equal(2)
```

</details>

#### inserts new row with correct content

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_row(doc, 0, 0, ["X", "Y"])
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| X | Y |")
# Verify order: header, separator, X Y, A1 A2, B1 B2
val lines = text.split("\n")
expect(lines.len()).to_equal(5)
expect(lines.get(2)).to_contain("X")
```

</details>

#### inserts at end of table (row_index=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_row(doc, 0, 2, ["Z1", "Z2"])
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| Z1 | Z2 |")
val lines = text.split("\n")
expect(lines.get(4)).to_contain("Z1")
```

</details>

#### returns unchanged doc for out-of-range block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_row(doc, 99, 0, ["X", "Y"])
val dims = table_dims(new_doc, 0)
expect(dims.get(0)).to_equal(1)  # Unchanged
```

</details>

### table_delete_row: delete a row at given index
_Delete row from table body (after separator)._

#### deletes a row and dims decrease to [1, 2]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_row(doc, 0, 0)
val dims = table_dims(new_doc, 0)
expect(dims.get(0)).to_equal(1)
expect(dims.get(1)).to_equal(2)
```

</details>

#### deletes correct row (first row A1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_row(doc, 0, 0)
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| B1 | B2 |")
expect(text.contains("A1")).to_be(false)
```

</details>

#### deletes last row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_row(doc, 0, 1)
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| A1 | A2 |")
expect(text.contains("B1")).to_be(false)
```

</details>

#### returns unchanged doc for out-of-range row

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_row(doc, 0, 99)
val dims = table_dims(new_doc, 0)
expect(dims.get(0)).to_equal(1)  # Unchanged
```

</details>

### table_insert_col: insert a column at given index
_Insert column with header and cells at col_index._

#### inserts a column and dims increase to [2, 3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_col(doc, 0, 1, "H_NEW", ["X", "Y"])
val dims = table_dims(new_doc, 0)
expect(dims.get(0)).to_equal(2)
expect(dims.get(1)).to_equal(3)
```

</details>

#### inserts column with correct header

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_col(doc, 0, 0, "NEW", ["V1", "V2"])
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| NEW | H1 |")
```

</details>

#### inserts column with correct cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_col(doc, 0, 1, "MID", ["X", "Y"])
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| H1 | MID | H2 |")
expect(text).to_contain("| A1 | X | A2 |")
expect(text).to_contain("| B1 | Y | B2 |")
```

</details>

#### inserts at end of row (col_index=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_col(doc, 0, 2, "H3", ["A3", "B3"])
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| H1 | H2 | H3 |")
expect(text).to_contain("| A1 | A2 | A3 |")
```

</details>

#### returns unchanged doc for out-of-range col_index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_insert_col(doc, 0, 99, "X", ["Y"])
val dims = table_dims(new_doc, 0)
expect(dims.get(1)).to_equal(2)  # Unchanged
```

</details>

### table_delete_col: delete a column at given index
_Delete column from table._

#### deletes a column and dims decrease to [2, 1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_col(doc, 0, 1)
val dims = table_dims(new_doc, 0)
expect(dims.get(0)).to_equal(2)
expect(dims.get(1)).to_equal(1)
```

</details>

#### deletes correct column (first column)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_col(doc, 0, 0)
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| H2 |")
expect(text.contains("H1")).to_be(false)
expect(text).to_contain("| A2 |")
```

</details>

#### deletes last column

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 | H3 |\n|---|---|---|\n| A1 | A2 | A3 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_col(doc, 0, 2)
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| H1 | H2 |")
expect(text.contains("H3")).to_be(false)
val dims = table_dims(new_doc, 0)
expect(dims.get(1)).to_equal(2)
```

</details>

#### returns unchanged doc for out-of-range col_index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_delete_col(doc, 0, 99)
val dims = table_dims(new_doc, 0)
expect(dims.get(1)).to_equal(2)  # Unchanged
```

</details>

### table_set_cell: set a cell value
_Set cell at (row_index, col_index) to a new value._

#### sets a cell to new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_set_cell(doc, 0, 0, 0, "CHANGED")
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| CHANGED | A2 |")
```

</details>

#### sets different cell in same row

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_set_cell(doc, 0, 0, 1, "NEW_A2")
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| A1 | NEW_A2 |")
```

</details>

#### sets cell in second row

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_set_cell(doc, 0, 1, 0, "B1_EDIT")
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| B1_EDIT | B2 |")
# Verify first row unchanged
expect(text).to_contain("| A1 | A2 |")
```

</details>

#### returns unchanged doc for out-of-range cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |"
val doc = _table_doc(table_md, "test")
val new_doc = table_set_cell(doc, 0, 0, 99, "X")
val text = _get_table_text(new_doc, 0)
expect(text).to_contain("| A1 | A2 |")  # Unchanged
```

</details>

### combined operations: insert row, dims, delete row
_Test sequences of operations preserve document integrity._

#### insert row and verify dims, then delete returns to original dims

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_md = "| H1 | H2 |\n|---|---|\n| A1 | A2 |\n| B1 | B2 |"
val doc = _table_doc(table_md, "test")
val original_dims = table_dims(doc, 0)
expect(original_dims.get(0)).to_equal(2)

val after_insert = table_insert_row(doc, 0, 1, ["X", "Y"])
val insert_dims = table_dims(after_insert, 0)
expect(insert_dims.get(0)).to_equal(3)

val after_delete = table_delete_row(after_insert, 0, 1)
val final_dims = table_dims(after_delete, 0)
expect(final_dims.get(0)).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_table_ops_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering table_dims: get table dimensions, table_insert_row: insert a row at given index, table_delete_row: delete a row at given index, table_insert_col: insert a column at given index, table_delete_col: delete a column at given index, table_set_cell: set a cell value, combined operations: insert row, dims, delete row.
- table_dims: get table dimensions
- table_insert_row: insert a row at given index
- table_delete_row: delete a row at given index
- table_insert_col: insert a column at given index
- table_delete_col: delete a column at given index
- table_set_cell: set a cell value
- combined operations: insert row, dims, delete row

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
