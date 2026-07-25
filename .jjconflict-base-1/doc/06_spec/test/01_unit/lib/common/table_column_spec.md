# Table Column Specification

> <details>

<!-- sdn-diagram:id=table_column_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=table_column_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

table_column_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=table_column_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Table Column Specification

## Scenarios

### column_create

#### creates a column with name and data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("age", [25, 30, 35])
expect(col["name"]).to_equal("age")
expect(col["data"].len()).to_equal(3)
```

</details>

#### creates empty column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("empty", [])
expect(col["name"]).to_equal("empty")
expect(col["data"].len()).to_equal(0)
```

</details>

### column_len

#### returns length of column

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [1, 2, 3, 4, 5])
expect(column_len(col)).to_equal(5)
```

</details>

#### returns 0 for empty column

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [])
expect(column_len(col)).to_equal(0)
```

</details>

### column_get

#### gets value by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [10, 20, 30])
expect(column_get(col, 0)).to_equal(10)
expect(column_get(col, 1)).to_equal(20)
expect(column_get(col, 2)).to_equal(30)
```

</details>

### column_sum

#### sums integer values

- var result = column sum
   - Expected: result equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [1, 2, 3, 4, 5])
var result = column_sum(col)
expect(result).to_equal(15.0)
```

</details>

#### sums to 0 for empty column

- var result = column sum
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [])
var result = column_sum(col)
expect(result).to_equal(0.0)
```

</details>

### column_mean

#### computes mean of values

- var result = column mean
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [2, 4, 6])
var result = column_mean(col)
expect(result).to_equal(4.0)
```

</details>

#### returns 0 for empty column

- var result = column mean
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [])
var result = column_mean(col)
expect(result).to_equal(0.0)
```

</details>

#### computes mean of single value

- var result = column mean
   - Expected: result equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [10])
var result = column_mean(col)
expect(result).to_equal(10.0)
```

</details>

### column_min

#### finds minimum value

- var result = column min
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [5, 3, 8, 1, 4])
var result = column_min(col)
expect(result).to_equal(1)
```

</details>

#### returns nil for empty column

- var result = column min


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [])
var result = column_min(col)
expect(result).to_be_nil()
```

</details>

#### works with single element

- var result = column min
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [42])
var result = column_min(col)
expect(result).to_equal(42)
```

</details>

### column_max

#### finds maximum value

- var result = column max
   - Expected: result equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [5, 3, 8, 1, 4])
var result = column_max(col)
expect(result).to_equal(8)
```

</details>

#### returns nil for empty column

- var result = column max


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [])
var result = column_max(col)
expect(result).to_be_nil()
```

</details>

#### works with single element

- var result = column max
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [42])
var result = column_max(col)
expect(result).to_equal(42)
```

</details>

### column_unique

#### returns unique values

- var result = column unique
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [1, 2, 2, 3, 3, 3])
var result = column_unique(col)
expect(result.len()).to_equal(3)
```

</details>

#### preserves order

- var result = column unique
   - Expected: result[0] equals `3`
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [3, 1, 2, 1, 3])
var result = column_unique(col)
expect(result[0]).to_equal(3)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(2)
```

</details>

#### handles empty column

- var result = column unique
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [])
var result = column_unique(col)
expect(result.len()).to_equal(0)
```

</details>

#### handles all unique values

- var result = column unique
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [10, 20, 30])
var result = column_unique(col)
expect(result.len()).to_equal(3)
```

</details>

### column_value_counts

#### counts value occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", ["a", "b", "a", "c", "b", "a"])
val counts = column_value_counts(col)
expect(counts["a"]).to_equal(3)
expect(counts["b"]).to_equal(2)
expect(counts["c"]).to_equal(1)
```

</details>

#### handles single unique value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [5, 5, 5])
val counts = column_value_counts(col)
expect(counts["5"]).to_equal(3)
```

</details>

#### handles empty column

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [])
val counts = column_value_counts(col)
val count = 0
for (k, v) in counts:
    pass
expect(count).to_equal(0)
```

</details>

### table_empty

#### creates table with no columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = table_empty()
expect(table["column_names"].len()).to_equal(0)
expect(table["num_rows"]).to_equal(0)
```

</details>

### table_from_columns

#### creates table from columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col1 = column_create("name", ["Alice", "Bob", "Charlie"])
val col2 = column_create("age", [25, 30, 35])
val table = table_from_columns([col1, col2])
expect(table["column_names"].len()).to_equal(2)
expect(table["num_rows"]).to_equal(3)
```

</details>

#### creates table from single column

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [1, 2, 3])
val table = table_from_columns([col])
expect(table["column_names"].len()).to_equal(1)
expect(table["num_rows"]).to_equal(3)
```

</details>

#### creates empty table from no columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = table_from_columns([])
expect(table["column_names"].len()).to_equal(0)
expect(table["num_rows"]).to_equal(0)
```

</details>

### table_get

#### gets column by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col1 = column_create("x", [1, 2, 3])
val col2 = column_create("y", [4, 5, 6])
val table = table_from_columns([col1, col2])
val found = table_get(table, "x")
expect(found["name"]).to_equal("x")
expect(found["data"][0]).to_equal(1)
```

</details>

#### returns nil for non-existent column

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("x", [1, 2])
val table = table_from_columns([col])
val found = table_get(table, "z")
expect(found).to_be_nil()
```

</details>

### table_col_index

#### returns index of existing column

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col1 = column_create("a", [1])
val col2 = column_create("b", [2])
val col3 = column_create("c", [3])
val table = table_from_columns([col1, col2, col3])
expect(table_col_index(table, "a")).to_equal(0)
expect(table_col_index(table, "b")).to_equal(1)
expect(table_col_index(table, "c")).to_equal(2)
```

</details>

#### returns -1 for non-existent column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("a", [1])
val table = table_from_columns([col])
expect(table_col_index(table, "z")).to_equal(-1)
```

</details>

### table_select

#### selects specific columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col1 = column_create("a", [1, 2])
val col2 = column_create("b", [3, 4])
val col3 = column_create("c", [5, 6])
val table = table_from_columns([col1, col2, col3])
val selected = table_select(table, ["a", "c"])
expect(selected["column_names"].len()).to_equal(2)
expect(selected["column_names"][0]).to_equal("a")
expect(selected["column_names"][1]).to_equal("c")
```

</details>

#### returns empty table for non-existent columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("a", [1, 2])
val table = table_from_columns([col])
val selected = table_select(table, ["x", "y"])
expect(selected["column_names"].len()).to_equal(0)
```

</details>

### table_drop

#### drops specified columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col1 = column_create("a", [1, 2])
val col2 = column_create("b", [3, 4])
val col3 = column_create("c", [5, 6])
val table = table_from_columns([col1, col2, col3])
val dropped = table_drop(table, ["b"])
expect(dropped["column_names"].len()).to_equal(2)
expect(dropped["column_names"][0]).to_equal("a")
expect(dropped["column_names"][1]).to_equal("c")
```

</details>

#### returns same table when dropping non-existent column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("a", [1, 2])
val table = table_from_columns([col])
val dropped = table_drop(table, ["x"])
expect(dropped["column_names"].len()).to_equal(1)
expect(dropped["column_names"][0]).to_equal("a")
```

</details>

### table_with_column

#### adds a new column

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("a", [1, 2, 3])
val table = table_from_columns([col])
val updated = table_with_column(table, "b", [4, 5, 6])
expect(updated["column_names"].len()).to_equal(2)
val new_col = updated["columns"]["b"]
expect(new_col["data"][0]).to_equal(4)
expect(new_col["data"][2]).to_equal(6)
```

</details>

#### rejects column with wrong length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = column_create("a", [1, 2, 3])
val table = table_from_columns([col])
val updated = table_with_column(table, "b", [4, 5])
# Should return original table unchanged
expect(updated["column_names"].len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/table_column_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- column_create
- column_len
- column_get
- column_sum
- column_mean
- column_min
- column_max
- column_unique
- column_value_counts
- table_empty
- table_from_columns
- table_get
- table_col_index
- table_select
- table_drop
- table_with_column

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
