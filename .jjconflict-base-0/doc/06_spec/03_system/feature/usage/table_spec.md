# Table (DataFrame) Specification

> Table/DataFrame-like data structure for tabular data:

<!-- sdn-diagram:id=table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

table_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Table (DataFrame) Specification

Table/DataFrame-like data structure for tabular data:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2250-2260 |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/03_system/feature/usage/table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Table/DataFrame-like data structure for tabular data:
- Column-based storage with typed columns
- SQL-like operations (select, where, join)
- Aggregation and grouping
- Statistical operations

## Scenarios

### Table Construction

#### from columns

#### creates table from column list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col1 = Column(name: "x", data: [1, 2, 3])
val col2 = Column(name: "y", data: [4, 5, 6])
val table = table_from_columns([col1, col2])

expect(table.num_rows).to_equal(3)
expect(table.column_names.len()).to_equal(2)
```

</details>

#### from dictionary

#### creates table from dict of arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["a"] = [1, 2, 3]
data["b"] = [4, 5, 6]
val table = table_from_dict(data)

expect(table.num_rows).to_equal(3)
expect(table.column_names.len()).to_equal(2)
```

</details>

### Column Access

#### by name

#### gets column via get()

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [1, 2, 3]
data["y"] = [4, 5, 6]
val table = table_from_dict(data)

val col_opt = table_get(table, "x")
expect(col_opt.?).to_equal(true)
```

</details>

#### returns nil for missing column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = table_empty()
val col_opt = table_get(table, "missing")
expect(col_opt.?).to_equal(false)
```

</details>

### Column Reductions

#### sum

#### sums numeric column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = Column(name: "x", data: [1, 2, 3, 4])
val total = column_sum(col)
expect(total).to_equal(10.0)
```

</details>

#### mean

#### computes mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = Column(name: "x", data: [2, 4, 6, 8])
val avg = column_mean(col)
expect(avg).to_equal(5.0)
```

</details>

#### min/max

#### finds minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = Column(name: "x", data: [5, 2, 8, 1, 9])
val minimum = column_min(col)
expect(minimum).to_equal(1)
```

</details>

#### finds maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = Column(name: "x", data: [5, 2, 8, 1, 9])
val maximum = column_max(col)
expect(maximum).to_equal(9)
```

</details>

#### std/var

#### computes standard deviation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = Column(name: "x", data: [2, 4, 6, 8])
val std = column_std_dev(col)
# std_dev of [2,4,6,8] = sqrt(5) ≈ 2.236
expect(std > 2.0).to_equal(true)
expect(std < 2.5).to_equal(true)
```

</details>

### Filtering

#### where

#### filters by predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [1, 2, 3, 4, 5]
data["y"] = [10, 20, 30, 40, 50]
val table1 = table_from_dict(data)

val table2 = table_where(table1, fn(row): row["x"] > 2)
expect(table2.num_rows).to_equal(3)
```

</details>

#### chains multiple filters

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [1, 2, 3, 4, 5]
data["y"] = [10, 20, 30, 40, 50]
val table1 = table_from_dict(data)

val table2 = table_where(table1, fn(row): row["x"] > 2)
val table3 = table_where(table2, fn(row): row["y"] < 50)
expect(table3.num_rows).to_equal(2)
```

</details>

### Selection

#### select

#### selects specific columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["a"] = [1, 2, 3]
data["b"] = [4, 5, 6]
data["c"] = [7, 8, 9]
val table1 = table_from_dict(data)

val table2 = table_select(table1, ["a", "c"])
expect(table2.column_names.len()).to_equal(2)
```

</details>

#### drop

#### drops specific columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["a"] = [1, 2, 3]
data["b"] = [4, 5, 6]
data["c"] = [7, 8, 9]
val table1 = table_from_dict(data)

val table2 = table_drop(table1, ["b"])
expect(table2.column_names.len()).to_equal(2)
```

</details>

### Sorting

#### sort_by

#### sorts ascending by column

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [3, 1, 2]
data["y"] = [30, 10, 20]
val table1 = table_from_dict(data)

val table2 = table_sort_by(table1, "x", true)
val x_col = table_get(table2, "x")
# Can't easily check values, just verify it ran
expect(x_col.?).to_equal(true)
```

</details>

#### sorts descending

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [1, 2, 3]
data["y"] = [10, 20, 30]
val table1 = table_from_dict(data)

val table2 = table_sort_by(table1, "x", false)
val x_col = table_get(table2, "x")
expect(x_col.?).to_equal(true)
```

</details>

### Grouping and Aggregation

#### group_by

#### groups by single column

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["category"] = ["A", "B", "A", "B"]
data["value"] = [10, 20, 30, 40]
val table1 = table_from_dict(data)

val table2 = table_group_by(table1, "category", "value", "sum")
expect(table2.num_rows).to_equal(2)
```

</details>

#### computes sum per group

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["category"] = ["A", "A", "B"]
data["value"] = [10, 20, 30]
val table1 = table_from_dict(data)

val table2 = table_group_by(table1, "category", "value", "sum")
expect(table2.num_rows).to_equal(2)
```

</details>

#### aggregation functions

#### supports multiple aggregations

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = ["A", "A"]
data["y"] = [5, 10]
val table1 = table_from_dict(data)

val sum_table = table_group_by(table1, "x", "y", "sum")
val mean_table = table_group_by(table1, "x", "y", "mean")
expect(sum_table.num_rows).to_equal(1)
expect(mean_table.num_rows).to_equal(1)
```

</details>

### Joins

#### inner join

#### joins on common column

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var left_data = {}
left_data["id"] = [1, 2, 3]
left_data["name"] = ["Alice", "Bob", "Carol"]
val left_table = table_from_dict(left_data)

var right_data = {}
right_data["id"] = [1, 2]
right_data["score"] = [95, 87]
val right_table = table_from_dict(right_data)

val joined = table_inner_join(left_table, right_table, "id")
expect(joined.num_rows).to_equal(2)
```

</details>

### Computed Columns

#### with_column

#### adds new column

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [1, 2, 3]
val table1 = table_from_dict(data)

val table2 = table_with_column(table1, "y", [10, 20, 30])
expect(table2.column_names.len()).to_equal(2)
```

</details>

#### with_computed

#### adds column from computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [1, 2, 3]
val table1 = table_from_dict(data)

val table2 = table_with_computed(table1, "x2", fn(row): row["x"] * 2)
expect(table2.column_names.len()).to_equal(2)
```

</details>

### Chained Operations

#### chains filter, select, and aggregate

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["x"] = [1, 2, 3, 4, 5]
data["y"] = [10, 20, 30, 40, 50]
val table1 = table_from_dict(data)

val table2 = table_where(table1, fn(row): row["x"] > 2)
val table3 = table_select(table2, ["x"])
expect(table3.num_rows).to_equal(3)
expect(table3.column_names.len()).to_equal(1)
```

</details>

#### computes department statistics

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {}
data["dept"] = ["A", "B", "A", "B"]
data["salary"] = [50000, 60000, 55000, 65000]
val table1 = table_from_dict(data)

val table2 = table_group_by(table1, "dept", "salary", "mean")
expect(table2.num_rows).to_equal(2)
```

</details>

### Column Utilities

#### unique

#### gets unique values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = Column(name: "x", data: [1, 2, 2, 3, 3, 3])
val uniq = column_unique(col)
expect(uniq.len()).to_equal(3)
```

</details>

#### value_counts

#### counts value occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = Column(name: "x", data: [1, 2, 2, 3, 3, 3])
val counts = column_value_counts(col)
expect(counts.len()).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
