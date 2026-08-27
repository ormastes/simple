# Table (DataFrame) Specification

> Table/DataFrame-like data structure for tabular data:

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
| Updated | 2026-08-26 |
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

- creates table from column list
   - Expected: table.num_rows equals `3`
   - Expected: table.column_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates table from column list")
val col1 = Column(name: "x", data: [1, 2, 3])
val col2 = Column(name: "y", data: [4, 5, 6])
val table = table_from_columns([col1, col2])

expect(table.num_rows).to_equal(3)
expect(table.column_names.len()).to_equal(2)
```

</details>

#### from dictionary

#### creates table from dict of arrays

- creates table from dict of arrays
   - Expected: table.num_rows equals `3`
   - Expected: table.column_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates table from dict of arrays")
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

- gets column via get()
   - Expected: col_opt == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets column via get()")
var data = {}
data["x"] = [1, 2, 3]
data["y"] = [4, 5, 6]
val table = table_from_dict(data)

val col_opt = table_get(table, "x")
expect(col_opt == nil).to_equal(false)
```

</details>

#### returns nil for missing column

- returns nil for missing column
   - Expected: col_opt == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for missing column")
val table = table_empty()
val col_opt = table_get(table, "missing")
expect(col_opt == nil).to_equal(true)
```

</details>

### Column Reductions

#### sum

#### sums numeric column

- sums numeric column
   - Expected: total equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sums numeric column")
val col = Column(name: "x", data: [1, 2, 3, 4])
val total = column_sum(col)
expect(total).to_equal(10.0)
```

</details>

#### mean

#### computes mean

- computes mean
   - Expected: avg equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes mean")
val col = Column(name: "x", data: [2, 4, 6, 8])
val avg = column_mean(col)
expect(avg).to_equal(5.0)
```

</details>

#### min/max

#### finds minimum

- finds minimum
   - Expected: minimum equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds minimum")
val col = Column(name: "x", data: [5, 2, 8, 1, 9])
val minimum = column_min(col)
expect(minimum).to_equal(1)
```

</details>

#### finds maximum

- finds maximum
   - Expected: maximum equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds maximum")
val col = Column(name: "x", data: [5, 2, 8, 1, 9])
val maximum = column_max(col)
expect(maximum).to_equal(9)
```

</details>

#### std/var

#### computes standard deviation

- computes standard deviation
   - Expected: std > 2.0 is true
   - Expected: std < 2.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes standard deviation")
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

- filters by predicate
   - Expected: table2.num_rows equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters by predicate")
var data = {}
data["x"] = [1, 2, 3, 4, 5]
data["y"] = [10, 20, 30, 40, 50]
val table1 = table_from_dict(data)

val table2 = table_where(table1, fn(row): row["x"] > 2)
expect(table2.num_rows).to_equal(3)
```

</details>

#### chains multiple filters

- chains multiple filters
   - Expected: table3.num_rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple filters")
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

- selects specific columns
   - Expected: table2.column_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects specific columns")
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

- drops specific columns
   - Expected: table2.column_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("drops specific columns")
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

- sorts ascending by column
   - Expected: x_col == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sorts ascending by column")
var data = {}
data["x"] = [3, 1, 2]
data["y"] = [30, 10, 20]
val table1 = table_from_dict(data)

val table2 = table_sort_by(table1, "x", true)
val x_col = table_get(table2, "x")
# Can't easily check values, just verify it ran
expect(x_col == nil).to_equal(false)
```

</details>

#### sorts descending

- sorts descending
   - Expected: x_col == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sorts descending")
var data = {}
data["x"] = [1, 2, 3]
data["y"] = [10, 20, 30]
val table1 = table_from_dict(data)

val table2 = table_sort_by(table1, "x", false)
val x_col = table_get(table2, "x")
expect(x_col == nil).to_equal(false)
```

</details>

### Grouping and Aggregation

#### group_by

#### groups by single column

- groups by single column
   - Expected: table2.num_rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("groups by single column")
var data = {}
data["category"] = ["A", "B", "A", "B"]
data["value"] = [10, 20, 30, 40]
val table1 = table_from_dict(data)

val table2 = table_group_by(table1, "category", "value", "sum")
expect(table2.num_rows).to_equal(2)
```

</details>

#### computes sum per group

- computes sum per group
   - Expected: table2.num_rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes sum per group")
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

- supports multiple aggregations
   - Expected: sum_table.num_rows equals `1`
   - Expected: mean_table.num_rows equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multiple aggregations")
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

- joins on common column
   - Expected: joined.num_rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("joins on common column")
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

- adds new column
   - Expected: table2.column_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds new column")
var data = {}
data["x"] = [1, 2, 3]
val table1 = table_from_dict(data)

val table2 = table_with_column(table1, "y", [10, 20, 30])
expect(table2.column_names.len()).to_equal(2)
```

</details>

#### with_computed

#### adds column from computation

- adds column from computation
   - Expected: table2.column_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds column from computation")
var data = {}
data["x"] = [1, 2, 3]
val table1 = table_from_dict(data)

val table2 = table_with_computed(table1, "x2", fn(row): row["x"] * 2)
expect(table2.column_names.len()).to_equal(2)
```

</details>

### Chained Operations

#### chains filter, select, and aggregate

- chains filter, select, and aggregate
   - Expected: table3.num_rows equals `3`
   - Expected: table3.column_names.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains filter, select, and aggregate")
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

- computes department statistics
   - Expected: table2.num_rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes department statistics")
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

- gets unique values
   - Expected: uniq.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets unique values")
val col = Column(name: "x", data: [1, 2, 2, 3, 3, 3])
val uniq = column_unique(col)
expect(uniq.len()).to_equal(3)
```

</details>

#### value_counts

#### counts value occurrences

- counts value occurrences
   - Expected: counts.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts value occurrences")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3532a77296a756e4f2fff60b6b899a50295c1d61d3acb76fd1a5b73974e1afd7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3532a77296a756e4f2fff60b6b899a50295c1d61d3acb76fd1a5b73974e1afd7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3532a77296a756e4f2fff60b6b899a50295c1d61d3acb76fd1a5b73974e1afd7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/table_spec.spl
mirror: doc/06_spec/03_system/feature/usage/table_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/table_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/table_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/table_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/table_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates table from column list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/table_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates table from dict of arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/table_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets column via get()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
