# Table Column Specification

> Tests covering column_create, column_len, column_get, column_sum, column_mean, column_min, column_max, column_unique, column_value_counts, table_empty, table_from_columns, table_get, table_col_index, table_select, table_drop, table_with_column.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Table Column Specification

## Scenarios

### column_create

#### creates a column with name and data

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a column with name and data
   - Expected: col["name"] equals `age`
   - Expected: col["data"].len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a column with name and data")
val col = column_create("age", [25, 30, 35])
expect(col["name"]).to_equal("age")
expect(col["data"].len()).to_equal(3)
```

</details>

#### creates empty column

- creates empty column
   - Expected: col["name"] equals `empty`
   - Expected: col["data"].len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty column")
val col = column_create("empty", [])
expect(col["name"]).to_equal("empty")
expect(col["data"].len()).to_equal(0)
```

</details>

### column_len

#### returns length of column

- returns length of column
   - Expected: column_len(col) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns length of column")
val col = column_create("x", [1, 2, 3, 4, 5])
expect(column_len(col)).to_equal(5)
```

</details>

#### returns 0 for empty column

- returns 0 for empty column
   - Expected: column_len(col) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for empty column")
val col = column_create("x", [])
expect(column_len(col)).to_equal(0)
```

</details>

### column_get

#### gets value by index

- gets value by index
   - Expected: column_get(col, 0) equals `10`
   - Expected: column_get(col, 1) equals `20`
   - Expected: column_get(col, 2) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets value by index")
val col = column_create("x", [10, 20, 30])
expect(column_get(col, 0)).to_equal(10)
expect(column_get(col, 1)).to_equal(20)
expect(column_get(col, 2)).to_equal(30)
```

</details>

### column_sum

#### sums integer values

- sums integer values
   - Expected: result equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sums integer values")
val col = column_create("x", [1, 2, 3, 4, 5])
var result = column_sum(col)
expect(result).to_equal(15.0)
```

</details>

#### sums to 0 for empty column

- sums to 0 for empty column
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sums to 0 for empty column")
val col = column_create("x", [])
var result = column_sum(col)
expect(result).to_equal(0.0)
```

</details>

### column_mean

#### computes mean of values

- computes mean of values
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes mean of values")
val col = column_create("x", [2, 4, 6])
var result = column_mean(col)
expect(result).to_equal(4.0)
```

</details>

#### returns 0 for empty column

- returns 0 for empty column
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for empty column")
val col = column_create("x", [])
var result = column_mean(col)
expect(result).to_equal(0.0)
```

</details>

#### computes mean of single value

- computes mean of single value
   - Expected: result equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes mean of single value")
val col = column_create("x", [10])
var result = column_mean(col)
expect(result).to_equal(10.0)
```

</details>

### column_min

#### finds minimum value

- finds minimum value
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds minimum value")
val col = column_create("x", [5, 3, 8, 1, 4])
var result = column_min(col)
expect(result).to_equal(1)
```

</details>

#### returns nil for empty column

- returns nil for empty column


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for empty column")
val col = column_create("x", [])
var result = column_min(col)
expect(result).to_be_nil()
```

</details>

#### works with single element

- works with single element
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("works with single element")
val col = column_create("x", [42])
var result = column_min(col)
expect(result).to_equal(42)
```

</details>

### column_max

#### finds maximum value

- finds maximum value
   - Expected: result equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds maximum value")
val col = column_create("x", [5, 3, 8, 1, 4])
var result = column_max(col)
expect(result).to_equal(8)
```

</details>

#### returns nil for empty column

- returns nil for empty column


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for empty column")
val col = column_create("x", [])
var result = column_max(col)
expect(result).to_be_nil()
```

</details>

#### works with single element

- works with single element
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("works with single element")
val col = column_create("x", [42])
var result = column_max(col)
expect(result).to_equal(42)
```

</details>

### column_unique

#### returns unique values

- returns unique values
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns unique values")
val col = column_create("x", [1, 2, 2, 3, 3, 3])
var result = column_unique(col)
expect(result.len()).to_equal(3)
```

</details>

#### preserves order

- preserves order
   - Expected: result[0] equals `3`
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves order")
val col = column_create("x", [3, 1, 2, 1, 3])
var result = column_unique(col)
expect(result[0]).to_equal(3)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(2)
```

</details>

#### handles empty column

- handles empty column
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles empty column")
val col = column_create("x", [])
var result = column_unique(col)
expect(result.len()).to_equal(0)
```

</details>

#### handles all unique values

- handles all unique values
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles all unique values")
val col = column_create("x", [10, 20, 30])
var result = column_unique(col)
expect(result.len()).to_equal(3)
```

</details>

### column_value_counts

#### counts value occurrences

- counts value occurrences
   - Expected: counts["a"] equals `3`
   - Expected: counts["b"] equals `2`
   - Expected: counts["c"] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts value occurrences")
val col = column_create("x", ["a", "b", "a", "c", "b", "a"])
val counts = column_value_counts(col)
expect(counts["a"]).to_equal(3)
expect(counts["b"]).to_equal(2)
expect(counts["c"]).to_equal(1)
```

</details>

#### handles single unique value

- handles single unique value
   - Expected: counts["5"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles single unique value")
val col = column_create("x", [5, 5, 5])
val counts = column_value_counts(col)
expect(counts["5"]).to_equal(3)
```

</details>

#### handles empty column

- handles empty column
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles empty column")
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

- creates table with no columns
   - Expected: table["column_names"].len() equals `0`
   - Expected: table["num_rows"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates table with no columns")
val table = table_empty()
expect(table["column_names"].len()).to_equal(0)
expect(table["num_rows"]).to_equal(0)
```

</details>

### table_from_columns

#### creates table from columns

- creates table from columns
   - Expected: table["column_names"].len() equals `2`
   - Expected: table["num_rows"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates table from columns")
val col1 = column_create("name", ["Alice", "Bob", "Charlie"])
val col2 = column_create("age", [25, 30, 35])
val table = table_from_columns([col1, col2])
expect(table["column_names"].len()).to_equal(2)
expect(table["num_rows"]).to_equal(3)
```

</details>

#### creates table from single column

- creates table from single column
   - Expected: table["column_names"].len() equals `1`
   - Expected: table["num_rows"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates table from single column")
val col = column_create("x", [1, 2, 3])
val table = table_from_columns([col])
expect(table["column_names"].len()).to_equal(1)
expect(table["num_rows"]).to_equal(3)
```

</details>

#### creates empty table from no columns

- creates empty table from no columns
   - Expected: table["column_names"].len() equals `0`
   - Expected: table["num_rows"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty table from no columns")
val table = table_from_columns([])
expect(table["column_names"].len()).to_equal(0)
expect(table["num_rows"]).to_equal(0)
```

</details>

### table_get

#### gets column by name

- gets column by name
   - Expected: found["name"] equals `x`
   - Expected: found["data"][0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets column by name")
val col1 = column_create("x", [1, 2, 3])
val col2 = column_create("y", [4, 5, 6])
val table = table_from_columns([col1, col2])
val found = table_get(table, "x")
expect(found["name"]).to_equal("x")
expect(found["data"][0]).to_equal(1)
```

</details>

#### returns nil for non-existent column

- returns nil for non-existent column


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for non-existent column")
val col = column_create("x", [1, 2])
val table = table_from_columns([col])
val found = table_get(table, "z")
expect(found).to_be_nil()
```

</details>

### table_col_index

#### returns index of existing column

- returns index of existing column
   - Expected: table_col_index(table, "a") equals `0`
   - Expected: table_col_index(table, "b") equals `1`
   - Expected: table_col_index(table, "c") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns index of existing column")
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

- returns -1 for non-existent column
   - Expected: table_col_index(table, "z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns -1 for non-existent column")
val col = column_create("a", [1])
val table = table_from_columns([col])
expect(table_col_index(table, "z")).to_equal(-1)
```

</details>

### table_select

#### selects specific columns

- selects specific columns
   - Expected: selected["column_names"].len() equals `2`
   - Expected: selected["column_names"][0] equals `a`
   - Expected: selected["column_names"][1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selects specific columns")
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

- returns empty table for non-existent columns
   - Expected: selected["column_names"].len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty table for non-existent columns")
val col = column_create("a", [1, 2])
val table = table_from_columns([col])
val selected = table_select(table, ["x", "y"])
expect(selected["column_names"].len()).to_equal(0)
```

</details>

### table_drop

#### drops specified columns

- drops specified columns
   - Expected: dropped["column_names"].len() equals `2`
   - Expected: dropped["column_names"][0] equals `a`
   - Expected: dropped["column_names"][1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops specified columns")
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

- returns same table when dropping non-existent column
   - Expected: dropped["column_names"].len() equals `1`
   - Expected: dropped["column_names"][0] equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns same table when dropping non-existent column")
val col = column_create("a", [1, 2])
val table = table_from_columns([col])
val dropped = table_drop(table, ["x"])
expect(dropped["column_names"].len()).to_equal(1)
expect(dropped["column_names"][0]).to_equal("a")
```

</details>

### table_with_column

#### adds a new column

- adds a new column
   - Expected: updated["column_names"].len() equals `2`
   - Expected: new_col["data"][0] equals `4`
   - Expected: new_col["data"][2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adds a new column")
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

- rejects column with wrong length
   - Expected: updated["column_names"].len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects column with wrong length")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering column_create, column_len, column_get, column_sum, column_mean, column_min, column_max, column_unique, column_value_counts, table_empty, table_from_columns, table_get, table_col_index, table_select, table_drop, table_with_column.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db48413c847965add39bf14d48a0b7baa2c0bf8c7556d48c8f0b647a9688a8a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db48413c847965add39bf14d48a0b7baa2c0bf8c7556d48c8f0b647a9688a8a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db48413c847965add39bf14d48a0b7baa2c0bf8c7556d48c8f0b647a9688a8a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/table_column_spec.spl
mirror: doc/06_spec/01_unit/lib/common/table_column_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/table_column_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/table_column_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/table_column_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 48 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/table_column_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a column with name and data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/table_column_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/table_column_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns length of column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
