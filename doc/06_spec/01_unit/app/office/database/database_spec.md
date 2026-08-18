# database_spec

> Minimal Access-like database spec — table.spl + query.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# database_spec

Minimal Access-like database spec — table.spl + query.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/database_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Minimal Access-like database spec — table.spl + query.spl.

Ground truth is hand-computed against two small tables:

employees(id, name, dept, salary):
  1, Alice, Eng,   90000
  2, bob,   Sales, 60000
  3, Carol, Eng,   95000
  4, Dave,  Sales, 55000

departments(dept, manager):
  Eng,   Erin
  Sales, Sam

## Scenarios

### table_new / table_insert / table_row_count / table_get

#### builds a table and reports the correct row count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees()
expect(table_row_count(t)).to_equal(4)
```

</details>

#### gets cells by row index and column name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees()
expect(table_get(t, 0, "name")).to_equal("Alice")
expect(table_get(t, 2, "salary")).to_equal("95000")
```

</details>

### query_select_where

#### numeric compare selects rows with salary > 60000

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees()
val r = query_select_where(t, "salary", ">", "60000")
expect(table_row_count(r)).to_equal(2)
expect(table_get(r, 0, "name")).to_equal("Alice")
expect(table_get(r, 1, "name")).to_equal("Carol")
```

</details>

#### case-insensitive text compare selects rows with dept = eng

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees()
val r = query_select_where(t, "dept", "=", "eng")
expect(table_row_count(r)).to_equal(2)
expect(table_get(r, 0, "name")).to_equal("Alice")
expect(table_get(r, 1, "name")).to_equal("Carol")
```

</details>

### query_order_by

#### sorts ascending by salary

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees()
val r = query_order_by(t, "salary", false)
expect(table_get(r, 0, "name")).to_equal("Dave")
expect(table_get(r, 1, "name")).to_equal("bob")
expect(table_get(r, 2, "name")).to_equal("Alice")
expect(table_get(r, 3, "name")).to_equal("Carol")
```

</details>

#### sorts descending by salary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees()
val r = query_order_by(t, "salary", true)
expect(table_get(r, 0, "name")).to_equal("Carol")
expect(table_get(r, 3, "name")).to_equal("Dave")
```

</details>

### query_inner_join

#### joins employees to departments on dept

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = _employees()
val d = _departments()
val j = query_inner_join(e, d, "dept", "dept")
expect(table_row_count(j)).to_equal(4)
expect(table_get(j, 0, "manager")).to_equal("Erin")
expect(table_get(j, 0, "name")).to_equal("Alice")
```

</details>

### query_group_count

#### groups employees by dept in first-seen order with counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _employees()
val g = query_group_count(t, "dept")
expect(table_row_count(g)).to_equal(2)
expect(table_get(g, 0, "dept")).to_equal("Eng")
expect(table_get(g, 0, "count")).to_equal("2")
expect(table_get(g, 1, "dept")).to_equal("Sales")
expect(table_get(g, 1, "count")).to_equal("2")
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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
