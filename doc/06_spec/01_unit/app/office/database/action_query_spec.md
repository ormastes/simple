# action_query_spec

> Action-query + macro-runner spec — action_query.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# action_query_spec

Action-query + macro-runner spec — action_query.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/action_query_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Action-query + macro-runner spec — action_query.spl.

Ground truth is hand-computed against one small table:

employees(name, dept, salary):
  Alice, Eng,   90000
  Bob,   Sales, 60000
  Carol, Eng,   95000
  Dave,  Sales, 55000

count_where(dept = Eng): Alice, Carol -> 2

update_where(salary=99999 where dept=Eng):
  Alice: Eng -> matches, salary becomes 99999
  Bob:   Sales -> no match, salary stays 60000
  Carol: Eng -> matches, salary becomes 99999
  Dave:  Sales -> no match, salary stays 55000
  row count unchanged: 4

delete_where(salary < 60000):
  Alice: 90000 < 60000 false -> stays
  Bob:   60000 < 60000 false -> stays
  Carol: 95000 < 60000 false -> stays
  Dave:  55000 < 60000 true  -> removed
  row count: 3

append_row([Eve, Sales, 70000]):
  row count grows by 1, last row name == Eve

macro_run over the base table, in order:
  1. delete salary<60000                (Dave 55000 removed on the ORIGINAL salaries)
  2. update dept=Eng -> salary=1        (Alice, Carol both salary 90000/95000 -> 1)
  3. append Zoe/HR/80000
  Final table (4 rows): Alice/Eng/1, Bob/Sales/60000, Carol/Eng/1, Zoe/HR/80000

  NOTE on ordering: update-before-delete would NOT reach this result — macro_run
  threads the table through each action in real sequence (RETURN-THE-OBJECT), so
  setting Eng salaries to 1 first would make them ALSO match a later
  `salary < 60000`, wiping Alice/Carol out along with Dave. Delete must run on
  the original salaries first for the hand-computed final table below to hold.

## Scenarios

### count_where

#### counts rows matching dept = Eng as 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
expect(count_where(employees, "dept", "=", "Eng")).to_equal(2)
```

</details>

### update_where

#### sets salary=99999 on the two Eng rows and leaves Sales rows + row count untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
val updated = update_where(employees, "salary", "99999", "dept", "=", "Eng")
expect(table_get(updated, 0, "salary")).to_equal("99999")
expect(table_get(updated, 1, "salary")).to_equal("60000")
expect(table_get(updated, 2, "salary")).to_equal("99999")
expect(table_get(updated, 3, "salary")).to_equal("55000")
expect(table_row_count(updated)).to_equal(4)
```

</details>

### delete_where

#### removes Dave (salary 55000 < 60000) and leaves 3 rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
val remaining = delete_where(employees, "salary", "<", "60000")
expect(table_row_count(remaining)).to_equal(3)
expect(table_get(remaining, 0, "name")).to_equal("Alice")
expect(table_get(remaining, 1, "name")).to_equal("Bob")
expect(table_get(remaining, 2, "name")).to_equal("Carol")
```

</details>

### append_row

#### grows the row count by 1 and the last row is Eve

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
val grown = append_row(employees, ["Eve", "Sales", "70000"])
expect(table_row_count(grown)).to_equal(5)
expect(table_get(grown, 4, "name")).to_equal("Eve")
```

</details>

### macro_run

#### applies delete, update, and append in order over the base table

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
var m = macro_new()
m = macro_add(m, action_new("delete", "", "", "salary", "<", "60000", ""))
m = macro_add(m, action_new("update", "salary", "1", "dept", "=", "Eng", ""))
m = macro_add(m, action_new("append", "", "", "", "", "", "Zoe,HR,80000"))
val result = macro_run(m, employees)

expect(table_row_count(result)).to_equal(4)
expect(table_get(result, 0, "name")).to_equal("Alice")
expect(table_get(result, 0, "salary")).to_equal("1")
expect(table_get(result, 1, "name")).to_equal("Bob")
expect(table_get(result, 1, "salary")).to_equal("60000")
expect(table_get(result, 2, "name")).to_equal("Carol")
expect(table_get(result, 2, "salary")).to_equal("1")
expect(table_get(result, 3, "name")).to_equal("Zoe")
expect(table_get(result, 3, "dept")).to_equal("HR")
expect(table_get(result, 3, "salary")).to_equal("80000")
```

</details>

### tail execution probe

#### confirms the final nested describe block actually runs

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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
