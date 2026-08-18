# qbe_spec

> Query-By-Example (QBE) design-grid spec — qbe.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# qbe_spec

Query-By-Example (QBE) design-grid spec — qbe.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/qbe_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Query-By-Example (QBE) design-grid spec — qbe.spl.

Ground truth is hand-computed against one small table:

employees(name, dept, salary):
  Alice, Eng,   90000
  Bob,   Sales, 60000
  Carol, Eng,   95000
  Dave,  Sales, 55000

Grid 1 — filter + project (name shown/sort asc no criteria, dept
criteria "=Eng" shown, salary criteria ">90000" NOT shown):
  Alice: dept Eng==Eng true, salary 90000>90000 false -> no
  Bob:   dept Sales!=Eng -> no
  Carol: dept Eng==Eng true, salary 95000>90000 true -> match
  Dave:  dept Sales!=Eng -> no
  => just Carol; salary hidden -> result cols = [name, dept], 1 row
     (name=Carol, dept=Eng)

Grid 2 — sort only (name shown/sort desc, dept shown, no criteria):
  all 4 rows kept; sorted by name desc -> Dave, Carol, Bob, Alice
  => result cols = [name, dept], 4 rows in that order

## Scenarios

### qbe_col_new / qbe_new / qbe_add

#### carries all four declared fields on QbeColumn

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qcol = qbe_col_new("salary", ">90000", false, "")
expect(qcol.col).to_equal("salary")
expect(qcol.criteria).to_equal(">90000")
expect(qcol.shown).to_equal(false)
expect(qcol.sort).to_equal("")
```

</details>

#### starts empty and qbe_add RETURNS a new object with the column appended

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qbe = qbe_new()
expect(qbe.columns.len()).to_equal(0)
val qbe2 = qbe_add(qbe, qbe_col_new("name", "", true, "asc"))
expect(qbe2.columns.len()).to_equal(1)
expect(qbe.columns.len()).to_equal(0)
```

</details>

### qbe_run

#### filters on dept=Eng AND salary>90000, sorts by name asc, hides salary -> just Carol/Eng

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
var qbe = qbe_new()
qbe = qbe_add(qbe, qbe_col_new("name", "", true, "asc"))
qbe = qbe_add(qbe, qbe_col_new("dept", "=Eng", true, ""))
qbe = qbe_add(qbe, qbe_col_new("salary", ">90000", false, ""))
val result = qbe_run(qbe, employees)
expect(result.cols).to_equal(["name", "dept"])
expect(table_row_count(result)).to_equal(1)
expect(table_get(result, 0, "name")).to_equal("Carol")
expect(table_get(result, 0, "dept")).to_equal("Eng")
expect(table_col_index(result, "salary")).to_equal(-1)
```

</details>

#### with no criteria, keeps all rows and sorts by the first sort column (name desc)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
var qbe = qbe_new()
qbe = qbe_add(qbe, qbe_col_new("name", "", true, "desc"))
qbe = qbe_add(qbe, qbe_col_new("dept", "", true, ""))
val result = qbe_run(qbe, employees)
expect(result.cols).to_equal(["name", "dept"])
expect(table_row_count(result)).to_equal(4)
expect(_names(result)).to_equal(["Dave", "Carol", "Bob", "Alice"])
```

</details>

### qbe_criteria_summary

#### renders one preview line per column carrying a criterion or sort

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var qbe = qbe_new()
qbe = qbe_add(qbe, qbe_col_new("name", "", true, "asc"))
qbe = qbe_add(qbe, qbe_col_new("dept", "=Eng", true, ""))
qbe = qbe_add(qbe, qbe_col_new("salary", ">90000", false, ""))
val lines = qbe_criteria_summary(qbe)
expect(lines).to_equal([
    "name  sort=asc shown=true",
    "dept =Eng sort= shown=true",
    "salary >90000 sort= shown=false",
])
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
