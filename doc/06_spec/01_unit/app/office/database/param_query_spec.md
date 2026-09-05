# param_query_spec

> Parameterized, multi-condition query spec — param_query.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# param_query_spec

Parameterized, multi-condition query spec — param_query.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/param_query_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Parameterized, multi-condition query spec — param_query.spl.

Ground truth is hand-computed against one small table:

employees(name, dept, salary):
  Alice, Eng,   90000
  Bob,   Sales, 60000
  Carol, Eng,   95000
  Dave,  Sales, 55000

AND query: salary >= :min_salary AND dept = :dept, bound with
min_salary=70000, dept=Eng:
  Alice: 90000>=70000 true, Eng==Eng true -> match
  Bob:   dept Sales != Eng -> no
  Carol: 95000>=70000 true, Eng==Eng true -> match
  Dave:  dept Sales != Eng -> no
  => {Alice, Carol}

OR query: dept = :d1 OR salary >= :hi, bound with d1=Sales, hi=95000:
  Alice: dept Eng != Sales, 90000>=95000 false -> no
  Bob:   dept Sales == Sales -> match
  Carol: dept Eng != Sales, 95000>=95000 true -> match
  Dave:  dept Sales == Sales -> match
  => {Bob, Carol, Dave}

## Scenarios

### condition_new

#### carries all three declared fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = condition_new("salary", ">=", "min_salary")
expect(c.col).to_equal("salary")
expect(c.op).to_equal(">=")
expect(c.param_name).to_equal("min_salary")
```

</details>

### param_query_new / param_query_add

#### starts with the given table_name/conjunction and zero conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pq = param_query_new("employees", "and")
expect(pq.table_name).to_equal("employees")
expect(pq.conjunction).to_equal("and")
expect(pq.conditions.len()).to_equal(0)
```

</details>

#### param_query_add RETURNS a new object with the condition appended (original untouched)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pq = param_query_new("employees", "and")
val pq2 = param_query_add(pq, condition_new("salary", ">=", "min_salary"))
expect(pq2.conditions.len()).to_equal(1)
expect(pq.conditions.len()).to_equal(0)
```

</details>

### param_query_run

#### AND: salary>=:min_salary AND dept=:dept keeps exactly Alice and Carol

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
var pq = param_query_new("employees", "and")
pq = param_query_add(pq, condition_new("salary", ">=", "min_salary"))
pq = param_query_add(pq, condition_new("dept", "=", "dept"))
val result = param_query_run(pq, employees, ["min_salary", "dept"], ["70000", "Eng"])
expect(table_row_count(result)).to_equal(2)
expect(_names(result)).to_equal(["Alice", "Carol"])
```

</details>

#### OR: dept=:d1 OR salary>=:hi keeps exactly Bob, Carol, Dave

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val employees = _employees()
var pq = param_query_new("employees", "or")
pq = param_query_add(pq, condition_new("dept", "=", "d1"))
pq = param_query_add(pq, condition_new("salary", ">=", "hi"))
val result = param_query_run(pq, employees, ["d1", "hi"], ["Sales", "95000"])
expect(table_row_count(result)).to_equal(3)
expect(_names(result)).to_equal(["Bob", "Carol", "Dave"])
```

</details>

### param_query_required_params

#### returns distinct param names in first-seen order for the AND query

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pq = param_query_new("employees", "and")
pq = param_query_add(pq, condition_new("salary", ">=", "min_salary"))
pq = param_query_add(pq, condition_new("dept", "=", "dept"))
expect(param_query_required_params(pq)).to_equal(["min_salary", "dept"])
```

</details>

#### returns distinct param names in first-seen order for the OR query

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pq = param_query_new("employees", "or")
pq = param_query_add(pq, condition_new("dept", "=", "d1"))
pq = param_query_add(pq, condition_new("salary", ">=", "hi"))
expect(param_query_required_params(pq)).to_equal(["d1", "hi"])
```

</details>

### param_query_to_text

#### renders a readable SQL-like string for the AND query

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pq = param_query_new("employees", "and")
pq = param_query_add(pq, condition_new("salary", ">=", "min_salary"))
pq = param_query_add(pq, condition_new("dept", "=", "dept"))
expect(param_query_to_text(pq)).to_equal("SELECT * FROM employees WHERE salary >= :min_salary AND dept = :dept")
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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
