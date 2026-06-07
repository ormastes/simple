# Sql Query Builder Specification

> 1. var q = SelectQuery from

<!-- sdn-diagram:id=sql_query_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_query_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_query_builder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_query_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Query Builder Specification

## Scenarios

### SelectQuery

#### basic select

#### builds SELECT * FROM table

1. var q = SelectQuery from
   - Expected: params.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_start_with("SELECT *")
expect(sql).to_contain("users")
expect(params.len()).to_equal(0)
```

</details>

#### builds SELECT with specific columns

1. var q = SelectQuery from
2. q = q select


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.select(["name", "age"])
val result = q.build()
val sql = result.0
expect(sql).to_contain("name")
expect(sql).to_contain("age")
```

</details>

#### with where_eq

#### builds SELECT with WHERE equality

1. var q = SelectQuery from
2. q = q where eq
   - Expected: params.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.where_eq("id", DbValue.Integer(value: 1))
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_contain("WHERE")
expect(sql).to_contain("id")
expect(params.len()).to_equal(1)
```

</details>

#### builds SELECT with multiple WHERE conditions

1. var q = SelectQuery from
2. q = q where eq
3. q = q where eq
   - Expected: params.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.where_eq("name", DbValue.Text(value: "Alice"))
q = q.where_eq("age", DbValue.Integer(value: 30))
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_contain("AND")
expect(params.len()).to_equal(2)
```

</details>

#### with order

#### builds SELECT with ORDER BY ASC

1. var q = SelectQuery from
2. q = q order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.order("name", SqlOrder.Asc)
val result = q.build()
val sql = result.0
expect(sql).to_contain("ORDER BY")
expect(sql).to_contain("ASC")
```

</details>

#### builds SELECT with ORDER BY DESC

1. var q = SelectQuery from
2. q = q order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.order("age", SqlOrder.Desc)
val result = q.build()
val sql = result.0
expect(sql).to_contain("DESC")
```

</details>

#### builds SELECT with multiple ORDER BY columns

1. var q = SelectQuery from
2. q = q order
3. q = q order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.order("name", SqlOrder.Asc)
q = q.order("age", SqlOrder.Desc)
val result = q.build()
val sql = result.0
expect(sql).to_contain("ASC")
expect(sql).to_contain("DESC")
```

</details>

#### with limit and offset

#### builds SELECT with LIMIT

1. var q = SelectQuery from
2. q = q limit
   - Expected: params.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.limit(10)
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_contain("LIMIT ?")
expect(params.len()).to_equal(1)
```

</details>

#### builds SELECT with LIMIT and OFFSET

1. var q = SelectQuery from
2. q = q limit
3. q = q offset
   - Expected: params.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.limit(10)
q = q.offset(20)
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_contain("LIMIT ?")
expect(sql).to_contain("OFFSET ?")
expect(params.len()).to_equal(2)
```

</details>

#### combined query

#### builds full SELECT with all clauses

1. var q = SelectQuery from
2. q = q select
3. q = q where eq
4. q = q order
5. q = q limit
6. q = q offset
   - Expected: params.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = SelectQuery.from("users")
q = q.select(["name", "age"])
q = q.where_eq("active", DbValue.Integer(value: 1))
q = q.order("name", SqlOrder.Asc)
q = q.limit(10)
q = q.offset(0)
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_contain("SELECT")
expect(sql).to_contain("WHERE")
expect(sql).to_contain("ORDER BY")
expect(sql).to_contain("LIMIT")
expect(sql).to_contain("OFFSET")
expect(params.len()).to_equal(3)
```

</details>

### InsertQuery

#### basic insert

#### builds INSERT INTO with columns and row

1. var q = InsertQuery into
2. q = q columns
3. q = q row
   - Expected: params.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = InsertQuery.into("users")
q = q.columns(["name", "age"])
q = q.row([DbValue.Text(value: "Alice"), DbValue.Integer(value: 30)])
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_start_with("INSERT INTO")
expect(sql).to_contain("users")
expect(sql).to_contain("VALUES")
expect(sql).to_contain("?")
expect(params.len()).to_equal(2)
```

</details>

#### batch insert

#### builds batch INSERT statements

1. var q = InsertQuery into
2. q = q columns
3. q = q row
4. q = q row
   - Expected: results.len() equals `2`
   - Expected: first.1.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = InsertQuery.into("users")
q = q.columns(["name", "age"])
q = q.row([DbValue.Text(value: "Alice"), DbValue.Integer(value: 30)])
q = q.row([DbValue.Text(value: "Bob"), DbValue.Integer(value: 25)])
val results = q.build_batch()
expect(results.len()).to_equal(2)
val first = results[0]
expect(first.0).to_contain("INSERT INTO")
expect(first.1.len()).to_equal(2)
```

</details>

### UpdateQuery

#### basic update

#### builds UPDATE with SET and WHERE

1. var q = UpdateQuery table
2. q = q set
3. q = q where eq
   - Expected: params.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = UpdateQuery.table("users")
q = q.set("name", DbValue.Text(value: "Bob"))
q = q.where_eq("id", DbValue.Integer(value: 1))
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_start_with("UPDATE")
expect(sql).to_contain("SET")
expect(sql).to_contain("WHERE")
expect(params.len()).to_equal(2)
```

</details>

#### builds UPDATE with multiple SET columns

1. var q = UpdateQuery table
2. q = q set
3. q = q set
4. q = q where eq
   - Expected: params.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = UpdateQuery.table("users")
q = q.set("name", DbValue.Text(value: "Bob"))
q = q.set("age", DbValue.Integer(value: 31))
q = q.where_eq("id", DbValue.Integer(value: 1))
val result = q.build()
val sql = result.0
val params = result.1
expect(params.len()).to_equal(3)
```

</details>

### DeleteQuery

#### basic delete

#### builds DELETE FROM with WHERE

1. var q = DeleteQuery from
2. q = q where eq
   - Expected: params.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = DeleteQuery.from("users")
q = q.where_eq("id", DbValue.Integer(value: 1))
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_start_with("DELETE FROM")
expect(sql).to_contain("WHERE")
expect(params.len()).to_equal(1)
```

</details>

#### builds DELETE FROM without WHERE

1. var q = DeleteQuery from
   - Expected: params.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = DeleteQuery.from("users")
val result = q.build()
val sql = result.0
val params = result.1
expect(sql).to_start_with("DELETE FROM")
expect(params.len()).to_equal(0)
```

</details>

### Expression Helpers

#### sql_eq

#### creates equality expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = sql_eq("name", DbValue.Text(value: "Alice"))
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("=")
expect(compiled.sql).to_contain("name")
expect(compiled.params.len()).to_equal(1)
```

</details>

#### sql_and

#### creates AND expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = sql_eq("name", DbValue.Text(value: "Alice"))
val right = sql_eq("age", DbValue.Integer(value: 30))
val expr = sql_and(left, right)
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("AND")
expect(compiled.params.len()).to_equal(2)
```

</details>

#### sql_or

#### creates OR expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = sql_eq("name", DbValue.Text(value: "Alice"))
val right = sql_eq("name", DbValue.Text(value: "Bob"))
val expr = sql_or(left, right)
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("OR")
expect(compiled.params.len()).to_equal(2)
```

</details>

#### sql_not

#### creates NOT expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = sql_eq("active", DbValue.Integer(value: 0))
val expr = sql_not(inner)
val compiled = compile_expr(expr)
expect(compiled.sql).to_start_with("NOT")
expect(compiled.params.len()).to_equal(1)
```

</details>

#### sql_is_null

#### creates IS NULL expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = sql_is_null("deleted_at")
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("IS NULL")
expect(compiled.params.len()).to_equal(0)
```

</details>

#### sql_is_not_null

#### creates IS NOT NULL expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = sql_is_not_null("email")
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("IS NOT NULL")
expect(compiled.params.len()).to_equal(0)
```

</details>

#### sql_like

#### creates LIKE expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = sql_like("name", "%Alice%")
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("LIKE")
expect(compiled.params.len()).to_equal(1)
```

</details>

#### sql_in

#### creates IN expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [DbValue.Integer(value: 1), DbValue.Integer(value: 2), DbValue.Integer(value: 3)]
val expr = sql_in("id", values)
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("IN")
expect(compiled.params.len()).to_equal(3)
```

</details>

#### sql_raw

#### creates raw SQL expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = sql_raw("1 = 1")
val compiled = compile_expr(expr)
expect(compiled.sql).to_equal("1 = 1")
expect(compiled.params.len()).to_equal(0)
```

</details>

#### compile_expr

#### compiles simple equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = sql_eq("id", DbValue.Integer(value: 42))
val compiled = compile_expr(expr)
expect(compiled.sql).to_contain("= ?")
expect(compiled.params.len()).to_equal(1)
```

</details>

#### compiles nested AND/OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = sql_eq("x", DbValue.Integer(value: 1))
val b = sql_eq("y", DbValue.Integer(value: 2))
val c = sql_eq("z", DbValue.Integer(value: 3))
val and_expr = sql_and(a, b)
val or_expr = sql_or(and_expr, c)
val compiled = compile_expr(or_expr)
expect(compiled.sql).to_contain("AND")
expect(compiled.sql).to_contain("OR")
expect(compiled.params.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/sql/sql_query_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SelectQuery
- InsertQuery
- UpdateQuery
- DeleteQuery
- Expression Helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
