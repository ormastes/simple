# SQL Database Connection Specification

> Tests for the Database connection facade: opening in-memory databases, executing DDL/DML, querying rows, and lifecycle management (close). All tests use Database.memory() for isolation.

<!-- sdn-diagram:id=sql_connection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_connection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_connection_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_connection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Database Connection Specification

Tests for the Database connection facade: opening in-memory databases, executing DDL/DML, querying rows, and lifecycle management (close). All tests use Database.memory() for isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-003 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/database/sql/sql_connection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Database connection facade: opening in-memory databases,
executing DDL/DML, querying rows, and lifecycle management (close).
All tests use Database.memory() for isolation.

## Scenarios

### Database

#### opening

#### opens an in-memory database successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_result = Database.memory()
expect(db_result.is_ok()).to_equal(true)
```

</details>

#### exec

#### creates a table with exec

1. var db = Database memory
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val result = db.exec("CREATE TABLE t1 (id INTEGER PRIMARY KEY, name TEXT)", [])
expect(result.is_ok()).to_equal(true)
```

</details>

#### inserts data with exec

1. var db = Database memory
2. db exec
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t2 (id INTEGER PRIMARY KEY, val TEXT)", [])?
val result = db.exec("INSERT INTO t2 (id, val) VALUES (1, 'hello')", [])
expect(result.is_ok()).to_equal(true)
```

</details>

#### inserts with typed parameters

1. var db = Database memory
2. db exec
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t3 (id INTEGER, name TEXT)", [])?
val params = [DbValue.Integer(value: 1), DbValue.Text(value: "Alice")]
val result = db.exec("INSERT INTO t3 (id, name) VALUES (?, ?)", params)
expect(result.is_ok()).to_equal(true)
```

</details>

#### query

#### returns rows from a query

1. var db = Database memory
2. db exec
3. db exec
4. db exec
   - Expected: rows_result.is_ok() is true
   - Expected: rows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t4 (id INTEGER PRIMARY KEY, name TEXT)", [])?
db.exec("INSERT INTO t4 (id, name) VALUES (1, 'Alice')", [])?
db.exec("INSERT INTO t4 (id, name) VALUES (2, 'Bob')", [])?

val rows_result = db.query("SELECT id, name FROM t4 ORDER BY id", [])
expect(rows_result.is_ok()).to_equal(true)
val rows = rows_result?
expect(rows.len()).to_equal(2)
```

</details>

#### returns empty list for no matches

1. var db = Database memory
2. db exec
   - Expected: rows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t5 (id INTEGER)", [])?

val rows = db.query("SELECT * FROM t5", [])?
expect(rows.len()).to_equal(0)
```

</details>

#### queries with typed parameters

1. var db = Database memory
2. db exec
3. db exec
4. db exec
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t6 (id INTEGER, name TEXT)", [])?
db.exec("INSERT INTO t6 VALUES (1, 'Alice')", [])?
db.exec("INSERT INTO t6 VALUES (2, 'Bob')", [])?

val params = [DbValue.Integer(value: 2)]
val rows = db.query("SELECT name FROM t6 WHERE id = ?", params)?
expect(rows.len()).to_equal(1)
```

</details>

#### query_one

#### returns single row

1. var db = Database memory
2. db exec
3. db exec
   - Expected: result.is_ok() is true
   - Expected: row_opt.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t7 (id INTEGER PRIMARY KEY, val TEXT)", [])?
db.exec("INSERT INTO t7 VALUES (1, 'only')", [])?

val result = db.query_one("SELECT val FROM t7 WHERE id = 1", [])
expect(result.is_ok()).to_equal(true)
val row_opt = result?
expect(row_opt.?).to_equal(true)
```

</details>

#### returns nil when no rows match

1. var db = Database memory
2. db exec
   - Expected: row_opt.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t8 (id INTEGER)", [])?

val row_opt = db.query_one("SELECT * FROM t8 WHERE id = 999", [])?
expect(row_opt.?).to_equal(false)
```

</details>

#### query_value

#### returns single scalar value

1. var db = Database memory
2. db exec
3. db exec
   - Expected: result.is_ok() is true
   - Expected: val_opt.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t9 (id INTEGER, val TEXT)", [])?
db.exec("INSERT INTO t9 VALUES (1, 'scalar')", [])?

val result = db.query_value("SELECT val FROM t9 WHERE id = 1", [])
expect(result.is_ok()).to_equal(true)
val val_opt = result?
expect(val_opt.?).to_equal(true)
```

</details>

#### returns nil for empty result

1. var db = Database memory
2. db exec
   - Expected: val_opt.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t10 (id INTEGER)", [])?

val val_opt = db.query_value("SELECT id FROM t10", [])?
expect(val_opt.?).to_equal(false)
```

</details>

#### table_exists

#### returns true for existing table

1. var db = Database memory
2. db exec
   - Expected: db.table_exists("t11") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t11 (id INTEGER)", [])?
expect(db.table_exists("t11")).to_equal(true)
```

</details>

#### returns false for non-existing table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = Database.memory()?
expect(db.table_exists("no_such_table")).to_equal(false)
```

</details>

#### close

#### closes successfully

1. var db = Database memory
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val result = db.close()
expect(result.is_ok()).to_equal(true)
```

</details>

#### returns error when exec after close

1. var db = Database memory
2. db close
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.close()?
val result = db.exec("SELECT 1", [])
expect(result.is_err()).to_equal(true)
```

</details>

#### returns error when query after close

1. var db = Database memory
2. db close
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.close()?
val result = db.query("SELECT 1", [])
expect(result.is_err()).to_equal(true)
```

</details>

#### returns error when closing twice

1. var db = Database memory
2. db close
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.close()?
val result = db.close()
expect(result.is_err()).to_equal(true)
```

</details>

#### exec_sql convenience

#### executes SQL without parameters

1. var db = Database memory
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val result = db.exec_sql("CREATE TABLE t12 (id INTEGER)")
expect(result.is_ok()).to_equal(true)
```

</details>

#### last_insert_rowid

#### returns the last inserted row id

1. var db = Database memory
2. db exec
3. db exec


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE t13 (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT)", [])?
db.exec("INSERT INTO t13 (name) VALUES ('first')", [])?
val rowid = db.last_insert_rowid()
expect(rowid).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
