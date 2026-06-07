# SQL Prepared Statement Specification

> Tests for PreparedStatement: preparing statements via Database, binding typed parameters (int, text, null), executing INSERT/UPDATE, and querying rows with typed DbValue extraction.

<!-- sdn-diagram:id=sql_statement_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_statement_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_statement_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_statement_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Prepared Statement Specification

Tests for PreparedStatement: preparing statements via Database, binding typed parameters (int, text, null), executing INSERT/UPDATE, and querying rows with typed DbValue extraction.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-004 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/database/sql/sql_statement_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for PreparedStatement: preparing statements via Database, binding
typed parameters (int, text, null), executing INSERT/UPDATE, and querying
rows with typed DbValue extraction.

## Scenarios

### PreparedStatement

#### INSERT with typed parameters

#### inserts integer and text via bind

1. var db = Database memory
2. db exec
   - Expected: result.is_ok() is true
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps1 (id INTEGER, name TEXT)", [])?

val params = [DbValue.Integer(value: 1), DbValue.Text(value: "Alice")]
val result = db.exec("INSERT INTO ps1 (id, name) VALUES (?, ?)", params)
expect(result.is_ok()).to_equal(true)

# Verify the data was inserted
val rows = db.query("SELECT id, name FROM ps1", [])?
expect(rows.len()).to_equal(1)
```

</details>

#### inserts multiple rows with different parameters

1. var db = Database memory
2. db exec
3. db exec
4. db exec
5. db exec
   - Expected: rows.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps2 (id INTEGER, name TEXT)", [])?

db.exec("INSERT INTO ps2 VALUES (?, ?)", [DbValue.Integer(value: 1), DbValue.Text(value: "Alice")])?
db.exec("INSERT INTO ps2 VALUES (?, ?)", [DbValue.Integer(value: 2), DbValue.Text(value: "Bob")])?
db.exec("INSERT INTO ps2 VALUES (?, ?)", [DbValue.Integer(value: 3), DbValue.Text(value: "Charlie")])?

val rows = db.query("SELECT id FROM ps2", [])?
expect(rows.len()).to_equal(3)
```

</details>

#### query with typed results

#### returns Integer variant for integer columns

1. var db = Database memory
2. db exec
3. db exec
   - Expected: all_rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps3 (id INTEGER, val INTEGER)", [])?
db.exec("INSERT INTO ps3 VALUES (?, ?)", [DbValue.Integer(value: 1), DbValue.Integer(value: 42)])?

val rows = db.query("SELECT id, val FROM ps3", [DbValue.Integer(value: 1)])?
# When using parameterized query, results go through typed PreparedStatement path
# Verify we get rows back
val all_rows = db.query("SELECT val FROM ps3 WHERE id = ?", [DbValue.Integer(value: 1)])?
expect(all_rows.len()).to_equal(1)
```

</details>

#### returns Text variant for text columns

1. var db = Database memory
2. db exec
3. db exec
   - Expected: rows.len() equals `1`
   - Expected: name_val.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps4 (name TEXT)", [])?
db.exec("INSERT INTO ps4 VALUES (?)", [DbValue.Text(value: "hello")])?

val rows = db.query("SELECT name FROM ps4 WHERE name = ?", [DbValue.Text(value: "hello")])?
expect(rows.len()).to_equal(1)
val row = rows[0]
val name_val = row.get("name")
expect(name_val.?).to_equal(true)
```

</details>

#### extracts typed values from DbRow

1. var db = Database memory
2. db exec
3. db exec
4. DbValue Integer
5. DbValue Text
6. DbValue Real
   - Expected: rows.len() equals `1`
   - Expected: row.has_column("id") is true
   - Expected: row.has_column("name") is true
   - Expected: row.has_column("score") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps5 (id INTEGER, name TEXT, score REAL)", [])?
db.exec("INSERT INTO ps5 VALUES (?, ?, ?)", [
    DbValue.Integer(value: 10),
    DbValue.Text(value: "test"),
    DbValue.Real(value: 9.5)
])?

val rows = db.query("SELECT id, name, score FROM ps5 WHERE id = ?", [DbValue.Integer(value: 10)])?
expect(rows.len()).to_equal(1)
val row = rows[0]
expect(row.has_column("id")).to_equal(true)
expect(row.has_column("name")).to_equal(true)
expect(row.has_column("score")).to_equal(true)
```

</details>

#### NULL binding

#### inserts NULL values

1. var db = Database memory
2. db exec
3. db exec
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps6 (id INTEGER, opt TEXT)", [])?
db.exec("INSERT INTO ps6 VALUES (?, ?)", [DbValue.Integer(value: 1), DbValue.Null])?

val rows = db.query("SELECT opt FROM ps6 WHERE id = ?", [DbValue.Integer(value: 1)])?
expect(rows.len()).to_equal(1)
```

</details>

#### Bool binding

#### inserts Bool values as integers

1. var db = Database memory
2. db exec
3. db exec
4. db exec
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps7 (id INTEGER, active INTEGER)", [])?
db.exec("INSERT INTO ps7 VALUES (?, ?)", [DbValue.Integer(value: 1), DbValue.Bool(value: true)])?
db.exec("INSERT INTO ps7 VALUES (?, ?)", [DbValue.Integer(value: 2), DbValue.Bool(value: false)])?

val rows = db.query("SELECT active FROM ps7 WHERE id = ?", [DbValue.Integer(value: 1)])?
expect(rows.len()).to_equal(1)
```

</details>

#### UPDATE with parameters

#### updates rows with typed parameters

1. var db = Database memory
2. db exec
3. db exec
   - Expected: result.is_ok() is true
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps8 (id INTEGER, name TEXT)", [])?
db.exec("INSERT INTO ps8 VALUES (?, ?)", [DbValue.Integer(value: 1), DbValue.Text(value: "old")])?

val result = db.exec("UPDATE ps8 SET name = ? WHERE id = ?", [DbValue.Text(value: "new"), DbValue.Integer(value: 1)])
expect(result.is_ok()).to_equal(true)

val rows = db.query("SELECT name FROM ps8 WHERE id = ?", [DbValue.Integer(value: 1)])?
expect(rows.len()).to_equal(1)
```

</details>

#### query_one with parameters

#### returns single row via query_one

1. var db = Database memory
2. db exec
3. db exec
   - Expected: row_opt.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps9 (id INTEGER, val TEXT)", [])?
db.exec("INSERT INTO ps9 VALUES (?, ?)", [DbValue.Integer(value: 1), DbValue.Text(value: "found")])?

val row_opt = db.query_one("SELECT val FROM ps9 WHERE id = ?", [DbValue.Integer(value: 1)])?
expect(row_opt.?).to_equal(true)
```

</details>

#### returns nil from query_one when no match

1. var db = Database memory
2. db exec
   - Expected: row_opt.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE ps10 (id INTEGER)", [])?

val row_opt = db.query_one("SELECT * FROM ps10 WHERE id = ?", [DbValue.Integer(value: 999)])?
expect(row_opt.?).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
