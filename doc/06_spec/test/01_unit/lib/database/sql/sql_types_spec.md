# SQL Types Specification

> Tests for the core SQL type system: DbValue construction and accessors, DbRow column access, DbError message formatting.

<!-- sdn-diagram:id=sql_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Types Specification

Tests for the core SQL type system: DbValue construction and accessors, DbRow column access, DbError message formatting.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/database/sql/sql_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the core SQL type system: DbValue construction and accessors,
DbRow column access, DbError message formatting.

## Scenarios

### DbValue

#### Integer variant

#### constructs and extracts via as_int

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 42)
val result = v.as_int()
expect(result.?).to_equal(true)
expect(result?).to_equal(42)
```

</details>

#### returns nil for as_text on Integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 10)
val result = v.as_text()
expect(result.?).to_equal(false)
```

</details>

#### returns nil for as_real on Integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 10)
val result = v.as_real()
expect(result.?).to_equal(false)
```

</details>

#### is not null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 0)
expect(v.is_null()).to_equal(false)
```

</details>

#### reports db_type as Integer

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 5)
val t = v.db_type()
match t:
    DbType.Integer: expect(t).to_equal(DbType.Integer)
    _: fail("DbValue.Integer db_type was not DbType.Integer")
```

</details>

#### converts to text representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 99)
expect(v.to_text()).to_equal("99")
```

</details>

#### Real variant

#### constructs and extracts via as_real

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Real(value: 3.14)
val result = v.as_real()
expect(result.?).to_equal(true)
```

</details>

#### returns nil for as_int on Real

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Real(value: 2.5)
val result = v.as_int()
expect(result.?).to_equal(false)
```

</details>

#### Text variant

#### constructs and extracts via as_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Text(value: "hello")
val result = v.as_text()
expect(result.?).to_equal(true)
expect(result?).to_equal("hello")
```

</details>

#### returns nil for as_int on Text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Text(value: "abc")
val result = v.as_int()
expect(result.?).to_equal(false)
```

</details>

#### converts to text representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Text(value: "world")
expect(v.to_text()).to_equal("world")
```

</details>

#### Bool variant

#### constructs and extracts via as_bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Bool(value: true)
val result = v.as_bool()
expect(result.?).to_equal(true)
expect(result?).to_equal(true)
```

</details>

#### extracts false via as_bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Bool(value: false)
val result = v.as_bool()
expect(result.?).to_equal(true)
expect(result?).to_equal(false)
```

</details>

#### converts true Bool to int 1 via as_int

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Bool(value: true)
val result = v.as_int()
expect(result.?).to_equal(true)
expect(result?).to_equal(1)
```

</details>

#### converts false Bool to int 0 via as_int

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Bool(value: false)
val result = v.as_int()
expect(result.?).to_equal(true)
expect(result?).to_equal(0)
```

</details>

#### reports db_type as Integer for Bool

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Bool(value: true)
val t = v.db_type()
match t:
    DbType.Integer: expect(t).to_equal(DbType.Integer)
    _: fail("DbValue.Bool db_type was not DbType.Integer")
```

</details>

#### Null variant

#### is null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Null
expect(v.is_null()).to_equal(true)
```

</details>

#### returns nil for all typed accessors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Null
expect(v.as_int().?).to_equal(false)
expect(v.as_real().?).to_equal(false)
expect(v.as_text().?).to_equal(false)
expect(v.as_bool().?).to_equal(false)
```

</details>

#### converts to NULL text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Null
expect(v.to_text()).to_equal("NULL")
```

</details>

#### Integer as_bool edge cases

#### converts integer 1 to true via as_bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 1)
val result = v.as_bool()
expect(result.?).to_equal(true)
expect(result?).to_equal(true)
```

</details>

#### converts integer 0 to false via as_bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 0)
val result = v.as_bool()
expect(result.?).to_equal(true)
expect(result?).to_equal(false)
```

</details>

#### returns nil for integer 2 via as_bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DbValue.Integer(value: 2)
val result = v.as_bool()
expect(result.?).to_equal(false)
```

</details>

### DbRow

#### empty row

#### creates via static empty()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow.empty()
expect(row.column_count()).to_equal(0)
expect(row.column_names().len()).to_equal(0)
```

</details>

#### populated row

#### gets value by column name

1. values: [DbValue Integer
   - Expected: v.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["id", "name"],
    values: [DbValue.Integer(value: 1), DbValue.Text(value: "Alice")]
)
val v = row.get("name")
expect(v.?).to_equal(true)
```

</details>

#### returns nil for missing column

1. values: [DbValue Integer
   - Expected: v.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["id"],
    values: [DbValue.Integer(value: 1)]
)
val v = row.get("missing")
expect(v.?).to_equal(false)
```

</details>

#### gets text by column name

1. values: [DbValue Text
   - Expected: result.? is true
   - Expected: result? equals `Bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["name"],
    values: [DbValue.Text(value: "Bob")]
)
val result = row.get_text("name")
expect(result.?).to_equal(true)
expect(result?).to_equal("Bob")
```

</details>

#### gets int by column name

1. values: [DbValue Integer
   - Expected: result.? is true
   - Expected: result? equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["age"],
    values: [DbValue.Integer(value: 30)]
)
val result = row.get_int("age")
expect(result.?).to_equal(true)
expect(result?).to_equal(30)
```

</details>

#### gets real by column name

1. values: [DbValue Real
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["score"],
    values: [DbValue.Real(value: 9.5)]
)
val result = row.get_real("score")
expect(result.?).to_equal(true)
```

</details>

#### gets bool by column name

1. values: [DbValue Bool
   - Expected: result.? is true
   - Expected: result? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["active"],
    values: [DbValue.Bool(value: true)]
)
val result = row.get_bool("active")
expect(result.?).to_equal(true)
expect(result?).to_equal(true)
```

</details>

#### gets value by index

1. values: [DbValue Integer
   - Expected: v.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["a", "b"],
    values: [DbValue.Integer(value: 10), DbValue.Integer(value: 20)]
)
val v = row.get_at(1)
expect(v.?).to_equal(true)
```

</details>

#### returns nil for out-of-bounds index

1. values: [DbValue Integer
   - Expected: v.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["a"],
    values: [DbValue.Integer(value: 1)]
)
val v = row.get_at(5)
expect(v.?).to_equal(false)
```

</details>

#### returns nil for negative index

1. values: [DbValue Integer
   - Expected: v.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["a"],
    values: [DbValue.Integer(value: 1)]
)
val v = row.get_at(-1)
expect(v.?).to_equal(false)
```

</details>

#### has_column

#### returns true for existing column

1. values: [DbValue Integer
   - Expected: row.has_column("id") is true
   - Expected: row.has_column("name") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["id", "name"],
    values: [DbValue.Integer(value: 1), DbValue.Text(value: "X")]
)
expect(row.has_column("id")).to_equal(true)
expect(row.has_column("name")).to_equal(true)
```

</details>

#### returns false for missing column

1. values: [DbValue Integer
   - Expected: row.has_column("missing") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = DbRow(
    columns: ["id"],
    values: [DbValue.Integer(value: 1)]
)
expect(row.has_column("missing")).to_equal(false)
```

</details>

### DbError

#### formats ConnectionFailed message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.ConnectionFailed(path: "/tmp/db.sqlite", message: "not found")
expect(err.message()).to_contain("Connection failed")
expect(err.message()).to_contain("/tmp/db.sqlite")
```

</details>

#### formats QueryFailed message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.QueryFailed(sql: "SELECT *", message: "syntax error")
expect(err.message()).to_contain("Query failed")
expect(err.message()).to_contain("syntax error")
```

</details>

#### formats BindFailed message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.BindFailed(index: 3, message: "type mismatch")
expect(err.message()).to_contain("Bind failed")
expect(err.message()).to_contain("3")
```

</details>

#### formats TypeMismatch message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.TypeMismatch(column: "age", expected: "int", actual: "text")
expect(err.message()).to_contain("Type mismatch")
expect(err.message()).to_contain("age")
```

</details>

#### formats NotFound message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.NotFound(description: "user 42")
expect(err.message()).to_contain("Not found")
expect(err.message()).to_contain("user 42")
```

</details>

#### formats ConstraintViolation message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.ConstraintViolation(message: "UNIQUE constraint failed")
expect(err.message()).to_contain("Constraint violation")
```

</details>

#### formats MigrationFailed message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.MigrationFailed(id: "v002", reason: "column exists")
expect(err.message()).to_contain("Migration")
expect(err.message()).to_contain("v002")
```

</details>

#### formats TransactionFailed message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.TransactionFailed(reason: "deadlock")
expect(err.message()).to_contain("Transaction failed")
```

</details>

#### formats Closed message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.Closed
expect(err.message()).to_contain("closed")
```

</details>

#### formats Other message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = DbError.Other(message: "unexpected")
expect(err.message()).to_contain("unexpected")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
