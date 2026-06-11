# Sql Schema Specification

> <details>

<!-- sdn-diagram:id=sql_schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_schema_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Schema Specification

## Scenarios

### ColumnDef

#### constructors

#### creates integer column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = ColumnDef.integer("age")
expect(col.name).to_equal("age")
expect(col.constraints.len()).to_equal(0)
```

</details>

#### creates text column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = ColumnDef.text_col("name")
expect(col.name).to_equal("name")
expect(col.constraints.len()).to_equal(0)
```

</details>

#### creates real column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = ColumnDef.real("score")
expect(col.name).to_equal("score")
expect(col.constraints.len()).to_equal(0)
```

</details>

#### creates blob column

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = ColumnDef.blob("data")
expect(col.name).to_equal("data")
expect(col.constraints.len()).to_equal(0)
```

</details>

#### constraint builders

#### adds primary key and autoincrement with pk()

1. var col = ColumnDef integer
2. col = col pk
   - Expected: col.constraints.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.integer("id")
col = col.pk()
expect(col.constraints.len()).to_equal(2)
```

</details>

#### adds not_null constraint

1. var col = ColumnDef text col
2. col = col not null
   - Expected: col.constraints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.text_col("name")
col = col.not_null()
expect(col.constraints.len()).to_equal(1)
```

</details>

#### adds unique constraint

1. var col = ColumnDef text col
2. col = col unique
   - Expected: col.constraints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.text_col("email")
col = col.unique()
expect(col.constraints.len()).to_equal(1)
```

</details>

#### adds default value constraint

1. var col = ColumnDef integer
2. col = col default val
   - Expected: col.constraints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.integer("status")
col = col.default_val("0")
expect(col.constraints.len()).to_equal(1)
```

</details>

#### adds foreign key constraint

1. var col = ColumnDef integer
2. col = col fk
   - Expected: col.constraints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.integer("user_id")
col = col.fk("users", "id")
expect(col.constraints.len()).to_equal(1)
```

</details>

#### adds check constraint

1. var col = ColumnDef integer
2. col = col check
   - Expected: col.constraints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.integer("age")
col = col.check("age >= 0")
expect(col.constraints.len()).to_equal(1)
```

</details>

#### chains multiple constraints via intermediate vars

1. var col = ColumnDef text col
2. col = col not null
3. col = col unique
   - Expected: col.constraints.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.text_col("email")
col = col.not_null()
col = col.unique()
expect(col.constraints.len()).to_equal(2)
```

</details>

#### to_sql output

#### generates integer column SQL

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = ColumnDef.integer("age")
val sql = col.to_sql()
expect(sql).to_contain("INTEGER")
expect(sql).to_contain("age")
```

</details>

#### generates text column SQL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = ColumnDef.text_col("name")
val sql = col.to_sql()
expect(sql).to_contain("TEXT")
```

</details>

#### generates column with primary key SQL

1. var col = ColumnDef integer
2. col = col pk


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.integer("id")
col = col.pk()
val sql = col.to_sql()
expect(sql).to_contain("PRIMARY KEY")
expect(sql).to_contain("AUTOINCREMENT")
```

</details>

#### generates column with not_null SQL

1. var col = ColumnDef text col
2. col = col not null


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.text_col("name")
col = col.not_null()
val sql = col.to_sql()
expect(sql).to_contain("NOT NULL")
```

</details>

#### generates column with unique SQL

1. var col = ColumnDef text col
2. col = col unique


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.text_col("email")
col = col.unique()
val sql = col.to_sql()
expect(sql).to_contain("UNIQUE")
```

</details>

#### generates column with default value SQL

1. var col = ColumnDef integer
2. col = col default val


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var col = ColumnDef.integer("status")
col = col.default_val("0")
val sql = col.to_sql()
expect(sql).to_contain("DEFAULT 0")
```

</details>

### ColumnConstraint

#### to_sql

#### generates PRIMARY KEY

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ColumnConstraint.PrimaryKey
expect(c.to_sql()).to_equal("PRIMARY KEY")
```

</details>

#### generates AUTOINCREMENT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ColumnConstraint.AutoIncrement
expect(c.to_sql()).to_equal("AUTOINCREMENT")
```

</details>

#### generates NOT NULL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ColumnConstraint.NotNull
expect(c.to_sql()).to_equal("NOT NULL")
```

</details>

#### generates UNIQUE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ColumnConstraint.Unique
expect(c.to_sql()).to_equal("UNIQUE")
```

</details>

#### generates DEFAULT with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ColumnConstraint.Default(value: "42")
expect(c.to_sql()).to_equal("DEFAULT 42")
```

</details>

#### generates CHECK with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ColumnConstraint.Check(expr: "age >= 0")
expect(c.to_sql()).to_equal("CHECK (age >= 0)")
```

</details>

### TableSchema

#### construction

#### creates empty schema with name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = TableSchema.new("users")
expect(schema.name).to_equal("users")
expect(schema.columns.len()).to_equal(0)
```

</details>

#### adds columns with col()

1. var schema = TableSchema new
2. schema = schema col
   - Expected: schema.columns.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
val col = ColumnDef.text_col("name")
schema = schema.col(col)
expect(schema.columns.len()).to_equal(1)
```

</details>

#### convenience methods

#### adds auto-increment id column with id_col()

1. var schema = TableSchema new
2. schema = schema id col
   - Expected: schema.columns.len() equals `1`
   - Expected: schema.columns[0].name equals `id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.id_col()
expect(schema.columns.len()).to_equal(1)
expect(schema.columns[0].name).to_equal("id")
```

</details>

#### adds NOT NULL text column with text_col()

1. var schema = TableSchema new
2. schema = schema text col
   - Expected: schema.columns.len() equals `1`
   - Expected: schema.columns[0].name equals `name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.text_col("name")
expect(schema.columns.len()).to_equal(1)
expect(schema.columns[0].name).to_equal("name")
```

</details>

#### adds NOT NULL integer column with int_col()

1. var schema = TableSchema new
2. schema = schema int col
   - Expected: schema.columns.len() equals `1`
   - Expected: schema.columns[0].name equals `age`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.int_col("age")
expect(schema.columns.len()).to_equal(1)
expect(schema.columns[0].name).to_equal("age")
```

</details>

#### adds NOT NULL real column with real_col()

1. var schema = TableSchema new
2. schema = schema real col
   - Expected: schema.columns.len() equals `1`
   - Expected: schema.columns[0].name equals `score`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("metrics")
schema = schema.real_col("score")
expect(schema.columns.len()).to_equal(1)
expect(schema.columns[0].name).to_equal("score")
```

</details>

#### adds nullable text column with nullable_text()

1. var schema = TableSchema new
2. schema = schema nullable text
   - Expected: schema.columns.len() equals `1`
   - Expected: schema.columns[0].name equals `bio`
   - Expected: schema.columns[0].constraints.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.nullable_text("bio")
expect(schema.columns.len()).to_equal(1)
expect(schema.columns[0].name).to_equal("bio")
expect(schema.columns[0].constraints.len()).to_equal(0)
```

</details>

#### adds nullable integer column with nullable_int()

1. var schema = TableSchema new
2. schema = schema nullable int
   - Expected: schema.columns.len() equals `1`
   - Expected: schema.columns[0].constraints.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.nullable_int("score")
expect(schema.columns.len()).to_equal(1)
expect(schema.columns[0].constraints.len()).to_equal(0)
```

</details>

#### column_names

#### returns list of column names

1. var schema = TableSchema new
2. schema = schema id col
3. schema = schema text col
4. schema = schema int col
   - Expected: names.len() equals `3`
   - Expected: names[0] equals `id`
   - Expected: names[1] equals `name`
   - Expected: names[2] equals `age`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.id_col()
schema = schema.text_col("name")
schema = schema.int_col("age")
val names = schema.column_names()
expect(names.len()).to_equal(3)
expect(names[0]).to_equal("id")
expect(names[1]).to_equal("name")
expect(names[2]).to_equal("age")
```

</details>

#### returns empty list for empty schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = TableSchema.new("empty")
val names = schema.column_names()
expect(names.len()).to_equal(0)
```

</details>

#### to_create_sql

#### generates CREATE TABLE statement

1. var schema = TableSchema new
2. schema = schema id col
3. schema = schema text col


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.id_col()
schema = schema.text_col("name")
val sql = schema.to_create_sql()
expect(sql).to_start_with("CREATE TABLE")
expect(sql).to_contain("users")
expect(sql).to_contain("name")
```

</details>

#### generates CREATE TABLE IF NOT EXISTS statement

1. var schema = TableSchema new
2. schema = schema id col


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.id_col()
val sql = schema.to_create_if_not_exists_sql()
expect(sql).to_contain("IF NOT EXISTS")
```

</details>

#### full schema

#### builds complete users table schema

1. var schema = TableSchema new
2. schema = schema id col
3. schema = schema text col
4. schema = schema text col
5. schema = schema int col
   - Expected: schema.columns.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.id_col()
schema = schema.text_col("name")
schema = schema.text_col("email")
schema = schema.int_col("age")
expect(schema.columns.len()).to_equal(4)
val sql = schema.to_create_sql()
expect(sql).to_contain("INTEGER")
expect(sql).to_contain("TEXT")
expect(sql).to_contain("PRIMARY KEY")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/sql/sql_schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ColumnDef
- ColumnConstraint
- TableSchema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
