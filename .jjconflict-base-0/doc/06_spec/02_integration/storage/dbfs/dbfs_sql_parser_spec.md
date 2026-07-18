# Dbfs Sql Parser Specification

> 1. expect tokens len

<!-- sdn-diagram:id=dbfs_sql_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_sql_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_sql_parser_spec -> std
dbfs_sql_parser_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_sql_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Sql Parser Specification

## Scenarios

### SQL Tokenizer

#### tokenizes SELECT statement keywords

1. expect tokens len


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = sql_tokenize("SELECT * FROM users")
expect tokens.len() == 5
expect tokens[0].kind == SqlTokenKind.Select
expect tokens[1].kind == SqlTokenKind.Star
expect tokens[2].kind == SqlTokenKind.From
expect tokens[3].kind == SqlTokenKind.Ident
expect tokens[3].value == "users"
expect tokens[4].kind == SqlTokenKind.Eof
```

</details>

#### tokenizes string literals

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = sql_tokenize("'hello world'")
expect tokens[0].kind == SqlTokenKind.StringLit
expect tokens[0].value == "hello world"
```

</details>

#### tokenizes integer and float literals

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = sql_tokenize("42 3.14")
expect tokens[0].kind == SqlTokenKind.IntLit
expect tokens[0].value == "42"
expect tokens[1].kind == SqlTokenKind.FloatLit
expect tokens[1].value == "3.14"
```

</details>

#### tokenizes comparison operators

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = sql_tokenize("= != < > <= >=")
expect tokens[0].kind == SqlTokenKind.Eq
expect tokens[1].kind == SqlTokenKind.Ne
expect tokens[2].kind == SqlTokenKind.Lt
expect tokens[3].kind == SqlTokenKind.Gt
expect tokens[4].kind == SqlTokenKind.Le
expect tokens[5].kind == SqlTokenKind.Ge
```

</details>

#### is case insensitive for keywords

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = sql_tokenize("select FROM Where")
expect tokens[0].kind == SqlTokenKind.Select
expect tokens[1].kind == SqlTokenKind.From
expect tokens[2].kind == SqlTokenKind.Where
```

</details>

### SQL Parser - SELECT

#### parses simple SELECT *

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT * FROM users")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Select
val sel = stmt.select
expect sel.from_table == "users"
```

</details>

#### parses SELECT with WHERE

1. expect result is ok

2. expect sel columns len


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT id, name FROM users WHERE id = 1")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Select
val sel = stmt.select
expect sel.columns.len() == 2
expect sel.where_expr.?
```

</details>

#### parses SELECT with ORDER BY and LIMIT

1. expect result is ok

2. expect sel order by len


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT * FROM users ORDER BY name ASC LIMIT 10 OFFSET 5")
expect result.is_ok()
val stmt = result.unwrap()
val sel = stmt.select
expect sel.order_by.len() == 1
expect sel.limit == 10
expect sel.offset == 5
```

</details>

#### parses SELECT DISTINCT

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT DISTINCT name FROM users")
expect result.is_ok()
val stmt = result.unwrap()
val sel = stmt.select
expect sel.distinct == true
```

</details>

#### parses SELECT with GROUP BY and HAVING

1. expect result is ok

2. expect sel group by len


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT name, COUNT(*) FROM users GROUP BY name HAVING COUNT(*) > 1")
expect result.is_ok()
val stmt = result.unwrap()
val sel = stmt.select
expect sel.group_by.len() == 1
expect sel.having.?
```

</details>

### SQL Parser - INSERT

#### parses simple INSERT

1. expect result is ok

2. expect ins columns len

3. expect ins values len


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("INSERT INTO users (name, age) VALUES ('Alice', 30)")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Insert
val ins = stmt.insert
expect ins.table == "users"
expect ins.columns.len() == 2
expect ins.values.len() == 1
```

</details>

#### parses multi-row INSERT

1. expect result is ok

2. expect ins values len


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("INSERT INTO users (name) VALUES ('Alice'), ('Bob')")
expect result.is_ok()
val stmt = result.unwrap()
val ins = stmt.insert
expect ins.values.len() == 2
```

</details>

### SQL Parser - UPDATE

#### parses UPDATE with WHERE

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("UPDATE users SET name = 'Bob' WHERE id = 1")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Update
```

</details>

### SQL Parser - DELETE

#### parses DELETE with WHERE

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("DELETE FROM users WHERE id = 1")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Delete
```

</details>

### SQL Parser - CREATE TABLE

#### parses CREATE TABLE

1. expect result is ok

2. expect ct columns len


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT NOT NULL)")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.CreateTable
val ct = stmt.create_table
expect ct.table == "users"
expect ct.columns.len() == 2
```

</details>

#### parses CREATE TABLE IF NOT EXISTS

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("CREATE TABLE IF NOT EXISTS users (id INTEGER)")
expect result.is_ok()
val stmt = result.unwrap()
val ct = stmt.create_table
expect ct.if_not_exists == true
```

</details>

### SQL Parser - Expressions

#### parses arithmetic expressions

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT 1 + 2 * 3 FROM dual")
expect result.is_ok()
```

</details>

#### parses comparison expressions

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT * FROM t WHERE a > 5 AND b < 10")
expect result.is_ok()
```

</details>

#### parses IS NULL

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT * FROM t WHERE x IS NULL")
expect result.is_ok()
```

</details>

#### parses placeholder parameters

1. expect result is ok


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("SELECT * FROM t WHERE id = ?")
expect result.is_ok()
```

</details>

#### rejects invalid SQL

1. expect result is err


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sql_parse("INVALID QUERY")
expect result.is_err()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_sql_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SQL Tokenizer
- SQL Parser - SELECT
- SQL Parser - INSERT
- SQL Parser - UPDATE
- SQL Parser - DELETE
- SQL Parser - CREATE TABLE
- SQL Parser - Expressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
