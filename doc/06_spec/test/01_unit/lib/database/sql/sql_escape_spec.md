# SQL Escape Utilities Specification

> Tests for SQL escape utilities: identifier quoting, value quoting, sanitization of table/column names, and placeholder generation for prepared statements.

<!-- sdn-diagram:id=sql_escape_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_escape_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_escape_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_escape_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Escape Utilities Specification

Tests for SQL escape utilities: identifier quoting, value quoting, sanitization of table/column names, and placeholder generation for prepared statements.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-002 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/database/sql/sql_escape_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SQL escape utilities: identifier quoting, value quoting,
sanitization of table/column names, and placeholder generation for
prepared statements.

## Scenarios

### quote_ident

#### quotes a normal name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_ident("users")
expect(result).to_equal("\"users\"")
```

</details>

#### doubles embedded double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_ident("my\"table")
expect(result).to_equal("\"my\"\"table\"")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_ident("")
expect(result).to_equal("\"\"")
```

</details>

#### handles name with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_ident("my table")
expect(result).to_equal("\"my table\"")
```

</details>

#### handles name with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_ident("col-name.1")
expect(result).to_equal("\"col-name.1\"")
```

</details>

### quote_value

#### quotes a normal value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_value("hello")
expect(result).to_equal("'hello'")
```

</details>

#### escapes embedded single quotes (O'Brien)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_value("O'Brien")
expect(result).to_equal("'O''Brien'")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_value("")
expect(result).to_equal("''")
```

</details>

#### handles value with multiple single quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_value("it's a 'test'")
expect(result).to_equal("'it''s a ''test'''")
```

</details>

### sanitize_table

#### keeps alphanumeric and underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_table("my_table_1")
expect(result).to_equal("my_table_1")
```

</details>

#### strips special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_table("drop; --table")
expect(result).to_equal("droptable")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_table("")
expect(result).to_equal("")
```

</details>

#### strips spaces and dashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_table("my-table name")
expect(result).to_equal("mytablename")
```

</details>

### sanitize_column

#### keeps valid column name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_column("user_id")
expect(result).to_equal("user_id")
```

</details>

#### strips injection characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_column("col; DROP TABLE")
expect(result).to_equal("colDROPTABLE")
```

</details>

### placeholder_list

#### returns empty string for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = placeholder_list(0)
expect(result).to_equal("")
```

</details>

#### returns single placeholder for 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = placeholder_list(1)
expect(result).to_equal("?")
```

</details>

#### returns three placeholders for 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = placeholder_list(3)
expect(result).to_equal("?, ?, ?")
```

</details>

#### returns empty for negative count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = placeholder_list(-1)
expect(result).to_equal("")
```

</details>

### set_clause

#### generates single column set clause

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = set_clause(["name"])
expect(result).to_equal("\"name\" = ?")
```

</details>

#### generates multi-column set clause

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = set_clause(["name", "age"])
expect(result).to_equal("\"name\" = ?, \"age\" = ?")
```

</details>

#### generates empty set clause for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = set_clause([])
expect(result).to_equal("")
```

</details>

### column_list

#### generates single column

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = column_list(["id"])
expect(result).to_equal("\"id\"")
```

</details>

#### generates multi-column list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = column_list(["id", "name", "email"])
expect(result).to_equal("\"id\", \"name\", \"email\"")
```

</details>

#### generates empty list for no columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = column_list([])
expect(result).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
