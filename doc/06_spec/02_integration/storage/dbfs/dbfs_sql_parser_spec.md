# Dbfs Sql Parser Specification

> Tests covering SQL Tokenizer, SQL Parser - SELECT, SQL Parser - INSERT, SQL Parser - UPDATE, SQL Parser - DELETE, SQL Parser - CREATE TABLE, SQL Parser - Expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Sql Parser Specification

## Scenarios

### SQL Tokenizer

#### tokenizes SELECT statement keywords

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenizes SELECT statement keywords


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes SELECT statement keywords")
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

#### preserves complete CREATE keywords and identifiers

- preserves complete CREATE keywords and identifiers


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves complete CREATE keywords and identifiers")
val tokens = sql_tokenize("CREATE TABLE messaging_events")
expect tokens[0].kind == SqlTokenKind.Create
expect tokens[0].value == "CREATE"
expect tokens[1].kind == SqlTokenKind.Table
expect tokens[1].value == "TABLE"
expect tokens[2].kind == SqlTokenKind.Ident
expect tokens[2].value == "messaging_events"
```

</details>

#### tokenizes string literals

- tokenizes string literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes string literals")
val tokens = sql_tokenize("'hello world'")
expect tokens[0].kind == SqlTokenKind.StringLit
expect tokens[0].value == "hello world"
```

</details>

#### preserves escaped quotes and multibyte string spans

- preserves escaped quotes and multibyte string spans


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves escaped quotes and multibyte string spans")
val tokens = sql_tokenize("'agent''s café'")
expect tokens[0].kind == SqlTokenKind.StringLit
expect tokens[0].value == "agent's café"
```

</details>

#### tokenizes integer and float literals

- tokenizes integer and float literals


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes integer and float literals")
val tokens = sql_tokenize("42 3.14")
expect tokens[0].kind == SqlTokenKind.IntLit
expect tokens[0].value == "42"
expect tokens[1].kind == SqlTokenKind.FloatLit
expect tokens[1].value == "3.14"
```

</details>

#### tokenizes comparison operators

- tokenizes comparison operators


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tokenizes comparison operators")
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

- is case insensitive for keywords


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is case insensitive for keywords")
val tokens = sql_tokenize("select FROM Where")
expect tokens[0].kind == SqlTokenKind.Select
expect tokens[1].kind == SqlTokenKind.From
expect tokens[2].kind == SqlTokenKind.Where
```

</details>

### SQL Parser - SELECT

#### parses simple SELECT *

- parses simple SELECT *


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses simple SELECT *")
val result = sql_parse("SELECT * FROM users")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Select
val sel = stmt.select
expect sel.from_table == "users"
```

</details>

#### parses SELECT with WHERE

- parses SELECT with WHERE


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses SELECT with WHERE")
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

- parses SELECT with ORDER BY and LIMIT


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses SELECT with ORDER BY and LIMIT")
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

- parses SELECT DISTINCT


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses SELECT DISTINCT")
val result = sql_parse("SELECT DISTINCT name FROM users")
expect result.is_ok()
val stmt = result.unwrap()
val sel = stmt.select
expect sel.distinct == true
```

</details>

#### parses SELECT with GROUP BY and HAVING

- parses SELECT with GROUP BY and HAVING


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses SELECT with GROUP BY and HAVING")
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

- parses simple INSERT


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses simple INSERT")
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

- parses multi-row INSERT


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses multi-row INSERT")
val result = sql_parse("INSERT INTO users (name) VALUES ('Alice'), ('Bob')")
expect result.is_ok()
val stmt = result.unwrap()
val ins = stmt.insert
expect ins.values.len() == 2
```

</details>

### SQL Parser - UPDATE

#### parses UPDATE with WHERE

- parses UPDATE with WHERE


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses UPDATE with WHERE")
val result = sql_parse("UPDATE users SET name = 'Bob' WHERE id = 1")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Update
```

</details>

### SQL Parser - DELETE

#### parses DELETE with WHERE

- parses DELETE with WHERE


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses DELETE with WHERE")
val result = sql_parse("DELETE FROM users WHERE id = 1")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Delete
```

</details>

### SQL Parser - CREATE TABLE

#### parses CREATE TABLE

- parses CREATE TABLE


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses CREATE TABLE")
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

- parses CREATE TABLE IF NOT EXISTS


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses CREATE TABLE IF NOT EXISTS")
val result = sql_parse("CREATE TABLE IF NOT EXISTS users (id INTEGER)")
expect result.is_ok()
val stmt = result.unwrap()
val ct = stmt.create_table
expect ct.if_not_exists == true
```

</details>

### SQL Parser - Expressions

#### parses arithmetic expressions

- parses arithmetic expressions


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses arithmetic expressions")
val result = sql_parse("SELECT 1 + 2 * 3 FROM dual")
expect result.is_ok()
```

</details>

#### parses comparison expressions

- parses comparison expressions


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses comparison expressions")
val result = sql_parse("SELECT * FROM t WHERE a > 5 AND b < 10")
expect result.is_ok()
```

</details>

#### parses IS NULL

- parses IS NULL


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses IS NULL")
val result = sql_parse("SELECT * FROM t WHERE x IS NULL")
expect result.is_ok()
```

</details>

#### parses placeholder parameters

- parses placeholder parameters


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses placeholder parameters")
val result = sql_parse("SELECT * FROM t WHERE id = ?")
expect result.is_ok()
```

</details>

#### rejects invalid SQL

- rejects invalid SQL


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid SQL")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SQL Tokenizer, SQL Parser - SELECT, SQL Parser - INSERT, SQL Parser - UPDATE, SQL Parser - DELETE, SQL Parser - CREATE TABLE, SQL Parser - Expressions.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0983971558bf8a0654b712112f58f9f2fb8c26d1ff33b032d1a79c6825824efd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0983971558bf8a0654b712112f58f9f2fb8c26d1ff33b032d1a79c6825824efd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0983971558bf8a0654b712112f58f9f2fb8c26d1ff33b032d1a79c6825824efd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/storage/dbfs/dbfs_sql_parser_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/dbfs_sql_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/dbfs_sql_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/dbfs_sql_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/dbfs_sql_parser_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes SELECT statement keywords' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_sql_parser_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves complete CREATE keywords and identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_sql_parser_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes string literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
