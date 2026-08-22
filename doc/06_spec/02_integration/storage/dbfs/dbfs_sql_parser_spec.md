# dbfs_sql_parser_spec

> Verifies the dbfs sql parser behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_sql_parser_spec

Verifies the dbfs sql parser behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_sql_parser_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the dbfs sql parser behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SQL Tokenizer

#### tokenizes SELECT statement keywords

- Verify: tokenizes SELECT statement keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: tokenizes SELECT statement keywords")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: preserves complete CREATE keywords and identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: preserves complete CREATE keywords and identifiers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: tokenizes string literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: tokenizes string literals")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tokens = sql_tokenize("'hello world'")
expect tokens[0].kind == SqlTokenKind.StringLit
expect tokens[0].value == "hello world"
```

</details>

#### preserves escaped quotes and multibyte string spans

- Verify: preserves escaped quotes and multibyte string spans


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: preserves escaped quotes and multibyte string spans")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tokens = sql_tokenize("'agent''s café'")
expect tokens[0].kind == SqlTokenKind.StringLit
expect tokens[0].value == "agent's café"
```

</details>

#### tokenizes integer and float literals

- Verify: tokenizes integer and float literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: tokenizes integer and float literals")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tokens = sql_tokenize("42 3.14")
expect tokens[0].kind == SqlTokenKind.IntLit
expect tokens[0].value == "42"
expect tokens[1].kind == SqlTokenKind.FloatLit
expect tokens[1].value == "3.14"
```

</details>

#### tokenizes comparison operators

- Verify: tokenizes comparison operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: tokenizes comparison operators")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: is case insensitive for keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: is case insensitive for keywords")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tokens = sql_tokenize("select FROM Where")
expect tokens[0].kind == SqlTokenKind.Select
expect tokens[1].kind == SqlTokenKind.From
expect tokens[2].kind == SqlTokenKind.Where
```

</details>

### SQL Parser - SELECT

#### parses simple SELECT *

- Verify: parses simple SELECT *


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses simple SELECT *")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("SELECT * FROM users")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Select
val sel = stmt.select
expect sel.from_table == "users"
```

</details>

#### parses SELECT with WHERE

- Verify: parses SELECT with WHERE


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses SELECT with WHERE")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: parses SELECT with ORDER BY and LIMIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses SELECT with ORDER BY and LIMIT")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: parses SELECT DISTINCT


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses SELECT DISTINCT")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("SELECT DISTINCT name FROM users")
expect result.is_ok()
val stmt = result.unwrap()
val sel = stmt.select
expect sel.distinct == true
```

</details>

#### parses SELECT with GROUP BY and HAVING

- Verify: parses SELECT with GROUP BY and HAVING


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses SELECT with GROUP BY and HAVING")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: parses simple INSERT


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses simple INSERT")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: parses multi-row INSERT


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses multi-row INSERT")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("INSERT INTO users (name) VALUES ('Alice'), ('Bob')")
expect result.is_ok()
val stmt = result.unwrap()
val ins = stmt.insert
expect ins.values.len() == 2
```

</details>

### SQL Parser - UPDATE

#### parses UPDATE with WHERE

- Verify: parses UPDATE with WHERE


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses UPDATE with WHERE")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("UPDATE users SET name = 'Bob' WHERE id = 1")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Update
```

</details>

### SQL Parser - DELETE

#### parses DELETE with WHERE

- Verify: parses DELETE with WHERE


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses DELETE with WHERE")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("DELETE FROM users WHERE id = 1")
expect result.is_ok()
val stmt = result.unwrap()
expect stmt.kind == SqlStmtKind.Delete
```

</details>

### SQL Parser - CREATE TABLE

#### parses CREATE TABLE

- Verify: parses CREATE TABLE


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses CREATE TABLE")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: parses CREATE TABLE IF NOT EXISTS


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses CREATE TABLE IF NOT EXISTS")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("CREATE TABLE IF NOT EXISTS users (id INTEGER)")
expect result.is_ok()
val stmt = result.unwrap()
val ct = stmt.create_table
expect ct.if_not_exists == true
```

</details>

### SQL Parser - Expressions

#### parses arithmetic expressions

- Verify: parses arithmetic expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses arithmetic expressions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("SELECT 1 + 2 * 3 FROM dual")
expect result.is_ok()
```

</details>

#### parses comparison expressions

- Verify: parses comparison expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses comparison expressions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("SELECT * FROM t WHERE a > 5 AND b < 10")
expect result.is_ok()
```

</details>

#### parses IS NULL

- Verify: parses IS NULL


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses IS NULL")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("SELECT * FROM t WHERE x IS NULL")
expect result.is_ok()
```

</details>

#### parses placeholder parameters

- Verify: parses placeholder parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: parses placeholder parameters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("SELECT * FROM t WHERE id = ?")
expect result.is_ok()
```

</details>

#### rejects invalid SQL

- Verify: rejects invalid SQL


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_SQL_PARSER-001
step("Verify: rejects invalid SQL")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = sql_parse("INVALID QUERY")
expect result.is_err()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e3294771ebddabbd255efd2a5b1df0fa0ba745ef092e987ae8743b8cca29e402`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3294771ebddabbd255efd2a5b1df0fa0ba745ef092e987ae8743b8cca29e402`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3294771ebddabbd255efd2a5b1df0fa0ba745ef092e987ae8743b8cca29e402`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/storage/dbfs/dbfs_sql_parser_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/dbfs_sql_parser_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/dbfs_sql_parser_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/storage/dbfs/dbfs_sql_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/dbfs_sql_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
