# SQL Escape Utilities Specification

> Tests for SQL escape utilities: identifier quoting, value quoting, sanitization of table/column names, and placeholder generation for prepared statements.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SQL escape utilities: identifier quoting, value quoting,
sanitization of table/column names, and placeholder generation for
prepared statements.

## Scenarios

### quote_ident

#### quotes a normal name

- quotes a normal name
   - Expected: result equals `"users"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes a normal name")
val result = quote_ident("users")
expect(result).to_equal("\"users\"")
```

</details>

#### doubles embedded double quotes

- doubles embedded double quotes
   - Expected: result equals `"my""table"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("doubles embedded double quotes")
val result = quote_ident("my\"table")
expect(result).to_equal("\"my\"\"table\"")
```

</details>

#### handles empty string

- handles empty string
   - Expected: result equals `""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
val result = quote_ident("")
expect(result).to_equal("\"\"")
```

</details>

#### handles name with spaces

- handles name with spaces
   - Expected: result equals `"my table"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles name with spaces")
val result = quote_ident("my table")
expect(result).to_equal("\"my table\"")
```

</details>

#### handles name with special characters

- handles name with special characters
   - Expected: result equals `"col-name.1"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles name with special characters")
val result = quote_ident("col-name.1")
expect(result).to_equal("\"col-name.1\"")
```

</details>

### quote_value

#### quotes a normal value

- quotes a normal value
   - Expected: result equals `'hello'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes a normal value")
val result = quote_value("hello")
expect(result).to_equal("'hello'")
```

</details>

#### escapes embedded single quotes (O'Brien)

- escapes embedded single quotes (O'Brien)
   - Expected: result equals `'O''Brien'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes embedded single quotes (O'Brien)")
val result = quote_value("O'Brien")
expect(result).to_equal("'O''Brien'")
```

</details>

#### handles empty string

- handles empty string
   - Expected: result equals `''`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
val result = quote_value("")
expect(result).to_equal("''")
```

</details>

#### handles value with multiple single quotes

- handles value with multiple single quotes
   - Expected: result equals `'it''s a ''test'''`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles value with multiple single quotes")
val result = quote_value("it's a 'test'")
expect(result).to_equal("'it''s a ''test'''")
```

</details>

### sanitize_table

#### keeps alphanumeric and underscore

- keeps alphanumeric and underscore
   - Expected: result equals `my_table_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps alphanumeric and underscore")
val result = sanitize_table("my_table_1")
expect(result).to_equal("my_table_1")
```

</details>

#### strips special characters

- strips special characters
   - Expected: result equals `droptable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips special characters")
val result = sanitize_table("drop; --table")
expect(result).to_equal("droptable")
```

</details>

#### handles empty string

- handles empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
val result = sanitize_table("")
expect(result).to_equal("")
```

</details>

#### strips spaces and dashes

- strips spaces and dashes
   - Expected: result equals `mytablename`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips spaces and dashes")
val result = sanitize_table("my-table name")
expect(result).to_equal("mytablename")
```

</details>

### sanitize_column

#### keeps valid column name

- keeps valid column name
   - Expected: result equals `user_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid column name")
val result = sanitize_column("user_id")
expect(result).to_equal("user_id")
```

</details>

#### strips injection characters

- strips injection characters
   - Expected: result equals `colDROPTABLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips injection characters")
val result = sanitize_column("col; DROP TABLE")
expect(result).to_equal("colDROPTABLE")
```

</details>

### placeholder_list

#### returns empty string for 0

- returns empty string for 0
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for 0")
val result = placeholder_list(0)
expect(result).to_equal("")
```

</details>

#### returns single placeholder for 1

- returns single placeholder for 1
   - Expected: result equals `?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single placeholder for 1")
val result = placeholder_list(1)
expect(result).to_equal("?")
```

</details>

#### returns three placeholders for 3

- returns three placeholders for 3
   - Expected: result equals `?, ?, ?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns three placeholders for 3")
val result = placeholder_list(3)
expect(result).to_equal("?, ?, ?")
```

</details>

#### returns empty for negative count

- returns empty for negative count
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for negative count")
val result = placeholder_list(-1)
expect(result).to_equal("")
```

</details>

### set_clause

#### generates single column set clause

- generates single column set clause
   - Expected: result equals `"name" = ?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates single column set clause")
val result = set_clause(["name"])
expect(result).to_equal("\"name\" = ?")
```

</details>

#### generates multi-column set clause

- generates multi-column set clause
   - Expected: result equals `"name" = ?, "age" = ?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates multi-column set clause")
val result = set_clause(["name", "age"])
expect(result).to_equal("\"name\" = ?, \"age\" = ?")
```

</details>

#### generates empty set clause for empty list

- generates empty set clause for empty list
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates empty set clause for empty list")
val result = set_clause([])
expect(result).to_equal("")
```

</details>

### column_list

#### generates single column

- generates single column
   - Expected: result equals `"id"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates single column")
val result = column_list(["id"])
expect(result).to_equal("\"id\"")
```

</details>

#### generates multi-column list

- generates multi-column list
   - Expected: result equals `"id", "name", "email"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates multi-column list")
val result = column_list(["id", "name", "email"])
expect(result).to_equal("\"id\", \"name\", \"email\"")
```

</details>

#### generates empty list for no columns

- generates empty list for no columns
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates empty list for no columns")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dba35618fc64e80c1e78e1a144085f65d73c6ef7811ea20be1528743fd429147`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dba35618fc64e80c1e78e1a144085f65d73c6ef7811ea20be1528743fd429147`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dba35618fc64e80c1e78e1a144085f65d73c6ef7811ea20be1528743fd429147`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/database/sql/sql_escape_spec.spl
mirror: doc/06_spec/01_unit/lib/database/sql/sql_escape_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/sql/sql_escape_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/sql/sql_escape_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/sql/sql_escape_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'quotes a normal name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/sql/sql_escape_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doubles embedded double quotes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/sql/sql_escape_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
