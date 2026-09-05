# SQL Transaction Savepoint Name Injection Specification

> `Transaction.savepoint` / `release_savepoint` / `rollback_to` take a caller supplied savepoint name and place it directly into SQL text. The native runtime primitive behind those calls (`rt_sqlite_execute` in `src/runtime/runtime_sqlite.c`) is `sqlite3_exec`, which executes **every** `;`-separated statement in the string. An unvalidated name is therefore a multi-statement SQL injection sink: `"sp1; DROP TABLE users; --"` appends a DROP to the transaction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Transaction Savepoint Name Injection Specification

`Transaction.savepoint` / `release_savepoint` / `rollback_to` take a caller supplied savepoint name and place it directly into SQL text. The native runtime primitive behind those calls (`rt_sqlite_execute` in `src/runtime/runtime_sqlite.c`) is `sqlite3_exec`, which executes **every** `;`-separated statement in the string. An unvalidated name is therefore a multi-statement SQL injection sink: `"sp1; DROP TABLE users; --"` appends a DROP to the transaction.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-005 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`Transaction.savepoint` / `release_savepoint` / `rollback_to` take a caller
supplied savepoint name and place it directly into SQL text. The native
runtime primitive behind those calls (`rt_sqlite_execute` in
`src/runtime/runtime_sqlite.c`) is `sqlite3_exec`, which executes **every**
`;`-separated statement in the string. An unvalidated name is therefore a
multi-statement SQL injection sink: `"sp1; DROP TABLE users; --"` appends a
DROP to the transaction.

Every sibling module in this package (`query_builder`, `repository`,
`schema`, `sql_gen`) already routes identifiers through
`escape.quote_ident`; the savepoint family was the one path that did not.

These specs pin the fix: a savepoint name must be validated as a plain SQL
identifier and **rejected before any SQL is constructed or dispatched**. The
oracle is the error message — a rejected name reports `invalid savepoint
name`, whereas an unvalidated name is handed to the engine and fails (if at
all) with an engine-level parse error instead.

## Scenarios

### Transaction savepoint name validation

#### names carrying extra SQL are rejected before dispatch

#### rejects a savepoint name containing a statement terminator

- rejects a savepoint name containing a statement terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a savepoint name containing a statement terminator")
var db = Database.memory()?
var tx = db.begin()?
val msg = _err_text(tx.savepoint("sp1; DROP TABLE users; --"))
tx.rollback()
expect(msg).to_contain("invalid savepoint name")
```

</details>

#### rejects a rollback_to name containing a statement terminator

- rejects a rollback_to name containing a statement terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a rollback_to name containing a statement terminator")
var db = Database.memory()?
var tx = db.begin()?
val msg = _err_text(tx.rollback_to("sp1; DROP TABLE users; --"))
tx.rollback()
expect(msg).to_contain("invalid savepoint name")
```

</details>

#### rejects a release_savepoint name containing a statement terminator

- rejects a release_savepoint name containing a statement terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a release_savepoint name containing a statement terminator")
var db = Database.memory()?
var tx = db.begin()?
val msg = _err_text(tx.release_savepoint("sp1; DROP TABLE users; --"))
tx.rollback()
expect(msg).to_contain("invalid savepoint name")
```

</details>

#### rejects a savepoint name containing a comment introducer

- rejects a savepoint name containing a comment introducer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a savepoint name containing a comment introducer")
var db = Database.memory()?
var tx = db.begin()?
val msg = _err_text(tx.savepoint("sp1 -- "))
tx.rollback()
expect(msg).to_contain("invalid savepoint name")
```

</details>

#### rejects a savepoint name containing a quote character

- rejects a savepoint name containing a quote character


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a savepoint name containing a quote character")
var db = Database.memory()?
var tx = db.begin()?
val msg = _err_text(tx.savepoint("sp1\" OR \"1"))
tx.rollback()
expect(msg).to_contain("invalid savepoint name")
```

</details>

#### rejects an empty savepoint name

- rejects an empty savepoint name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty savepoint name")
var db = Database.memory()?
var tx = db.begin()?
val msg = _err_text(tx.savepoint(""))
tx.rollback()
expect(msg).to_contain("invalid savepoint name")
```

</details>

#### ordinary identifier names are not refused by the validator

#### passes a plain identifier through savepoint and release

- passes a plain identifier through savepoint and release


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a plain identifier through savepoint and release")
var db = Database.memory()?
var tx = db.begin()?
val sp = _rejected_by_validator(tx.savepoint("sp_ok"))
val rel = _rejected_by_validator(tx.release_savepoint("sp_ok"))
tx.rollback()
assert_false(sp)
assert_false(rel)
```

</details>

#### passes a plain identifier through savepoint and rollback_to

- passes a plain identifier through savepoint and rollback_to


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a plain identifier through savepoint and rollback_to")
var db = Database.memory()?
var tx = db.begin()?
val sp = _rejected_by_validator(tx.savepoint("sp_two"))
val back = _rejected_by_validator(tx.rollback_to("sp_two"))
tx.rollback()
assert_false(sp)
assert_false(back)
```

</details>

#### passes an identifier with digits and underscores

- passes an identifier with digits and underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes an identifier with digits and underscores")
var db = Database.memory()?
var tx = db.begin()?
val sp = _rejected_by_validator(tx.savepoint("sp_retry_42"))
tx.rollback()
assert_false(sp)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `af033213aba5d340f4572b00ba9e2995eef9ceaa0d377b0509a3a766c8ff8dd2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af033213aba5d340f4572b00ba9e2995eef9ceaa0d377b0509a3a766c8ff8dd2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af033213aba5d340f4572b00ba9e2995eef9ceaa0d377b0509a3a766c8ff8dd2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.spl
mirror: doc/06_spec/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a savepoint name containing a statement terminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a rollback_to name containing a statement terminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/sql/sql_transaction_savepoint_injection_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a release_savepoint name containing a statement terminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
