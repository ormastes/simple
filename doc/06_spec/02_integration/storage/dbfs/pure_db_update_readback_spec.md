# Pure Db Update Readback Specification

> Tests covering PureDatabase UPDATE then read-back.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Update Readback Specification

## Scenarios

### PureDatabase UPDATE then read-back

#### reflects an UPDATE through the primary-key fast path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reflects an UPDATE through the primary-key fast path
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `777`
   - Expected: other.len() equals `1`
   - Expected: other[0].values[0].to_text() equals `20`
   - Expected: stale.len() equals `0`
   - Expected: all.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reflects an UPDATE through the primary-key fast path")
val path = _tmp_path("pk")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE t (id INTEGER PRIMARY KEY, n INTEGER)").unwrap()
db.exec_sql("INSERT INTO t (id, n) VALUES (1, 10)").unwrap()
db.exec_sql("INSERT INTO t (id, n) VALUES (2, 20)").unwrap()
db.exec_sql("UPDATE t SET n = 777 WHERE id = 1").unwrap()
val rows = db.query("SELECT n FROM t WHERE id = 1", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("777")
# the untouched row must keep its own value
val other = db.query("SELECT n FROM t WHERE id = 2", []).unwrap()
expect(other.len()).to_equal(1)
expect(other[0].values[0].to_text()).to_equal("20")
# the old value must be gone entirely, not merely shadowed
val stale = db.query("SELECT n FROM t WHERE n = 10", []).unwrap()
expect(stale.len()).to_equal(0)
# row count is unchanged by an UPDATE
val all = db.query("SELECT n FROM t", []).unwrap()
expect(all.len()).to_equal(2)
db.close().unwrap()
file_delete(path)
```

</details>

#### reflects an UPDATE through the general non-primary-key path

- reflects an UPDATE through the general non-primary-key path
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `555`
   - Expected: stale.len() equals `0`
   - Expected: all.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reflects an UPDATE through the general non-primary-key path")
val path = _tmp_path("gen")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE t (id INTEGER, n INTEGER)").unwrap()
db.exec_sql("INSERT INTO t (id, n) VALUES (1, 10)").unwrap()
db.exec_sql("INSERT INTO t (id, n) VALUES (2, 20)").unwrap()
db.exec_sql("UPDATE t SET n = 555 WHERE n = 10").unwrap()
val rows = db.query("SELECT n FROM t WHERE id = 1", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("555")
val stale = db.query("SELECT n FROM t WHERE n = 10", []).unwrap()
expect(stale.len()).to_equal(0)
val all = db.query("SELECT n FROM t", []).unwrap()
expect(all.len()).to_equal(2)
db.close().unwrap()
file_delete(path)
```

</details>

#### keeps an UPDATE visible after reopening the database

- keeps an UPDATE visible after reopening the database
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps an UPDATE visible after reopening the database")
val path = _tmp_path("persist")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE t (id INTEGER PRIMARY KEY, n INTEGER)").unwrap()
db.exec_sql("INSERT INTO t (id, n) VALUES (1, 10)").unwrap()
db.exec_sql("UPDATE t SET n = 999 WHERE id = 1").unwrap()
db.close().unwrap()
var db2 = PureDatabase.open(path).unwrap()
val rows = db2.query("SELECT n FROM t WHERE id = 1", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("999")
db2.close().unwrap()
file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/pure_db_update_readback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PureDatabase UPDATE then read-back.
- PureDatabase UPDATE then read-back

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `e0817579c00e695873348ce59bc95134a605d71038904063591607a26e6feeec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0817579c00e695873348ce59bc95134a605d71038904063591607a26e6feeec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0817579c00e695873348ce59bc95134a605d71038904063591607a26e6feeec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/storage/dbfs/pure_db_update_readback_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/pure_db_update_readback_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/pure_db_update_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/pure_db_update_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/pure_db_update_readback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/dbfs/pure_db_update_readback_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects an UPDATE through the primary-key fast path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/pure_db_update_readback_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects an UPDATE through the general non-primary-key path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/pure_db_update_readback_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an UPDATE visible after reopening the database' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
