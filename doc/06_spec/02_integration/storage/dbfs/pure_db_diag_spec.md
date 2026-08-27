# Pure Db Diag Specification

> Tests covering DIAG real column, DIAG rollback update, DIAG rollback update no index read, DIAG null.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Diag Specification

## Scenarios

### DIAG real column

#### reports counts for REAL comparisons

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports counts for REAL comparisons
   - Expected: all.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports counts for REAL comparisons")
val path = _tmp_path("real")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE pr (id INTEGER, amount REAL)").unwrap()
db.exec_sql("INSERT INTO pr (id, amount) VALUES (1, 2.5)").unwrap()
db.exec_sql("INSERT INTO pr (id, amount) VALUES (2, 30.0)").unwrap()
val all = db.query("SELECT * FROM pr", []).unwrap()
print("DIAG real all=" + all.len().to_text())
if all.len() > 0:
    print("DIAG real v0=" + all[0].values[1].to_text())
val gt = db.query("SELECT * FROM pr WHERE amount > 10", []).unwrap()
print("DIAG real gt10=" + gt.len().to_text())
val gtf = db.query("SELECT * FROM pr WHERE amount > 10.0", []).unwrap()
print("DIAG real gt10f=" + gtf.len().to_text())
val lt = db.query("SELECT * FROM pr WHERE amount < 10", []).unwrap()
print("DIAG real lt10=" + lt.len().to_text())
val btw = db.query("SELECT * FROM pr WHERE amount > 1 AND amount < 100", []).unwrap()
print("DIAG real range=" + btw.len().to_text())
expect(all.len()).to_equal(2)
db.close().unwrap()
file_delete(path)
```

</details>

### DIAG rollback update

#### reports row state around a rolled-back UPDATE

- reports row state around a rolled-back UPDATE
   - Expected: pre.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports row state around a rolled-back UPDATE")
val path = _tmp_path("rbu")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE ru (id INTEGER, n INTEGER)").unwrap()
db.exec_sql("INSERT INTO ru (id, n) VALUES (1, 10)").unwrap()
db.exec_sql("INSERT INTO ru (id, n) VALUES (2, 20)").unwrap()
val pre = db.query("SELECT * FROM ru", []).unwrap()
print("DIAG rbu pre_all=" + pre.len().to_text())
db.exec_sql("BEGIN").unwrap()
db.exec_sql("UPDATE ru SET n = 999 WHERE id = 1").unwrap()
val mid = db.query("SELECT * FROM ru", []).unwrap()
print("DIAG rbu mid_all=" + mid.len().to_text())
db.exec_sql("ROLLBACK").unwrap()
val post = db.query("SELECT * FROM ru", []).unwrap()
print("DIAG rbu post_all=" + post.len().to_text())
var i = 0
while i < post.len():
    print("DIAG rbu row ncols=" + post[i].columns.len().to_text() + " nvals=" + post[i].values.len().to_text())
    var j = 0
    while j < post[i].values.len():
        print("DIAG rbu   cell[" + j.to_text() + "]=" + post[i].values[j].to_text())
        j = j + 1
    i = i + 1
val one = db.query("SELECT * FROM ru WHERE id = 1", []).unwrap()
print("DIAG rbu post_id1=" + one.len().to_text())
expect(pre.len()).to_equal(2)
db.close().unwrap()
file_delete(path)
```

</details>

### DIAG rollback update no index read

#### reports rolled-back UPDATE without a prior warm read

- reports rolled-back UPDATE without a prior warm read
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports rolled-back UPDATE without a prior warm read")
val path = _tmp_path("rbu2")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE rv (id INTEGER, n INTEGER)").unwrap()
db.exec_sql("INSERT INTO rv (id, n) VALUES (1, 10)").unwrap()
db.exec_sql("BEGIN").unwrap()
db.exec_sql("UPDATE rv SET n = 999 WHERE id = 1").unwrap()
db.exec_sql("ROLLBACK").unwrap()
val post = db.query("SELECT * FROM rv", []).unwrap()
print("DIAG rbu2 post_all=" + post.len().to_text())
var i = 0
while i < post.len():
    print("DIAG rbu2 row ncols=" + post[i].columns.len().to_text() + " nvals=" + post[i].values.len().to_text())
    var j = 0
    while j < post[i].values.len():
        print("DIAG rbu2   cell[" + j.to_text() + "]=" + post[i].values[j].to_text())
        j = j + 1
    i = i + 1
# Control: a table never touched by a transaction must keep both columns.
db.exec_sql("CREATE TABLE ctl (id INTEGER, n INTEGER)").unwrap()
db.exec_sql("INSERT INTO ctl (id, n) VALUES (7, 70)").unwrap()
val ctl = db.query("SELECT * FROM ctl", []).unwrap()
if ctl.len() > 0:
    print("DIAG ctl nvals=" + ctl[0].values.len().to_text())
expect(1).to_equal(1)
db.close().unwrap()
file_delete(path)
```

</details>

### DIAG null

#### reports NULL comparison counts

- reports NULL comparison counts
   - Expected: isn.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports NULL comparison counts")
val path = _tmp_path("null")
file_delete(path)
var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE nu (id INTEGER, name TEXT)").unwrap()
db.exec_sql("INSERT INTO nu (id, name) VALUES (1, NULL)").unwrap()
db.exec_sql("INSERT INTO nu (id, name) VALUES (2, 'bob')").unwrap()
val eqnull = db.query("SELECT * FROM nu WHERE name = NULL", []).unwrap()
print("DIAG null eq_null=" + eqnull.len().to_text())
val ne = db.query("SELECT * FROM nu WHERE name != 'alice'", []).unwrap()
print("DIAG null ne_alice=" + ne.len().to_text())
val notq = db.query("SELECT * FROM nu WHERE NOT (name = 'bob')", []).unwrap()
print("DIAG null not_eq_bob=" + notq.len().to_text())
val isn = db.query("SELECT * FROM nu WHERE name IS NULL", []).unwrap()
print("DIAG null is_null=" + isn.len().to_text())
expect(isn.len()).to_equal(1)
db.close().unwrap()
file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/pure_db_diag_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DIAG real column, DIAG rollback update, DIAG rollback update no index read, DIAG null.
- DIAG real column
- DIAG rollback update
- DIAG rollback update no index read
- DIAG null

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `db0de8a3c8e5f31408279bd0f05369628d56087b70b395953813a97cdf9ad396`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db0de8a3c8e5f31408279bd0f05369628d56087b70b395953813a97cdf9ad396`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db0de8a3c8e5f31408279bd0f05369628d56087b70b395953813a97cdf9ad396`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/storage/dbfs/pure_db_diag_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/pure_db_diag_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/pure_db_diag_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/pure_db_diag_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/pure_db_diag_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/dbfs/pure_db_diag_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports counts for REAL comparisons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/pure_db_diag_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports row state around a rolled-back UPDATE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/pure_db_diag_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports rolled-back UPDATE without a prior warm read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
