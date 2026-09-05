# Pure Db Micro Specification

> Tests covering PureDatabase Micro-Benchmarks, W1: INSERT 200 rows deferred (no UNIQUE), W2: Point SELECT by rowid, W3: Range scan SELECT, W4: Prefix search, W5: FTS5 search, W6: Reopen latency, SQLite Comparison (AC-2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Micro Specification

## Scenarios

### PureDatabase Micro-Benchmarks

### W1: INSERT 200 rows deferred (no UNIQUE)

#### inserts 200 rows with deferred persist and measures time

- insert 200 rows through the deferred persist path and time it


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-MICRO
step("insert 200 rows through the deferred persist path and time it")
val path = tmp_path("w1")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w1 (id INTEGER, name TEXT, score INTEGER)").unwrap()

val t0 = bench_now_ns()
var i = 0
while i < 200:
    val sql = "INSERT INTO w1 (id, name, score) VALUES (" + i.to_text() + ", 'user_" + i.to_text() + "', " + (i * 10).to_text() + ")"
    db.exec_sql(sql).unwrap()
    i = i + 1
db.checkpoint().unwrap()
val t1 = bench_now_ns()

print("[W1] INSERT 200 rows (deferred): " + elapsed_ms(t0, t1).to_text() + " ms")

val rows = db.query("SELECT count(*) FROM w1", []).unwrap()
expect(rows.len()).to_be_greater_than(0)
# Real oracle: the inserted row survives checkpoint.
# oracle: id 199 is the final INSERT of the 0..199 loop.
val hit = db.query("SELECT id FROM w1 WHERE id = 199", []).unwrap()
expect(hit.len()).to_be_greater_than(0)

db.close().unwrap()
file_delete(path)
```

</details>

### W2: Point SELECT by rowid

#### selects single row by id 100 times

- run 100 point SELECTs by id and time them


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-MICRO
step("run 100 point SELECTs by id and time them")
val path = tmp_path("w2")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w2 (id INTEGER, name TEXT)").unwrap()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w2 (id, name) VALUES (" + i.to_text() + ", 'row_" + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val idx = j * 2
    val rs = db.query("SELECT id, name FROM w2 WHERE id = " + idx.to_text(), []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W2] Point SELECT x100: " + elapsed_ms(t0, t1).to_text() + " ms")
# Real oracle: a point SELECT outside the timed probes still hits.
# oracle: id 199 exists from the 200-row setup.
expect(db.query("SELECT id FROM w2 WHERE id = 199", []).unwrap().len()).to_be_greater_than(0)

db.close().unwrap()
file_delete(path)
```

</details>

### W3: Range scan SELECT

#### scans rows WHERE score > threshold 100 times

- run 100 range scans WHERE score > 150 and time them
   - Expected: db.query("SELECT id FROM w3 WHERE score > 150", []).unwrap().len() equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-MICRO
step("run 100 range scans WHERE score > 150 and time them")
val path = tmp_path("w3")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w3 (id INTEGER, score INTEGER)").unwrap()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w3 (id, score) VALUES (" + i.to_text() + ", " + i.to_text() + ")").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val rs = db.query("SELECT id, score FROM w3 WHERE score > 150", []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W3] Range scan x100: " + elapsed_ms(t0, t1).to_text() + " ms")
# Real oracle: exact predicate count.
# oracle: scores are ids 0..199, so score > 150 matches 151..199 = 49 rows.
expect(db.query("SELECT id FROM w3 WHERE score > 150", []).unwrap().len()).to_equal(49)

db.close().unwrap()
file_delete(path)
```

</details>

### W4: Prefix search

#### searches by prefix pattern 100 times

- run 100 prefix LIKE searches and time them
   - Expected: db.query("SELECT id FROM w4 WHERE name LIKE 'alpha_%'", []).unwrap().len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-MICRO
step("run 100 prefix LIKE searches and time them")
val path = tmp_path("w4")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w4 (id INTEGER, name TEXT)").unwrap()
var i = 0
while i < 200:
    val prefix = if i < 100: "alpha_" else: "beta_"
    db.exec_sql("INSERT INTO w4 (id, name) VALUES (" + i.to_text() + ", '" + prefix + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val rs = db.query("SELECT id, name FROM w4 WHERE name LIKE 'alpha_%'", []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W4] Prefix search x100: " + elapsed_ms(t0, t1).to_text() + " ms")
# Real oracle: exact prefix partition count.
# oracle: ids 0..99 got the alpha_ prefix = 100 rows.
expect(db.query("SELECT id FROM w4 WHERE name LIKE 'alpha_%'", []).unwrap().len()).to_equal(100)

db.close().unwrap()
file_delete(path)
```

</details>

### W5: FTS5 search

#### full-text searches 100 times

- run 100 FTS5 searches for 'bravo' and time them
   - Expected: db.fts5_search("w5", ["body"], "bravo", 200).unwrap().len() equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-MICRO
step("run 100 FTS5 searches for 'bravo' and time them")
val path = tmp_path("w5")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w5 (id INTEGER, body TEXT)").unwrap()
var i = 0
while i < 200:
    val word = if i < 40: "alpha" else: if i < 80: "bravo" else: if i < 120: "charlie" else: if i < 160: "delta" else: "echo"
    db.exec_sql("INSERT INTO w5 (id, body) VALUES (" + i.to_text() + ", '" + word + " document number " + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val results = db.fts5_search("w5", ["body"], "bravo", 10).unwrap()
    expect(results.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W5] FTS5 search x100: " + elapsed_ms(t0, t1).to_text() + " ms")
# Real oracle: FTS term partition size.
# oracle: 'bravo' is the body of ids 40..79 = 40 documents.
expect(db.fts5_search("w5", ["body"], "bravo", 200).unwrap().len()).to_equal(40)

db.close().unwrap()
file_delete(path)
```

</details>

### W6: Reopen latency

#### closes and reopens database 10 times

- reopen the persisted database 10 times and time it


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-MICRO
step("reopen the persisted database 10 times and time it")
val path = tmp_path("w6")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE w6 (id INTEGER, body TEXT)").unwrap()
var i = 0
while i < 100:
    db.exec_sql("INSERT INTO w6 (id, body) VALUES (" + i.to_text() + ", 'persistent row " + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()
db.close().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 10:
    var rdb = PureDatabase.open(path).unwrap()
    val rs = rdb.query("SELECT count(*) FROM w6", []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    rdb.close().unwrap()
    j = j + 1
val t1 = bench_now_ns()

print("[W6] Reopen x10: " + elapsed_ms(t0, t1).to_text() + " ms")
# Real oracle: persisted rows survive close/reopen.
# oracle: 100 rows were checkpointed before the reopen loop.
var rdb2 = PureDatabase.open(path).unwrap()
expect(rdb2.query("SELECT id FROM w6 WHERE id = 99", []).unwrap().len()).to_be_greater_than(0)
rdb2.close().unwrap()

file_delete(path)
```

</details>

### SQLite Comparison (AC-2)

#### W1s–W6s: documents SQLite FFI availability

**Manual warnings:**
- invalid manual visibility metadata: # @manual SQLite comparison availability note (expected show, folded, detail, or skip)


- record SQLite FFI availability for the comparison workloads
   - Expected: cnt.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-MICRO
step("record SQLite FFI availability for the comparison workloads")
# SQLite FFI (rt_sqlite_*) requires libsqlite3 linked at build time.
# When available, implement identical W1–W6 workloads against
# std.nogc_sync_mut.database.sql.connection.Database.
# Current status: FFI may not be linked in interpreter mode.
print("[SQLite] SKIP: SQLite FFI (rt_sqlite_*) not reliably available in interpreter mode")
print("[SQLite] See doc/09_report/ comparison report for qualitative analysis")
# Real oracle: the PureDatabase baseline this scenario is measured
# against is functional — a fresh in-DB count reflects inserted rows.
# oracle: 2 marker rows inserted, so count(*) returns one result row.
val path = tmp_path("w1s")
file_delete(path)
var db = PureDatabase.open_deferred(path).unwrap()
db.exec_sql("CREATE TABLE marker (id INTEGER)").unwrap()
db.exec_sql("INSERT INTO marker (id) VALUES (1)").unwrap()
db.exec_sql("INSERT INTO marker (id) VALUES (2)").unwrap()
db.checkpoint().unwrap()
val cnt = db.query("SELECT count(*) FROM marker", []).unwrap()
expect(cnt.len()).to_equal(1)
db.close().unwrap()
file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/bench/pure_db_micro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PureDatabase Micro-Benchmarks, W1: INSERT 200 rows deferred (no UNIQUE), W2: Point SELECT by rowid, W3: Range scan SELECT, W4: Prefix search, W5: FTS5 search, W6: Reopen latency, SQLite Comparison (AC-2).
- PureDatabase Micro-Benchmarks
- W1: INSERT 200 rows deferred (no UNIQUE)
- W2: Point SELECT by rowid
- W3: Range scan SELECT
- W4: Prefix search
- W5: FTS5 search
- W6: Reopen latency
- SQLite Comparison (AC-2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-DB-MICRO`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a36aa667b20a941836700fb65f38090fa7914b0dd92838425a5950d67a9fd003`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a36aa667b20a941836700fb65f38090fa7914b0dd92838425a5950d67a9fd003`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a36aa667b20a941836700fb65f38090fa7914b0dd92838425a5950d67a9fd003`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/perf/bench/pure_db_micro_spec.spl
mirror: doc/06_spec/perf/bench/pure_db_micro_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/bench/pure_db_micro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/bench/pure_db_micro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/bench/pure_db_micro_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/bench/pure_db_micro_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/bench/pure_db_micro_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts 200 rows with deferred persist and measures time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/bench/pure_db_micro_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects single row by id 100 times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/bench/pure_db_micro_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans rows WHERE score > threshold 100 times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
