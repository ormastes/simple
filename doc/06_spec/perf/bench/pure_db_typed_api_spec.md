# Pure Db Typed Api Specification

> Tests covering Direct Typed API Benchmarks, W7: put() 200 rows (direct API, no SQL parse), W8: get() point lookup by PK (hash index), W9: scan_all() full table scan, W10: SQL point SELECT with PRIMARY KEY, W11: delete_by_key().

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Typed Api Specification

## Scenarios

### Direct Typed API Benchmarks

### W7: put() 200 rows (direct API, no SQL parse)

#### inserts 200 rows via put() and measures time

- insert 200 rows via put() without SQL parsing and time it
   - Expected: rows.len() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-TYPED-API
step("insert 200 rows via put() without SQL parsing and time it")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w7 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()

val t0 = bench_now_ns()
var i = 0
while i < 200:
    val row = make_row3(i as i64, "user_" + i.to_text(), (i * 10) as i64)
    db.put("w7", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()
val t1 = bench_now_ns()

print("[W7] put() 200 rows (direct API): " + elapsed_ms(t0, t1).to_text() + " ms")

val rows = db.scan_all("w7").unwrap()
expect(rows.len()).to_be_greater_than(0)
# Real oracle: exact row count after the direct-API bulk insert.
# oracle: 200 rows were put() in the loop.
expect(rows.len()).to_equal(200)
db.close().unwrap()
```

</details>

### W8: get() point lookup by PK (hash index)

#### looks up single row by PK 100 times

- run 100 hash-indexed get() lookups by PK and time them
   - Expected: result != nil is true
   - Expected: db.get("w8", "id", DbValue.Integer(value: 199)).unwrap() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-TYPED-API
step("run 100 hash-indexed get() lookups by PK and time them")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w8 (id INTEGER PRIMARY KEY, name TEXT)").unwrap()
var i = 0
while i < 200:
    val row = make_row2(i as i64, "row_" + i.to_text())
    db.put("w8", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val idx = j * 2
    val result = db.get("w8", "id", DbValue.Integer(value: idx as i64)).unwrap()
    expect(result != nil).to_equal(true)
    j = j + 1
val t1 = bench_now_ns()

print("[W8] get() by PK x100 (hash index): " + elapsed_ms(t0, t1).to_text() + " ms")
# Real oracle: an unprobed id is still retrievable.
# oracle: id 199 exists from the 200-row setup.
expect(db.get("w8", "id", DbValue.Integer(value: 199)).unwrap() != nil).to_equal(true)
db.close().unwrap()
```

</details>

### W9: scan_all() full table scan

#### scans all rows 100 times

- run 100 typed scan_all() calls and time them
   - Expected: db.scan_all("w9").unwrap().len() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-TYPED-API
step("run 100 typed scan_all() calls and time them")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w9 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()
var i = 0
while i < 200:
    val row = make_row3(i as i64, "item_" + i.to_text(), (i * 5) as i64)
    db.put("w9", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 100:
    val rows = db.scan_all("w9").unwrap()
    expect(rows.len()).to_be_greater_than(0)
    j = j + 1
val t1 = bench_now_ns()

print("[W9] scan_all() x100 (typed): " + elapsed_ms(t0, t1).to_text() + " ms")
# Real oracle: exact table size.
# oracle: 200 rows were put() in setup.
expect(db.scan_all("w9").unwrap().len()).to_equal(200)
db.close().unwrap()
```

</details>

### W10: SQL point SELECT with PRIMARY KEY

#### compares SQL SELECT vs get() on PK column

- time 100 SQL point SELECTs vs 100 get() calls on the PK
   - Expected: result != nil is true
   - Expected: db.query("SELECT id FROM w10 WHERE id = 199", []).unwrap().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-TYPED-API
step("time 100 SQL point SELECTs vs 100 get() calls on the PK")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w10 (id INTEGER PRIMARY KEY, name TEXT)").unwrap()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w10 (id, name) VALUES (" + i.to_text() + ", 'user_" + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0_sql = bench_now_ns()
var j = 0
while j < 100:
    val idx = j * 2
    val rs = db.query("SELECT id, name FROM w10 WHERE id = " + idx.to_text(), []).unwrap()
    expect(rs.len()).to_be_greater_than(0)
    j = j + 1
val t1_sql = bench_now_ns()

val t0_api = bench_now_ns()
var k = 0
while k < 100:
    val idx2 = k * 2
    val result = db.get("w10", "id", DbValue.Integer(value: idx2 as i64)).unwrap()
    expect(result != nil).to_equal(true)
    k = k + 1
val t1_api = bench_now_ns()

val sql_ms = elapsed_ms(t0_sql, t1_sql)
val api_ms = elapsed_ms(t0_api, t1_api)
print("[W10] SQL SELECT x100: " + sql_ms.to_text() + " ms")
print("[W10] get() API x100: " + api_ms.to_text() + " ms")
print("[W10] Speedup: " + (sql_ms / (api_ms + 1)).to_text() + "x")
# Real oracle: both paths agree on a hit outside the timed probes.
# oracle: id 199 exists; SQL path returns exactly one row.
expect(db.query("SELECT id FROM w10 WHERE id = 199", []).unwrap().len()).to_equal(1)
db.close().unwrap()
```

</details>

### W11: delete_by_key()

#### deletes rows by key 50 times

- delete 50 rows by key and time it
   - Expected: remaining.len() equals `150`
   - Expected: db.get("w11", "id", DbValue.Integer(value: 0)).unwrap() == nil is true
   - Expected: db.get("w11", "id", DbValue.Integer(value: 50)).unwrap() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-TYPED-API
step("delete 50 rows by key and time it")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w11 (id INTEGER PRIMARY KEY, name TEXT)").unwrap()
var i = 0
while i < 200:
    val row = make_row2(i as i64, "del_" + i.to_text())
    db.put("w11", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var j = 0
while j < 50:
    db.delete_by_key("w11", "id", DbValue.Integer(value: j as i64)).unwrap()
    j = j + 1
val t1 = bench_now_ns()

print("[W11] delete_by_key() x50: " + elapsed_ms(t0, t1).to_text() + " ms")

val remaining = db.scan_all("w11").unwrap()
# oracle: 200 inserted - 50 deleted = 150 rows remain.
expect(remaining.len()).to_equal(150)
# Real oracle: the deleted key is gone, survivors are not.
# oracle: id 0 was deleted, id 50 was not.
expect(db.get("w11", "id", DbValue.Integer(value: 0)).unwrap() == nil).to_equal(true)
expect(db.get("w11", "id", DbValue.Integer(value: 50)).unwrap() != nil).to_equal(true)
db.close().unwrap()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/bench/pure_db_typed_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Direct Typed API Benchmarks, W7: put() 200 rows (direct API, no SQL parse), W8: get() point lookup by PK (hash index), W9: scan_all() full table scan, W10: SQL point SELECT with PRIMARY KEY, W11: delete_by_key().
- Direct Typed API Benchmarks
- W7: put() 200 rows (direct API, no SQL parse)
- W8: get() point lookup by PK (hash index)
- W9: scan_all() full table scan
- W10: SQL point SELECT with PRIMARY KEY
- W11: delete_by_key()

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-DB-TYPED-API`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `667d725787ef79dd9f03a9be718bb04bd46c676fcc1693395bcee5aab6d3c0ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `667d725787ef79dd9f03a9be718bb04bd46c676fcc1693395bcee5aab6d3c0ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `667d725787ef79dd9f03a9be718bb04bd46c676fcc1693395bcee5aab6d3c0ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/perf/bench/pure_db_typed_api_spec.spl
mirror: doc/06_spec/perf/bench/pure_db_typed_api_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/bench/pure_db_typed_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/bench/pure_db_typed_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/bench/pure_db_typed_api_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/bench/pure_db_typed_api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/bench/pure_db_typed_api_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts 200 rows via put() and measures time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/bench/pure_db_typed_api_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'looks up single row by PK 100 times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/bench/pure_db_typed_api_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans all rows 100 times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
