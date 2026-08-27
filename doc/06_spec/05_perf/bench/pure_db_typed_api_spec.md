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

- inserts 200 rows via put() and measures time


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("inserts 200 rows via put() and measures time")
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
db.close().unwrap()
```

</details>

### W8: get() point lookup by PK (hash index)

#### looks up single row by PK 100 times

- looks up single row by PK 100 times
   - Expected: result != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("looks up single row by PK 100 times")
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
db.close().unwrap()
```

</details>

### W9: scan_all() full table scan

#### scans all rows 100 times

- scans all rows 100 times


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("scans all rows 100 times")
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
db.close().unwrap()
```

</details>

### W10: SQL point SELECT with PRIMARY KEY

#### compares SQL SELECT vs get() on PK column

- compares SQL SELECT vs get() on PK column
   - Expected: result != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compares SQL SELECT vs get() on PK column")
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
db.close().unwrap()
```

</details>

### W11: delete_by_key()

#### deletes rows by key 50 times

- deletes rows by key 50 times
   - Expected: remaining.len() equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("deletes rows by key 50 times")
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
expect(remaining.len()).to_equal(150)
db.close().unwrap()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/pure_db_typed_api_spec.spl` |
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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5384c7edf778248348e894ce01adc4d3f28fd23d25212f575f29d59636124ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5384c7edf778248348e894ce01adc4d3f28fd23d25212f575f29d59636124ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5384c7edf778248348e894ce01adc4d3f28fd23d25212f575f29d59636124ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/05_perf/bench/pure_db_typed_api_spec.spl
mirror: doc/06_spec/05_perf/bench/pure_db_typed_api_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/bench/pure_db_typed_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/bench/pure_db_typed_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/bench/pure_db_typed_api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/bench/pure_db_typed_api_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts 200 rows via put() and measures time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/bench/pure_db_typed_api_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'looks up single row by PK 100 times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/bench/pure_db_typed_api_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans all rows 100 times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
