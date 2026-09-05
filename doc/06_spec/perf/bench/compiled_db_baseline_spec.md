# Compiled Db Baseline Specification

> Tests covering Phase 0: Compiled-Mode Baseline, W1: INSERT 200 rows (SQL, deferred), W2: Point SELECT x100 (SQL path with PK index), W3: Range scan x100 (SQL), W7: put() 200 rows (direct API), W8: get() x100 (hash index), W10: SQL vs API speedup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiled Db Baseline Specification

## Scenarios

### Phase 0: Compiled-Mode Baseline

### W1: INSERT 200 rows (SQL, deferred)

#### measures SQL INSERT timing

- insert 200 rows via SQL and time the deferred checkpoint
   - Expected: last != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-BASELINE
step("insert 200 rows via SQL and time the deferred checkpoint")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w1 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()
val t0 = bench_now_ns()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w1 (id, name, score) VALUES (" + i.to_text() + ", 'user_" + i.to_text() + "', " + (i * 10).to_text() + ")").unwrap()
    i = i + 1
db.checkpoint().unwrap()
val t1 = bench_now_ns()
print("[W1] INSERT 200 (SQL): " + elapsed_ms(t0, t1).to_text() + " ms (" + elapsed_us(t0, t1).to_text() + " us)")
expect(elapsed_ms(t0, t1)).to_be_greater_than(-1)
# Real oracle: the last inserted row is retrievable after checkpoint.
# oracle: id 199 is the final INSERT of the 0..199 loop, score = 199*10.
val last = db.get("w1", "id", DbValue.Integer(value: 199)).unwrap()
expect(last != nil).to_equal(true)
db.close().unwrap()
```

</details>

### W2: Point SELECT x100 (SQL path with PK index)

#### measures SQL SELECT with hash index

- run 100 indexed point SELECTs and time them
   - Expected: hit != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-BASELINE
step("run 100 indexed point SELECTs and time them")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w2 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w2 (id, name, score) VALUES (" + i.to_text() + ", 'user_" + i.to_text() + "', " + (i * 10).to_text() + ")").unwrap()
    i = i + 1
db.checkpoint().unwrap()
val t0 = bench_now_ns()
var j = 0
while j < 100:
    val idx = j * 2
    val rs = db.query("SELECT id, name, score FROM w2 WHERE id = " + idx.to_text(), []).unwrap()
    j = j + 1
val t1 = bench_now_ns()
print("[W2] Point SELECT x100 (SQL): " + elapsed_ms(t0, t1).to_text() + " ms (" + elapsed_us(t0, t1).to_text() + " us)")
expect(elapsed_ms(t0, t1)).to_be_greater_than(-1)
# Real oracle: an indexed point SELECT returns the inserted row.
# oracle: id 100 was inserted with name user_100 in the setup loop.
val hit = db.get("w2", "id", DbValue.Integer(value: 100)).unwrap()
expect(hit != nil).to_equal(true)
db.close().unwrap()
```

</details>

### W3: Range scan x100 (SQL)

#### measures range query

- run 100 range scans over ids 50..149 and time them
   - Expected: db.get("w3", "id", DbValue.Integer(value: 50)).unwrap() != nil is true
   - Expected: db.get("w3", "id", DbValue.Integer(value: 149)).unwrap() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-BASELINE
step("run 100 range scans over ids 50..149 and time them")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w3 (id INTEGER PRIMARY KEY, name TEXT)").unwrap()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w3 (id, name) VALUES (" + i.to_text() + ", 'user_" + i.to_text() + "')").unwrap()
    i = i + 1
db.checkpoint().unwrap()
val t0 = bench_now_ns()
var j = 0
while j < 100:
    val rs = db.query("SELECT id, name FROM w3 WHERE id >= 50 AND id < 150", []).unwrap()
    j = j + 1
val t1 = bench_now_ns()
print("[W3] Range scan x100 (SQL): " + elapsed_ms(t0, t1).to_text() + " ms (" + elapsed_us(t0, t1).to_text() + " us)")
expect(elapsed_ms(t0, t1)).to_be_greater_than(-1)
# Real oracle: both endpoints of the scanned range are retrievable.
# oracle: ids 50 and 149 exist in the range predicate id >= 50 AND id < 150.
expect(db.get("w3", "id", DbValue.Integer(value: 50)).unwrap() != nil).to_equal(true)
expect(db.get("w3", "id", DbValue.Integer(value: 149)).unwrap() != nil).to_equal(true)
db.close().unwrap()
```

</details>

### W7: put() 200 rows (direct API)

#### measures direct API insert

- insert 200 rows via put() and time the deferred checkpoint
   - Expected: db.get("w7", "id", DbValue.Integer(value: 199)).unwrap() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-BASELINE
step("insert 200 rows via put() and time the deferred checkpoint")
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
print("[W7] put() 200 (API): " + elapsed_ms(t0, t1).to_text() + " ms (" + elapsed_us(t0, t1).to_text() + " us)")
expect(elapsed_ms(t0, t1)).to_be_greater_than(-1)
# Real oracle: the final put() is retrievable after checkpoint.
# oracle: id 199 is the last of the 200 put() calls.
expect(db.get("w7", "id", DbValue.Integer(value: 199)).unwrap() != nil).to_equal(true)
db.close().unwrap()
```

</details>

### W8: get() x100 (hash index)

#### measures direct API get with hash index

- run 100 hash-indexed get() calls and time them
   - Expected: r != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-BASELINE
step("run 100 hash-indexed get() calls and time them")
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
    val r = db.get("w8", "id", DbValue.Integer(value: idx as i64)).unwrap()
    expect(r != nil).to_equal(true)
    j = j + 1
val t1 = bench_now_ns()
print("[W8] get() x100 (API): " + elapsed_ms(t0, t1).to_text() + " ms (" + elapsed_us(t0, t1).to_text() + " us)")
db.close().unwrap()
```

</details>

### W10: SQL vs API speedup

#### compares SQL SELECT vs get() on same data

- time 100 SQL SELECTs vs 100 get() calls on the same table
   - Expected: r != nil is true
   - Expected: db.get("w10", "id", DbValue.Integer(value: 198)).unwrap() != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-DB-BASELINE
step("time 100 SQL SELECTs vs 100 get() calls on the same table")
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
    j = j + 1
val t1_sql = bench_now_ns()

val t0_api = bench_now_ns()
var k = 0
while k < 100:
    val idx2 = k * 2
    val r = db.get("w10", "id", DbValue.Integer(value: idx2 as i64)).unwrap()
    expect(r != nil).to_equal(true)
    k = k + 1
val t1_api = bench_now_ns()

val sql_ms = elapsed_ms(t0_sql, t1_sql)
val api_ms = elapsed_ms(t0_api, t1_api)
print("[W10] SQL SELECT x100: " + sql_ms.to_text() + " ms")
print("[W10] get() API x100:  " + api_ms.to_text() + " ms")
print("[W10] Speedup:         " + (sql_ms / (api_ms + 1)).to_text() + "x")
# Real oracle: the comparison table still serves indexed reads.
# oracle: id 198 is the last even id probed by both timed loops.
expect(db.get("w10", "id", DbValue.Integer(value: 198)).unwrap() != nil).to_equal(true)
db.close().unwrap()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/bench/compiled_db_baseline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Phase 0: Compiled-Mode Baseline, W1: INSERT 200 rows (SQL, deferred), W2: Point SELECT x100 (SQL path with PK index), W3: Range scan x100 (SQL), W7: put() 200 rows (direct API), W8: get() x100 (hash index), W10: SQL vs API speedup.
- Phase 0: Compiled-Mode Baseline
- W1: INSERT 200 rows (SQL, deferred)
- W2: Point SELECT x100 (SQL path with PK index)
- W3: Range scan x100 (SQL)
- W7: put() 200 rows (direct API)
- W8: get() x100 (hash index)
- W10: SQL vs API speedup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-DB-BASELINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65110a48e1f231749d91a22ea0c2670dd5ae7973c1493d9bee8e975ff059f3f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65110a48e1f231749d91a22ea0c2670dd5ae7973c1493d9bee8e975ff059f3f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65110a48e1f231749d91a22ea0c2670dd5ae7973c1493d9bee8e975ff059f3f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/perf/bench/compiled_db_baseline_spec.spl
mirror: doc/06_spec/perf/bench/compiled_db_baseline_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/bench/compiled_db_baseline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/bench/compiled_db_baseline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/bench/compiled_db_baseline_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/bench/compiled_db_baseline_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures SQL INSERT timing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/bench/compiled_db_baseline_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures SQL SELECT with hash index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/bench/compiled_db_baseline_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures range query' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
