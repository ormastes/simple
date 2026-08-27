# Db Benchmark Suite Specification

> Tests covering Phase 8: Head-to-Head Benchmark Suite, W1: Bulk INSERT 200 — SQL vs Direct API, W2: Point SELECT — SQL vs get() (hash index), W3: Range Scan — SQL vs scan_range() (RowBitmap), W4: Full Scan — SQL vs scan_all(), W5: Delete — SQL vs delete_by_key(), W6: Mixed OLTP (80% read, 20% write).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Benchmark Suite Specification

## Scenarios

### Phase 8: Head-to-Head Benchmark Suite

### W1: Bulk INSERT 200 — SQL vs Direct API

#### compares SQL INSERT vs put() for 200 rows

- compares SQL INSERT vs put() for 200 rows
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compares SQL INSERT vs put() for 200 rows")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w1_sql (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()
db.exec_sql("CREATE TABLE w1_api (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()

val t0_sql = bench_now_ns()
var i = 0
while i < 200:
    db.exec_sql("INSERT INTO w1_sql (id, name, score) VALUES (" + i.to_text() + ", 'user_" + i.to_text() + "', " + (i * 10).to_text() + ")").unwrap()
    i = i + 1
db.checkpoint().unwrap()
val t1_sql = bench_now_ns()

val t0_api = bench_now_ns()
var j = 0
while j < 200:
    val row = make_row3(j as i64, "user_" + j.to_text(), (j * 10) as i64)
    db.put("w1_api", row).unwrap()
    j = j + 1
db.checkpoint().unwrap()
val t1_api = bench_now_ns()

print("[W1-SQL] INSERT 200: " + elapsed_ms(t0_sql, t1_sql).to_text() + " ms")
print("[W1-API] put() 200:  " + elapsed_ms(t0_api, t1_api).to_text() + " ms")
print("[W1] Speedup: " + (elapsed_ms(t0_sql, t1_sql) / (elapsed_ms(t0_api, t1_api) + 1)).to_text() + "x")
expect(true).to_equal(true)
db.close().unwrap()
```

</details>

### W2: Point SELECT — SQL vs get() (hash index)

#### compares SQL PK lookup vs direct API get()

- compares SQL PK lookup vs direct API get()
   - Expected: r != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compares SQL PK lookup vs direct API get()")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w2 (id INTEGER PRIMARY KEY, name TEXT)").unwrap()
var i = 0
while i < 200:
    val row = make_row2(i as i64, "row_" + i.to_text())
    db.put("w2", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0_sql = bench_now_ns()
var j = 0
while j < 100:
    val idx = j * 2
    val rs = db.query("SELECT id, name FROM w2 WHERE id = " + idx.to_text(), []).unwrap()
    j = j + 1
val t1_sql = bench_now_ns()

val t0_api = bench_now_ns()
var k = 0
while k < 100:
    val idx2 = k * 2
    val r = db.get("w2", "id", DbValue.Integer(value: idx2 as i64)).unwrap()
    expect(r != nil).to_equal(true)
    k = k + 1
val t1_api = bench_now_ns()

val sql_us = elapsed_us(t0_sql, t1_sql)
val api_us = elapsed_us(t0_api, t1_api)
print("[W2-SQL] SELECT x100: " + elapsed_ms(t0_sql, t1_sql).to_text() + " ms (" + sql_us.to_text() + " us)")
print("[W2-API] get() x100:  " + elapsed_ms(t0_api, t1_api).to_text() + " ms (" + api_us.to_text() + " us)")
print("[W2] Speedup: " + (sql_us / (api_us + 1)).to_text() + "x")
db.close().unwrap()
```

</details>

### W3: Range Scan — SQL vs scan_range() (RowBitmap)

#### compares SQL range vs bitmap-accelerated scan_range()

- compares SQL range vs bitmap-accelerated scan_range()


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compares SQL range vs bitmap-accelerated scan_range()")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w3 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()
var i = 0
while i < 200:
    val row = make_row3(i as i64, "item_" + i.to_text(), (i * 5) as i64)
    db.put("w3", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0_sql = bench_now_ns()
var j = 0
while j < 100:
    val rs = db.query("SELECT id, name FROM w3 WHERE id >= 50 AND id < 150", []).unwrap()
    j = j + 1
val t1_sql = bench_now_ns()

val t0_api = bench_now_ns()
var k = 0
while k < 100:
    val rows = db.scan_range("w3", "id", DbValue.Integer(value: 50), DbValue.Integer(value: 150)).unwrap()
    k = k + 1
val t1_api = bench_now_ns()

val sql_us = elapsed_us(t0_sql, t1_sql)
val api_us = elapsed_us(t0_api, t1_api)
print("[W3-SQL] Range scan x100: " + elapsed_ms(t0_sql, t1_sql).to_text() + " ms (" + sql_us.to_text() + " us)")
print("[W3-API] scan_range x100: " + elapsed_ms(t0_api, t1_api).to_text() + " ms (" + api_us.to_text() + " us)")
print("[W3] Speedup: " + (sql_us / (api_us + 1)).to_text() + "x")
db.close().unwrap()
```

</details>

### W4: Full Scan — SQL vs scan_all()

#### compares SQL SELECT * vs typed scan_all()

- compares SQL SELECT * vs typed scan_all()


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compares SQL SELECT * vs typed scan_all()")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w4 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)").unwrap()
var i = 0
while i < 200:
    val row = make_row3(i as i64, "scan_" + i.to_text(), (i * 3) as i64)
    db.put("w4", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0_sql = bench_now_ns()
var j = 0
while j < 100:
    val rs = db.query("SELECT id, name, score FROM w4", []).unwrap()
    j = j + 1
val t1_sql = bench_now_ns()

val t0_api = bench_now_ns()
var k = 0
while k < 100:
    val rows = db.scan_all("w4").unwrap()
    k = k + 1
val t1_api = bench_now_ns()

val sql_us = elapsed_us(t0_sql, t1_sql)
val api_us = elapsed_us(t0_api, t1_api)
print("[W4-SQL] SELECT * x100: " + elapsed_ms(t0_sql, t1_sql).to_text() + " ms (" + sql_us.to_text() + " us)")
print("[W4-API] scan_all x100: " + elapsed_ms(t0_api, t1_api).to_text() + " ms (" + api_us.to_text() + " us)")
print("[W4] Speedup: " + (sql_us / (api_us + 1)).to_text() + "x")
db.close().unwrap()
```

</details>

### W5: Delete — SQL vs delete_by_key()

#### compares SQL DELETE vs direct delete_by_key()

- compares SQL DELETE vs direct delete_by_key()


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compares SQL DELETE vs direct delete_by_key()")
var db_sql = PureDatabase.memory_deferred().unwrap()
db_sql.exec_sql("CREATE TABLE w5s (id INTEGER PRIMARY KEY, name TEXT)").unwrap()
var db_api = PureDatabase.memory_deferred().unwrap()
db_api.exec_sql("CREATE TABLE w5a (id INTEGER PRIMARY KEY, name TEXT)").unwrap()
var i = 0
while i < 200:
    db_sql.exec_sql("INSERT INTO w5s (id, name) VALUES (" + i.to_text() + ", 'del_" + i.to_text() + "')").unwrap()
    val row = make_row2(i as i64, "del_" + i.to_text())
    db_api.put("w5a", row).unwrap()
    i = i + 1
db_sql.checkpoint().unwrap()
db_api.checkpoint().unwrap()

val t0_sql = bench_now_ns()
var j = 0
while j < 50:
    db_sql.exec_sql("DELETE FROM w5s WHERE id = " + j.to_text()).unwrap()
    j = j + 1
val t1_sql = bench_now_ns()

val t0_api = bench_now_ns()
var k = 0
while k < 50:
    db_api.delete_by_key("w5a", "id", DbValue.Integer(value: k as i64)).unwrap()
    k = k + 1
val t1_api = bench_now_ns()

val sql_us = elapsed_us(t0_sql, t1_sql)
val api_us = elapsed_us(t0_api, t1_api)
print("[W5-SQL] DELETE x50: " + elapsed_ms(t0_sql, t1_sql).to_text() + " ms (" + sql_us.to_text() + " us)")
print("[W5-API] delete_by_key x50: " + elapsed_ms(t0_api, t1_api).to_text() + " ms (" + api_us.to_text() + " us)")
print("[W5] Speedup: " + (sql_us / (api_us + 1)).to_text() + "x")
db_sql.close().unwrap()
db_api.close().unwrap()
```

</details>

### W6: Mixed OLTP (80% read, 20% write)

#### measures mixed workload with typed API

- measures mixed workload with typed API
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("measures mixed workload with typed API")
var db = PureDatabase.memory_deferred().unwrap()
db.exec_sql("CREATE TABLE w6 (id INTEGER PRIMARY KEY, name TEXT, counter INTEGER)").unwrap()
var i = 0
while i < 200:
    val row = make_row3(i as i64, "oltp_" + i.to_text(), 0)
    db.put("w6", row).unwrap()
    i = i + 1
db.checkpoint().unwrap()

val t0 = bench_now_ns()
var op = 0
while op < 500:
    val mod5 = op - ((op / 5) * 5)
    if mod5 == 0:
        val row = make_row3((200 + op) as i64, "new_" + op.to_text(), (op * 7) as i64)
        db.put("w6", row).unwrap()
    else:
        val idx = op * 2
        val mod_idx = idx - ((idx / 200) * 200)
        val r = db.get("w6", "id", DbValue.Integer(value: mod_idx as i64)).unwrap()
    op = op + 1
val t1 = bench_now_ns()

print("[W6] Mixed OLTP 500 ops (80R/20W): " + elapsed_ms(t0, t1).to_text() + " ms (" + elapsed_us(t0, t1).to_text() + " us)")
expect(true).to_equal(true)
db.close().unwrap()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/db_benchmark_suite_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Phase 8: Head-to-Head Benchmark Suite, W1: Bulk INSERT 200 — SQL vs Direct API, W2: Point SELECT — SQL vs get() (hash index), W3: Range Scan — SQL vs scan_range() (RowBitmap), W4: Full Scan — SQL vs scan_all(), W5: Delete — SQL vs delete_by_key(), W6: Mixed OLTP (80% read, 20% write).
- Phase 8: Head-to-Head Benchmark Suite
- W1: Bulk INSERT 200 — SQL vs Direct API
- W2: Point SELECT — SQL vs get() (hash index)
- W3: Range Scan — SQL vs scan_range() (RowBitmap)
- W4: Full Scan — SQL vs scan_all()
- W5: Delete — SQL vs delete_by_key()
- W6: Mixed OLTP (80% read, 20% write)

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c68232a60cba5b69d39be29476916d27d96535b12928ab1ba5c6f88761d03ebc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c68232a60cba5b69d39be29476916d27d96535b12928ab1ba5c6f88761d03ebc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c68232a60cba5b69d39be29476916d27d96535b12928ab1ba5c6f88761d03ebc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/bench/db_benchmark_suite_spec.spl
mirror: doc/06_spec/05_perf/bench/db_benchmark_suite_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/bench/db_benchmark_suite_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/bench/db_benchmark_suite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/bench/db_benchmark_suite_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares SQL INSERT vs put() for 200 rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/bench/db_benchmark_suite_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares SQL PK lookup vs direct API get()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/bench/db_benchmark_suite_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares SQL range vs bitmap-accelerated scan_range()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
