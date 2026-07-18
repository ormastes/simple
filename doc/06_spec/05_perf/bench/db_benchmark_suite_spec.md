# Db Benchmark Suite Specification

> 1. var db = PureDatabase memory deferred

<!-- sdn-diagram:id=db_benchmark_suite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_benchmark_suite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_benchmark_suite_spec -> std
db_benchmark_suite_spec -> nogc_sync_mut
db_benchmark_suite_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_benchmark_suite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db exec sql
4. db exec sql
5. db checkpoint
6. db put
7. db checkpoint
8. print
9. print
10. print
   - Expected: true is true
11. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
   - Expected: r.? is true
5. print
6. print
7. print
8. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
    expect(r.?).to_equal(true)
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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
5. print
6. print
7. print
8. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
5. print
6. print
7. print
8. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db sql = PureDatabase memory deferred
2. db sql exec sql
3. var db api = PureDatabase memory deferred
4. db api exec sql
5. db sql exec sql
6. db api put
7. db sql checkpoint
8. db api checkpoint
9. db sql exec sql
10. db api delete by key
11. print
12. print
13. print
14. db sql close
15. db api close


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
5. db put
6. print
   - Expected: true is true
7. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
