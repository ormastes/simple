# Compiled Db Baseline Specification

> 1. var db = PureDatabase memory deferred

<!-- sdn-diagram:id=compiled_db_baseline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiled_db_baseline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiled_db_baseline_spec -> std
compiled_db_baseline_spec -> nogc_sync_mut
compiled_db_baseline_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiled_db_baseline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db exec sql
4. db checkpoint
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
db.close().unwrap()
```

</details>

### W2: Point SELECT x100 (SQL path with PK index)

#### measures SQL SELECT with hash index

1. var db = PureDatabase memory deferred
2. db exec sql
3. db exec sql
4. db checkpoint
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
db.close().unwrap()
```

</details>

### W3: Range scan x100 (SQL)

#### measures range query

1. var db = PureDatabase memory deferred
2. db exec sql
3. db exec sql
4. db checkpoint
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
db.close().unwrap()
```

</details>

### W7: put() 200 rows (direct API)

#### measures direct API insert

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
db.close().unwrap()
```

</details>

### W8: get() x100 (hash index)

#### measures direct API get with hash index

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
   - Expected: r.? is true
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
    expect(r.?).to_equal(true)
    j = j + 1
val t1 = bench_now_ns()
print("[W8] get() x100 (API): " + elapsed_ms(t0, t1).to_text() + " ms (" + elapsed_us(t0, t1).to_text() + " us)")
db.close().unwrap()
```

</details>

### W10: SQL vs API speedup

#### compares SQL SELECT vs get() on same data

1. var db = PureDatabase memory deferred
2. db exec sql
3. db exec sql
4. db checkpoint
   - Expected: r.? is true
5. print
6. print
7. print
8. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
    expect(r.?).to_equal(true)
    k = k + 1
val t1_api = bench_now_ns()

val sql_ms = elapsed_ms(t0_sql, t1_sql)
val api_ms = elapsed_ms(t0_api, t1_api)
print("[W10] SQL SELECT x100: " + sql_ms.to_text() + " ms")
print("[W10] get() API x100:  " + api_ms.to_text() + " ms")
print("[W10] Speedup:         " + (sql_ms / (api_ms + 1)).to_text() + "x")
db.close().unwrap()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/compiled_db_baseline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
