# Pure Db Typed Api Specification

> 1. var db = PureDatabase memory deferred

<!-- sdn-diagram:id=pure_db_typed_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_db_typed_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_db_typed_api_spec -> std
pure_db_typed_api_spec -> nogc_sync_mut
pure_db_typed_api_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_db_typed_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
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

print("[W7] put() 200 rows (direct API): " + elapsed_ms(t0, t1).to_text() + " ms")

val rows = db.scan_all("w7").unwrap()
expect(rows.len()).to_be_greater_than(0)
db.close().unwrap()
```

</details>

### W8: get() point lookup by PK (hash index)

#### looks up single row by PK 100 times

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
   - Expected: result.? is true
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
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
    val result = db.get("w8", "id", DbValue.Integer(value: idx as i64)).unwrap()
    expect(result.?).to_equal(true)
    j = j + 1
val t1 = bench_now_ns()

print("[W8] get() by PK x100 (hash index): " + elapsed_ms(t0, t1).to_text() + " ms")
db.close().unwrap()
```

</details>

### W9: scan_all() full table scan

#### scans all rows 100 times

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
5. print
6. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db exec sql
4. db checkpoint
   - Expected: result.? is true
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
    expect(result.?).to_equal(true)
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

1. var db = PureDatabase memory deferred
2. db exec sql
3. db put
4. db checkpoint
5. db delete by key
6. print
   - Expected: remaining.len() equals `150`
7. db close


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
