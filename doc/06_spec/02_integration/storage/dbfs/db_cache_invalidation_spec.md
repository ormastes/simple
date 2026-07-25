# DB Cache Invalidation Specification

> Validates that PureDatabase FTS/BM25 cache invalidation works correctly across all mutation paths: INSERT, UPDATE, DELETE, DROP, and reopen. Each mutation must clear stale FTS index entries so that subsequent searches reflect the current state of the data.

<!-- sdn-diagram:id=db_cache_invalidation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_cache_invalidation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_cache_invalidation_spec -> std
db_cache_invalidation_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_cache_invalidation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DB Cache Invalidation Specification

Validates that PureDatabase FTS/BM25 cache invalidation works correctly across all mutation paths: INSERT, UPDATE, DELETE, DROP, and reopen. Each mutation must clear stale FTS index entries so that subsequent searches reflect the current state of the data.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #db-hardening-optimization |
| Category | Database |
| Difficulty | 2/5 |
| Status | Draft |
| Plan | doc/03_plan/db_hardening_optimization_plan_2026-05-26.md |
| Source | `test/02_integration/storage/dbfs/db_cache_invalidation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that PureDatabase FTS/BM25 cache invalidation works correctly
across all mutation paths: INSERT, UPDATE, DELETE, DROP, and reopen.
Each mutation must clear stale FTS index entries so that subsequent
searches reflect the current state of the data.

## Behavior

- INSERT → FTS search returns the newly inserted document
- UPDATE → FTS search reflects updated content, old content not found
- DELETE → FTS search no longer returns the deleted document
- DROP → FTS search on dropped table returns empty
- Reopen → FTS search returns correct results after DB reopen

## Scenarios

### DB Cache Invalidation (AC-6)

### INSERT invalidation

#### AC-6: INSERT makes document findable via FTS search

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql
   - Expected: results.len() equals `1`
   - Expected: row_id equals `1`

5. db close

6. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_cache_inv_ins_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE inv_ins (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO inv_ins (id, body) VALUES (1, 'alpha bravo charlie')").unwrap()

val results = db.fts5_search("inv_ins", ["body"], "bravo", 5).unwrap()
expect(results.len()).to_equal(1)
val row_id = results[0].row.values[0].to_text()
expect(row_id).to_equal("1")

db.close().unwrap()
file_delete(path)
```

</details>

#### AC-6: second INSERT also findable without manual rebuild

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql
   - Expected: r1.len() equals `1`

5. db exec sql
   - Expected: r2.len() equals `1`
   - Expected: row_id equals `2`

6. db close

7. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_cache_inv_ins2_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE inv_ins2 (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO inv_ins2 (id, body) VALUES (1, 'first document')").unwrap()

val r1 = db.fts5_search("inv_ins2", ["body"], "first", 5).unwrap()
expect(r1.len()).to_equal(1)

db.exec_sql("INSERT INTO inv_ins2 (id, body) VALUES (2, 'second document')").unwrap()

val r2 = db.fts5_search("inv_ins2", ["body"], "second", 5).unwrap()
expect(r2.len()).to_equal(1)
val row_id = r2[0].row.values[0].to_text()
expect(row_id).to_equal("2")

db.close().unwrap()
file_delete(path)
```

</details>

### UPDATE invalidation

#### AC-6: UPDATE reflects new content and removes old content from FTS

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql
   - Expected: before.len() equals `1`

5. db exec sql
   - Expected: old_gone.len() equals `0`
   - Expected: new_found.len() equals `1`

6. db close

7. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_cache_inv_upd_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE inv_upd (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO inv_upd (id, body) VALUES (1, 'original content here')").unwrap()

val before = db.fts5_search("inv_upd", ["body"], "original", 5).unwrap()
expect(before.len()).to_equal(1)

db.exec_sql("UPDATE inv_upd SET body = 'replaced content here' WHERE id = 1").unwrap()

val old_gone = db.fts5_search("inv_upd", ["body"], "original", 5).unwrap()
expect(old_gone.len()).to_equal(0)

val new_found = db.fts5_search("inv_upd", ["body"], "replaced", 5).unwrap()
expect(new_found.len()).to_equal(1)

db.close().unwrap()
file_delete(path)
```

</details>

### DELETE invalidation

#### AC-6: DELETE removes document from FTS search results

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql
   - Expected: before.len() equals `1`

5. db exec sql
   - Expected: after.len() equals `0`

6. db close

7. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_cache_inv_del_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE inv_del (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO inv_del (id, body) VALUES (1, 'ephemeral data point')").unwrap()

val before = db.fts5_search("inv_del", ["body"], "ephemeral", 5).unwrap()
expect(before.len()).to_equal(1)

db.exec_sql("DELETE FROM inv_del WHERE id = 1").unwrap()

val after = db.fts5_search("inv_del", ["body"], "ephemeral", 5).unwrap()
expect(after.len()).to_equal(0)

db.close().unwrap()
file_delete(path)
```

</details>

### DROP invalidation

#### AC-6: DROP table makes FTS search return empty

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql
   - Expected: before.len() equals `1`

5. db exec sql
   - Expected: after.is_err() is true

6. db close

7. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_cache_inv_drop_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE inv_drop (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO inv_drop (id, body) VALUES (1, 'persistent record')").unwrap()

val before = db.fts5_search("inv_drop", ["body"], "persistent", 5).unwrap()
expect(before.len()).to_equal(1)

db.exec_sql("DROP TABLE inv_drop").unwrap()

val after = db.fts5_search("inv_drop", ["body"], "persistent", 5)
expect(after.is_err()).to_equal(true)

db.close().unwrap()
file_delete(path)
```

</details>

### Reopen invalidation

#### AC-6: reopen preserves data and FTS search still returns correct results

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql
   - Expected: warm.len() equals `1`

5. db close

6. var reopened = PureDatabase open
   - Expected: cold.len() equals `1`
   - Expected: row_id equals `1`

7. reopened close

8. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_cache_inv_reopen_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE inv_reopen (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO inv_reopen (id, body) VALUES (1, 'survive reopen cycle')").unwrap()

val warm = db.fts5_search("inv_reopen", ["body"], "survive", 5).unwrap()
expect(warm.len()).to_equal(1)
db.close().unwrap()

var reopened = PureDatabase.open(path).unwrap()
val cold = reopened.fts5_search("inv_reopen", ["body"], "survive", 5).unwrap()
expect(cold.len()).to_equal(1)
val row_id = cold[0].row.values[0].to_text()
expect(row_id).to_equal("1")

reopened.close().unwrap()
file_delete(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/db_hardening_optimization_plan_2026-05-26.md](doc/03_plan/db_hardening_optimization_plan_2026-05-26.md)


</details>
