# Pure Db Sql Extended Specification

> 1. file delete

<!-- sdn-diagram:id=pure_db_sql_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_db_sql_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_db_sql_extended_spec -> std
pure_db_sql_extended_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_db_sql_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Sql Extended Specification

## Scenarios

### PureDatabase extended SQL

#### persists rows and FTS metadata then rebuilds BM25 search after reopen

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql

5. db exec sql
   - Expected: warm.len() equals `1`
   - Expected: warm[0].row.values[0].to_text() equals `1`

6. db close

7. var reopened = PureDatabase open
   - Expected: rows.len() equals `2`
   - Expected: rebuilt.len() equals `1`
   - Expected: rebuilt[0].row.values[0].to_text() equals `1`

8. reopened close

9. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_pure_db_fts_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE docs_reopen (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO docs_reopen (id, body) VALUES (1, 'alpha beta beta')").unwrap()
db.exec_sql("INSERT INTO docs_reopen (id, body) VALUES (2, 'gamma delta')").unwrap()

val warm = db.fts5_search("docs_reopen", ["body"], "beta", 5).unwrap()
expect(warm.len()).to_equal(1)
expect(warm[0].row.values[0].to_text()).to_equal("1")
db.close().unwrap()

val disk_text = file_read(path)
expect(disk_text.contains("table|docs_reopen|id,body")).to_be(true)
expect(disk_text.contains("fts|docs_reopen|body")).to_be(true)
expect(disk_text.contains("row|docs_reopen|I:1")).to_be(true)
expect(disk_text.contains("T:alpha beta beta")).to_be(true)
var reopened = PureDatabase.open(path).unwrap()
val rows = reopened.query("SELECT * FROM docs_reopen", []).unwrap()
expect(rows.len()).to_equal(2)
val rebuilt = reopened.fts5_search("docs_reopen", ["body"], "beta", 5).unwrap()
expect(rebuilt.len()).to_equal(1)
expect(rebuilt[0].row.values[0].to_text()).to_equal("1")
reopened.close().unwrap()
file_delete(path)
```

</details>

#### invalidates rebuilt FTS search after post-reopen writes

1. file delete

2. var db = PureDatabase open

3. db exec sql

4. db exec sql

5. db fts5 search

6. db close

7. var reopened = PureDatabase open
   - Expected: cold.len() equals `0`

8. reopened exec sql
   - Expected: after_insert.len() equals `1`
   - Expected: after_insert[0].row.values[0].to_text() equals `2`

9. reopened exec sql
   - Expected: after_update.len() equals `1`
   - Expected: after_update[0].row.values[0].to_text() equals `1`

10. reopened close

11. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_pure_db_fts_update_" + getpid().to_text() + "_" + time_now_unix_micros().to_text() + ".sdb"
file_delete(path)

var db = PureDatabase.open(path).unwrap()
db.exec_sql("CREATE TABLE docs_reopen_update (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO docs_reopen_update (id, body) VALUES (1, 'alpha seed')").unwrap()
db.fts5_search("docs_reopen_update", ["body"], "omega", 5).unwrap()
db.close().unwrap()

var reopened = PureDatabase.open(path).unwrap()
val cold = reopened.fts5_search("docs_reopen_update", ["body"], "omega", 5).unwrap()
expect(cold.len()).to_equal(0)
reopened.exec_sql("INSERT INTO docs_reopen_update (id, body) VALUES (2, 'omega inserted')").unwrap()
val after_insert = reopened.fts5_search("docs_reopen_update", ["body"], "omega", 5).unwrap()
expect(after_insert.len()).to_equal(1)
expect(after_insert[0].row.values[0].to_text()).to_equal("2")
reopened.exec_sql("UPDATE docs_reopen_update SET body = 'alpha updated' WHERE id = 1").unwrap()
val after_update = reopened.fts5_search("docs_reopen_update", ["body"], "updated", 5).unwrap()
expect(after_update.len()).to_equal(1)
expect(after_update[0].row.values[0].to_text()).to_equal("1")
reopened.close().unwrap()
file_delete(path)
```

</details>

#### supports ORDER BY DESC

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql

5. db exec sql
   - Expected: rows.len() equals `3`
   - Expected: rows[0].values[0].to_text() equals `3`
   - Expected: rows[1].values[0].to_text() equals `2`
   - Expected: rows[2].values[0].to_text() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE ob_desc (id INTEGER, name TEXT)").unwrap()
db.exec_sql("INSERT INTO ob_desc (id, name) VALUES (3, 'C')").unwrap()
db.exec_sql("INSERT INTO ob_desc (id, name) VALUES (1, 'A')").unwrap()
db.exec_sql("INSERT INTO ob_desc (id, name) VALUES (2, 'B')").unwrap()
val rows = db.query("SELECT * FROM ob_desc ORDER BY id DESC", []).unwrap()
expect(rows.len()).to_equal(3)
expect(rows[0].values[0].to_text()).to_equal("3")
expect(rows[1].values[0].to_text()).to_equal("2")
expect(rows[2].values[0].to_text()).to_equal("1")
```

</details>

#### supports BETWEEN

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql

5. db exec sql

6. db exec sql

7. db exec sql
   - Expected: rows.len() equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE btw (id INTEGER, name TEXT)").unwrap()
db.exec_sql("INSERT INTO btw (id, name) VALUES (1, 'A')").unwrap()
db.exec_sql("INSERT INTO btw (id, name) VALUES (2, 'B')").unwrap()
db.exec_sql("INSERT INTO btw (id, name) VALUES (3, 'C')").unwrap()
db.exec_sql("INSERT INTO btw (id, name) VALUES (4, 'D')").unwrap()
db.exec_sql("INSERT INTO btw (id, name) VALUES (5, 'E')").unwrap()
val rows = db.query("SELECT * FROM btw WHERE id BETWEEN 2 AND 4", []).unwrap()
expect(rows.len()).to_equal(3)
```

</details>

#### supports IN list

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql

5. db exec sql

6. db exec sql
   - Expected: rows.len() equals `2`
   - Expected: rows[0].values[0].to_text() equals `1`
   - Expected: rows[1].values[0].to_text() equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE inl (id INTEGER, name TEXT)").unwrap()
db.exec_sql("INSERT INTO inl (id, name) VALUES (1, 'A')").unwrap()
db.exec_sql("INSERT INTO inl (id, name) VALUES (2, 'B')").unwrap()
db.exec_sql("INSERT INTO inl (id, name) VALUES (3, 'C')").unwrap()
db.exec_sql("INSERT INTO inl (id, name) VALUES (4, 'D')").unwrap()
val rows = db.query("SELECT * FROM inl WHERE id IN (1, 3)", []).unwrap()
expect(rows.len()).to_equal(2)
expect(rows[0].values[0].to_text()).to_equal("1")
expect(rows[1].values[0].to_text()).to_equal("3")
```

</details>

#### supports LEFT JOIN

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql

5. db exec sql

6. db exec sql
   - Expected: rows.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE lj_users (uid INTEGER, name TEXT)").unwrap()
db.exec_sql("CREATE TABLE lj_orders (oid INTEGER, user_id INTEGER, item TEXT)").unwrap()
db.exec_sql("INSERT INTO lj_users (uid, name) VALUES (1, 'Alice')").unwrap()
db.exec_sql("INSERT INTO lj_users (uid, name) VALUES (2, 'Bob')").unwrap()
db.exec_sql("INSERT INTO lj_orders (oid, user_id, item) VALUES (10, 1, 'book')").unwrap()
val rows = db.query("SELECT * FROM lj_users LEFT JOIN lj_orders ON uid = user_id", []).unwrap()
expect(rows.len()).to_equal(2)
expect(rows[1].values[2].is_null()).to_be(true)
```

</details>

#### supports SUM aggregate

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql

5. db exec sql
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `60`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE sm (id INTEGER, val INTEGER)").unwrap()
db.exec_sql("INSERT INTO sm (id, val) VALUES (1, 10)").unwrap()
db.exec_sql("INSERT INTO sm (id, val) VALUES (2, 20)").unwrap()
db.exec_sql("INSERT INTO sm (id, val) VALUES (3, 30)").unwrap()
val rows = db.query("SELECT SUM(val) FROM sm", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("60")
```

</details>

#### supports GROUP BY with COUNT

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql

5. db exec sql
   - Expected: rows.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE gc (id INTEGER, category TEXT)").unwrap()
db.exec_sql("INSERT INTO gc (id, category) VALUES (1, 'fruit')").unwrap()
db.exec_sql("INSERT INTO gc (id, category) VALUES (2, 'fruit')").unwrap()
db.exec_sql("INSERT INTO gc (id, category) VALUES (3, 'veggie')").unwrap()
val rows = db.query("SELECT category, COUNT(*) FROM gc GROUP BY category", []).unwrap()
expect(rows.len()).to_equal(2)
```

</details>

#### supports SQLite-style MATCH search in WHERE

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE docs_match (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO docs_match (id, body) VALUES (1, 'alpha beta beta')").unwrap()
db.exec_sql("INSERT INTO docs_match (id, body) VALUES (2, 'gamma delta')").unwrap()
val rows = db.query("SELECT * FROM docs_match WHERE body MATCH 'beta'", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("1")
```

</details>

#### supports fts_match function in WHERE

1. var db = r unwrap

2. db exec sql

3. db exec sql

4. db exec sql
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE docs_fts_fn (id INTEGER, body TEXT)").unwrap()
db.exec_sql("INSERT INTO docs_fts_fn (id, body) VALUES (1, 'trace trace hardware')").unwrap()
db.exec_sql("INSERT INTO docs_fts_fn (id, body) VALUES (2, 'external access')").unwrap()
val rows = db.query("SELECT * FROM docs_fts_fn WHERE fts_match(body, 'trace')", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PureDatabase extended SQL

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
