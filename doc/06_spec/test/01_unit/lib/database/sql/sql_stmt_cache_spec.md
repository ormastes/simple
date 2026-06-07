# SQL Statement Cache Specification

> Tests for StatementCache: cache hit/miss counting, LRU eviction when capacity is exceeded, clear, and hit_rate calculation.

<!-- sdn-diagram:id=sql_stmt_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_stmt_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_stmt_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_stmt_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Statement Cache Specification

Tests for StatementCache: cache hit/miss counting, LRU eviction when capacity is exceeded, clear, and hit_rate calculation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-006 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/database/sql/sql_stmt_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for StatementCache: cache hit/miss counting, LRU eviction when
capacity is exceeded, clear, and hit_rate calculation.

## Scenarios

### StatementCache

#### construction

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StatementCache.new(10)
expect(cache.size()).to_equal(0)
```

</details>

#### starts with zero hits and misses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StatementCache.new(10)
expect(cache.hits).to_equal(0)
expect(cache.misses).to_equal(0)
```

</details>

#### hit and miss counting

#### counts cache misses on first access

1. var db = Database memory
2. db exec
3. db query
   - Expected: db.cache.misses equals `1`
   - Expected: db.cache.hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc1 (id INTEGER)", [])?

# Access the database cache through queries
# First query with params triggers cache miss
db.query("SELECT * FROM sc1 WHERE id = ?", [DbValue.Integer(value: 1)])?
expect(db.cache.misses).to_equal(1)
expect(db.cache.hits).to_equal(0)
```

</details>

#### counts cache hits on repeated access

1. var db = Database memory
2. db exec
3. db query
4. db query
   - Expected: db.cache.misses equals `1`
   - Expected: db.cache.hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc2 (id INTEGER)", [])?

# First access = miss, second access = hit
db.query("SELECT * FROM sc2 WHERE id = ?", [DbValue.Integer(value: 1)])?
db.query("SELECT * FROM sc2 WHERE id = ?", [DbValue.Integer(value: 2)])?

expect(db.cache.misses).to_equal(1)
expect(db.cache.hits).to_equal(1)
```

</details>

#### tracks multiple different statements

1. var db = Database memory
2. db exec
3. db query
4. db query
5. db query
6. db query
   - Expected: db.cache.misses equals `2`
   - Expected: db.cache.hits equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc3 (id INTEGER, val TEXT)", [])?

val sql1 = "SELECT * FROM sc3 WHERE id = ?"
val sql2 = "SELECT val FROM sc3 WHERE id = ?"

db.query(sql1, [DbValue.Integer(value: 1)])?  # miss
db.query(sql2, [DbValue.Integer(value: 1)])?  # miss
db.query(sql1, [DbValue.Integer(value: 2)])?  # hit
db.query(sql2, [DbValue.Integer(value: 2)])?  # hit

expect(db.cache.misses).to_equal(2)
expect(db.cache.hits).to_equal(2)
```

</details>

#### LRU eviction

#### evicts oldest entry when capacity exceeded

1. var db = Database memory
2. var cache = StatementCache new
3. db exec
4. cache get or prepare
5. cache get or prepare
   - Expected: cache.size() equals `2`
6. cache get or prepare
   - Expected: cache.size() equals `2`
   - Expected: cache.misses equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
# Create a database with a small cache for testing eviction
# The default cache size is 64, so we test via a direct StatementCache

var cache = StatementCache.new(2)
db.exec("CREATE TABLE sc4 (id INTEGER, a TEXT, b TEXT, c TEXT)", [])?

# Fill the cache with 2 entries
cache.get_or_prepare(db.conn, "SELECT a FROM sc4 WHERE id = ?")?
cache.get_or_prepare(db.conn, "SELECT b FROM sc4 WHERE id = ?")?
expect(cache.size()).to_equal(2)

# Adding a third should evict the first (LRU)
cache.get_or_prepare(db.conn, "SELECT c FROM sc4 WHERE id = ?")?
expect(cache.size()).to_equal(2)

# The third miss happened
expect(cache.misses).to_equal(3)
```

</details>

#### evicts least recently used, not just oldest

1. var db = Database memory
2. db exec
3. var cache = StatementCache new
4. cache get or prepare
5. cache get or prepare
6. cache get or prepare
7. cache get or prepare
   - Expected: cache.size() equals `2`
8. cache get or prepare
   - Expected: cache.hits equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc5 (id INTEGER, a TEXT, b TEXT, c TEXT)", [])?

var cache = StatementCache.new(2)

# Add two entries: A then B
cache.get_or_prepare(db.conn, "SELECT a FROM sc5")?  # miss, order: [A]
cache.get_or_prepare(db.conn, "SELECT b FROM sc5")?  # miss, order: [A, B]

# Access A again (makes A most recent, B is now LRU)
cache.get_or_prepare(db.conn, "SELECT a FROM sc5")?  # hit, order: [B, A]

# Add C — should evict B (LRU), not A
cache.get_or_prepare(db.conn, "SELECT c FROM sc5")?  # miss, order: [A, C]
expect(cache.size()).to_equal(2)

# Access A again — should be a hit (it was NOT evicted)
cache.get_or_prepare(db.conn, "SELECT a FROM sc5")?  # hit
expect(cache.hits).to_equal(2)
```

</details>

#### clear

#### removes all entries

1. var db = Database memory
2. db exec
3. var cache = StatementCache new
4. cache get or prepare
5. cache get or prepare
   - Expected: cache.size() equals `2`
6. cache clear
   - Expected: cache.size() equals `0`
   - Expected: cache.hits equals `0`
   - Expected: cache.misses equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc6 (id INTEGER)", [])?

var cache = StatementCache.new(10)
cache.get_or_prepare(db.conn, "SELECT * FROM sc6")?
cache.get_or_prepare(db.conn, "SELECT id FROM sc6")?
expect(cache.size()).to_equal(2)

cache.clear()
expect(cache.size()).to_equal(0)
expect(cache.hits).to_equal(0)
expect(cache.misses).to_equal(0)
```

</details>

#### invalidate

#### removes a specific entry

1. var db = Database memory
2. db exec
3. var cache = StatementCache new
4. cache get or prepare
5. cache get or prepare
   - Expected: cache.size() equals `2`
6. cache invalidate
   - Expected: cache.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc7 (id INTEGER)", [])?

var cache = StatementCache.new(10)
cache.get_or_prepare(db.conn, "SELECT * FROM sc7")?
cache.get_or_prepare(db.conn, "SELECT id FROM sc7")?
expect(cache.size()).to_equal(2)

cache.invalidate("SELECT * FROM sc7")
expect(cache.size()).to_equal(1)
```

</details>

#### does nothing for non-existent key

1. var db = Database memory
2. var cache = StatementCache new
3. db exec
4. cache get or prepare
5. cache invalidate
   - Expected: cache.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var cache = StatementCache.new(10)
db.exec("CREATE TABLE sc8 (id INTEGER)", [])?
cache.get_or_prepare(db.conn, "SELECT * FROM sc8")?

cache.invalidate("SELECT nonexistent FROM sc8")
expect(cache.size()).to_equal(1)
```

</details>

#### hit_rate

#### returns 0.0 when no accesses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StatementCache.new(10)
expect(cache.hit_rate()).to_equal(0.0)
```

</details>

#### returns correct rate after mixed hits and misses

1. var db = Database memory
2. db exec
3. var cache = StatementCache new
4. cache get or prepare
5. cache get or prepare
6. cache get or prepare
7. cache get or prepare
   - Expected: cache.misses equals `1`
   - Expected: cache.hits equals `3`
   - Expected: cache.hit_rate() equals `0.75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc9 (id INTEGER)", [])?

var cache = StatementCache.new(10)
val sql = "SELECT * FROM sc9 WHERE id = ?"

# 1 miss + 3 hits = 0.75 hit rate
cache.get_or_prepare(db.conn, sql)?  # miss
cache.get_or_prepare(db.conn, sql)?  # hit
cache.get_or_prepare(db.conn, sql)?  # hit
cache.get_or_prepare(db.conn, sql)?  # hit

expect(cache.misses).to_equal(1)
expect(cache.hits).to_equal(3)
# hit_rate = 3/4 = 0.75
expect(cache.hit_rate()).to_equal(0.75)
```

</details>

#### returns 0.0 for all misses

1. var db = Database memory
2. db exec
3. var cache = StatementCache new
4. cache get or prepare
5. cache get or prepare
6. cache get or prepare
   - Expected: cache.hit_rate() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE sc10 (id INTEGER, a TEXT, b TEXT)", [])?

var cache = StatementCache.new(10)
cache.get_or_prepare(db.conn, "SELECT * FROM sc10")?
cache.get_or_prepare(db.conn, "SELECT a FROM sc10")?
cache.get_or_prepare(db.conn, "SELECT b FROM sc10")?

expect(cache.hit_rate()).to_equal(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
