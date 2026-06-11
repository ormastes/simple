# Sql Migration Specification

> 1. var db = Database memory

<!-- sdn-diagram:id=sql_migration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_migration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_migration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_migration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Migration Specification

## Scenarios

### MigrationRunner

#### add migrations

#### starts with empty migration list

1. var db = Database memory
   - Expected: pending.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val runner = MigrationRunner.new(db)
val pending = runner.pending()?
expect(pending.len()).to_equal(0)
```

</details>

#### adds a migration

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE users
   - Expected: pending.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_create_users",
    description: "Create users table",
    up_sql: "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)",
    down_sql: "DROP TABLE users"
))
val pending = runner.pending()?
expect(pending.len()).to_equal(1)
```

</details>

#### adds multiple migrations

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE users
   - Expected: pending.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_create_users",
    description: "Create users table",
    up_sql: "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)",
    down_sql: "DROP TABLE users"
))
runner = runner.add(Migration(
    id: "002_add_email",
    description: "Add email column",
    up_sql: "ALTER TABLE users ADD COLUMN email TEXT",
    down_sql: "ALTER TABLE users DROP COLUMN email"
))
val pending = runner.pending()?
expect(pending.len()).to_equal(2)
```

</details>

#### run

#### applies pending migrations

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE users
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_create_users",
    description: "Create users table",
    up_sql: "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT NOT NULL)",
    down_sql: "DROP TABLE users"
))
val count = runner.run()?
expect(count).to_equal(1)
```

</details>

#### returns 0 when no pending migrations

1. var db = Database memory
2. var runner = MigrationRunner new
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
val count = runner.run()?
expect(count).to_equal(0)
```

</details>

#### creates the table defined in the migration

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE items
4. runner run
   - Expected: db.table_exists("items") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_create_items",
    description: "Create items table",
    up_sql: "CREATE TABLE items (id INTEGER PRIMARY KEY, name TEXT NOT NULL)",
    down_sql: "DROP TABLE items"
))
runner.run()?
expect(db.table_exists("items")).to_equal(true)
```

</details>

#### applied

#### returns applied migration IDs after run

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE users
4. up sql: "CREATE TABLE posts
5. runner run
   - Expected: applied_ids.len() equals `2`
   - Expected: applied_ids[0] equals `001_create_users`
   - Expected: applied_ids[1] equals `002_create_posts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_create_users",
    description: "Create users table",
    up_sql: "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)",
    down_sql: "DROP TABLE users"
))
runner = runner.add(Migration(
    id: "002_create_posts",
    description: "Create posts table",
    up_sql: "CREATE TABLE posts (id INTEGER PRIMARY KEY, title TEXT)",
    down_sql: "DROP TABLE posts"
))
runner.run()?
val applied_ids = runner.applied()?
expect(applied_ids.len()).to_equal(2)
expect(applied_ids[0]).to_equal("001_create_users")
expect(applied_ids[1]).to_equal("002_create_posts")
```

</details>

#### returns empty list before any run

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE t
   - Expected: applied_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_test",
    description: "test",
    up_sql: "CREATE TABLE t (id INTEGER)",
    down_sql: "DROP TABLE t"
))
val applied_ids = runner.applied()?
expect(applied_ids.len()).to_equal(0)
```

</details>

#### pending

#### returns all migrations before run

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE a
4. up sql: "CREATE TABLE b
   - Expected: pending.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_a",
    description: "First",
    up_sql: "CREATE TABLE a (id INTEGER)",
    down_sql: "DROP TABLE a"
))
runner = runner.add(Migration(
    id: "002_b",
    description: "Second",
    up_sql: "CREATE TABLE b (id INTEGER)",
    down_sql: "DROP TABLE b"
))
val pending = runner.pending()?
expect(pending.len()).to_equal(2)
```

</details>

#### returns empty after all migrations applied

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE x
4. runner run
   - Expected: pending.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_x",
    description: "X",
    up_sql: "CREATE TABLE x (id INTEGER)",
    down_sql: "DROP TABLE x"
))
runner.run()?
val pending = runner.pending()?
expect(pending.len()).to_equal(0)
```

</details>

#### returns only unapplied migrations

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE first t
4. runner run
5. up sql: "CREATE TABLE second t
   - Expected: pending.len() equals `1`
   - Expected: pending[0].id equals `002_second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_first",
    description: "First",
    up_sql: "CREATE TABLE first_t (id INTEGER)",
    down_sql: "DROP TABLE first_t"
))
runner.run()?
runner = runner.add(Migration(
    id: "002_second",
    description: "Second",
    up_sql: "CREATE TABLE second_t (id INTEGER)",
    down_sql: "DROP TABLE second_t"
))
val pending = runner.pending()?
expect(pending.len()).to_equal(1)
expect(pending[0].id).to_equal("002_second")
```

</details>

#### idempotency

#### run is idempotent - second run applies nothing

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE idem t
   - Expected: first_count equals `1`
   - Expected: second_count equals `0`
   - Expected: applied_ids.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_idem",
    description: "Idempotent test",
    up_sql: "CREATE TABLE idem_t (id INTEGER PRIMARY KEY, val TEXT)",
    down_sql: "DROP TABLE idem_t"
))
val first_count = runner.run()?
expect(first_count).to_equal(1)
val second_count = runner.run()?
expect(second_count).to_equal(0)
val applied_ids = runner.applied()?
expect(applied_ids.len()).to_equal(1)
```

</details>

#### rollback

#### rolls back the last migration

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE rb t
4. runner run
   - Expected: db.table_exists("rb_t") is true
   - Expected: rolled equals `1`
   - Expected: applied_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_rb",
    description: "Rollback test",
    up_sql: "CREATE TABLE rb_t (id INTEGER PRIMARY KEY)",
    down_sql: "DROP TABLE rb_t"
))
runner.run()?
expect(db.table_exists("rb_t")).to_equal(true)
val rolled = runner.rollback(1)?
expect(rolled).to_equal(1)
val applied_ids = runner.applied()?
expect(applied_ids.len()).to_equal(0)
```

</details>

#### rolls back multiple migrations

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE rb2a
4. up sql: "CREATE TABLE rb2b
5. runner run
   - Expected: rolled equals `2`
   - Expected: applied_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_rb2a",
    description: "First",
    up_sql: "CREATE TABLE rb2a (id INTEGER)",
    down_sql: "DROP TABLE rb2a"
))
runner = runner.add(Migration(
    id: "002_rb2b",
    description: "Second",
    up_sql: "CREATE TABLE rb2b (id INTEGER)",
    down_sql: "DROP TABLE rb2b"
))
runner.run()?
val rolled = runner.rollback(2)?
expect(rolled).to_equal(2)
val applied_ids = runner.applied()?
expect(applied_ids.len()).to_equal(0)
```

</details>

#### rolls back only up to the requested count

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE partial a
4. up sql: "CREATE TABLE partial b
5. runner run
   - Expected: rolled equals `1`
   - Expected: applied_ids.len() equals `1`
   - Expected: applied_ids[0] equals `001_partial_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_partial_a",
    description: "A",
    up_sql: "CREATE TABLE partial_a (id INTEGER)",
    down_sql: "DROP TABLE partial_a"
))
runner = runner.add(Migration(
    id: "002_partial_b",
    description: "B",
    up_sql: "CREATE TABLE partial_b (id INTEGER)",
    down_sql: "DROP TABLE partial_b"
))
runner.run()?
val rolled = runner.rollback(1)?
expect(rolled).to_equal(1)
val applied_ids = runner.applied()?
expect(applied_ids.len()).to_equal(1)
expect(applied_ids[0]).to_equal("001_partial_a")
```

</details>

#### re-applies after rollback

1. var db = Database memory
2. var runner = MigrationRunner new
3. up sql: "CREATE TABLE reapply t
4. runner run
5. runner rollback
   - Expected: count equals `1`
   - Expected: applied_ids.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var runner = MigrationRunner.new(db)
runner = runner.add(Migration(
    id: "001_reapply",
    description: "Reapply test",
    up_sql: "CREATE TABLE reapply_t (id INTEGER PRIMARY KEY)",
    down_sql: "DROP TABLE reapply_t"
))
runner.run()?
runner.rollback(1)?
val count = runner.run()?
expect(count).to_equal(1)
val applied_ids = runner.applied()?
expect(applied_ids.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/sql/sql_migration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MigrationRunner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
