# Sql Repository Specification

> 1. var db = Database memory

<!-- sdn-diagram:id=sql_repository_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_repository_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_repository_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_repository_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Repository Specification

## Scenarios

### Repository

#### create_table

#### creates the table in the database

1. var db = Database memory
2. var repo = Repository new
   - Expected: db.table_exists("repo_users") is true
   - Expected: "create_table should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
val result = repo.create_table()
if val Ok(_) = result:
    expect(db.table_exists("repo_users")).to_equal(true)
else:
    expect("create_table should succeed").to_equal("")
```

</details>

#### is idempotent - can be called twice

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: db.table_exists("repo_users") is true
   - Expected: "second create_table should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val result = repo.create_table()
if val Ok(_) = result:
    expect(db.table_exists("repo_users")).to_equal(true)
else:
    expect("second create_table should succeed").to_equal("")
```

</details>

#### insert

#### inserts a single entity and returns row id

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: "insert should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val result = repo.insert(RepoUser(name: "Alice", age: 30))
if val Ok(id) = result:
    expect(id).to_be_greater_than(0)
else:
    expect("insert should succeed").to_equal("")
```

</details>

#### inserts multiple entities with incrementing ids

1. var db = Database memory
2. var repo = Repository new
3. repo create table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val id1 = repo.insert(RepoUser(name: "Alice", age: 30))?
val id2 = repo.insert(RepoUser(name: "Bob", age: 25))?
expect(id2).to_be_greater_than(id1)
```

</details>

#### find_by_id

#### finds an existing entity by id

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: user.name equals `Alice`
   - Expected: user.age equals `30`
   - Expected: "find_by_id should return user" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val id = repo.insert(RepoUser(name: "Alice", age: 30))?
val result = repo.find_by_id(id)?
if val Some(user) = result:
    expect(user.name).to_equal("Alice")
    expect(user.age).to_equal(30)
else:
    expect("find_by_id should return user").to_equal("")
```

</details>

#### returns nil for non-existent id

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val result = repo.find_by_id(999)?
expect(result.?).to_equal(false)
```

</details>

#### find_all

#### returns all entities

1. var db = Database memory
2. var repo = Repository new
3. repo create table
4. repo insert
5. repo insert
6. repo insert
   - Expected: users.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
repo.insert(RepoUser(name: "Alice", age: 30))?
repo.insert(RepoUser(name: "Bob", age: 25))?
repo.insert(RepoUser(name: "Charlie", age: 35))?
val users = repo.find_all()?
expect(users.len()).to_equal(3)
```

</details>

#### returns empty list for empty table

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: users.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val users = repo.find_all()?
expect(users.len()).to_equal(0)
```

</details>

#### update

#### updates an existing entity

1. var db = Database memory
2. var repo = Repository new
3. repo create table
4. repo update
   - Expected: user.name equals `Alice Updated`
   - Expected: user.age equals `31`
   - Expected: "updated user should be found" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val id = repo.insert(RepoUser(name: "Alice", age: 30))?
repo.update(id, RepoUser(name: "Alice Updated", age: 31))?
val updated = repo.find_by_id(id)?
if val Some(user) = updated:
    expect(user.name).to_equal("Alice Updated")
    expect(user.age).to_equal(31)
else:
    expect("updated user should be found").to_equal("")
```

</details>

#### delete_by_id

#### deletes an existing entity

1. var db = Database memory
2. var repo = Repository new
3. repo create table
4. repo delete by id
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val id = repo.insert(RepoUser(name: "Alice", age: 30))?
repo.delete_by_id(id)?
val result = repo.find_by_id(id)?
expect(result.?).to_equal(false)
```

</details>

#### returns 0 for non-existent id

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: deleted equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val deleted = repo.delete_by_id(999)?
expect(deleted).to_equal(0)
```

</details>

#### count

#### counts all entities

1. var db = Database memory
2. var repo = Repository new
3. repo create table
4. repo insert
5. repo insert
   - Expected: n equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
repo.insert(RepoUser(name: "Alice", age: 30))?
repo.insert(RepoUser(name: "Bob", age: 25))?
val n = repo.count()?
expect(n).to_equal(2)
```

</details>

#### returns 0 for empty table

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: n equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val n = repo.count()?
expect(n).to_equal(0)
```

</details>

#### insert_batch

#### inserts multiple entities in a batch

1. var db = Database memory
2. var repo = Repository new
3. repo create table
4. RepoUser
5. RepoUser
6. RepoUser
   - Expected: count equals `3`
   - Expected: total equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val entities = [
    RepoUser(name: "Alice", age: 30),
    RepoUser(name: "Bob", age: 25),
    RepoUser(name: "Charlie", age: 35)
]
val count = repo.insert_batch(entities)?
expect(count).to_equal(3)
val total = repo.count()?
expect(total).to_equal(3)
```

</details>

#### returns 0 for empty batch

1. var db = Database memory
2. var repo = Repository new
3. repo create table
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
repo.create_table()?
val count = repo.insert_batch([])?
expect(count).to_equal(0)
```

</details>

#### select

#### returns a SelectQuery for the table

1. var db = Database memory
2. var repo = Repository new


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
val codec = RepoUserCodec()
var repo = Repository.new(db, codec)
val q = repo.select()
val result = q.build()
val sql = result.0
expect(sql).to_contain("repo_users")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/sql/sql_repository_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Repository

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
