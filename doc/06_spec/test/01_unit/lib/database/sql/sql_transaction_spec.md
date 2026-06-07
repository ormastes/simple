# SQL Transaction Specification

> Tests for Transaction: begin/commit persistence, begin/rollback reversion, savepoint/rollback_to nested transactions, and error behavior after commit/rollback.

<!-- sdn-diagram:id=sql_transaction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_transaction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_transaction_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_transaction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SQL Transaction Specification

Tests for Transaction: begin/commit persistence, begin/rollback reversion, savepoint/rollback_to nested transactions, and error behavior after commit/rollback.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-005 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/database/sql/sql_transaction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for Transaction: begin/commit persistence, begin/rollback reversion,
savepoint/rollback_to nested transactions, and error behavior after
commit/rollback.

## Scenarios

### Transaction

#### commit

#### persists data after commit

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx execute
5. tx commit
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx1 (id INTEGER, val TEXT)", [])?

var tx = db.begin()?
tx.execute("INSERT INTO tx1 VALUES (1, 'committed')")?
tx.commit()?

# Data should persist after commit
val rows = db.query("SELECT val FROM tx1 WHERE id = 1", [])?
expect(rows.len()).to_equal(1)
```

</details>

#### persists multiple inserts after commit

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx execute
5. tx execute
6. tx execute
7. tx commit
   - Expected: rows.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx2 (id INTEGER)", [])?

var tx = db.begin()?
tx.execute("INSERT INTO tx2 VALUES (1)")?
tx.execute("INSERT INTO tx2 VALUES (2)")?
tx.execute("INSERT INTO tx2 VALUES (3)")?
tx.commit()?

val rows = db.query("SELECT id FROM tx2", [])?
expect(rows.len()).to_equal(3)
```

</details>

#### rollback

#### reverts data after rollback

1. var db = Database memory
2. db exec
3. db exec
4. var tx = db begin
5. tx execute
6. tx rollback
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx3 (id INTEGER, val TEXT)", [])?

# Insert before transaction
db.exec("INSERT INTO tx3 VALUES (1, 'before')", [])?

# Start transaction, insert, then rollback
var tx = db.begin()?
tx.execute("INSERT INTO tx3 VALUES (2, 'rolled_back')")?
tx.rollback()?

# Only the pre-transaction row should remain
val rows = db.query("SELECT id FROM tx3", [])?
expect(rows.len()).to_equal(1)
```

</details>

#### reverts updates after rollback

1. var db = Database memory
2. db exec
3. db exec
4. var tx = db begin
5. tx execute
6. tx rollback
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx4 (id INTEGER, val TEXT)", [])?
db.exec("INSERT INTO tx4 VALUES (1, 'original')", [])?

var tx = db.begin()?
tx.execute("UPDATE tx4 SET val = 'changed' WHERE id = 1")?
tx.rollback()?

# Value should be unchanged
val rows = db.query("SELECT val FROM tx4 WHERE id = 1", [])?
expect(rows.len()).to_equal(1)
```

</details>

#### savepoint

#### rolls back to savepoint without ending transaction

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx execute
5. tx savepoint
6. tx execute
7. tx rollback to
8. tx execute
9. tx commit
   - Expected: rows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx5 (id INTEGER, val TEXT)", [])?

var tx = db.begin()?

# Insert first row
tx.execute("INSERT INTO tx5 VALUES (1, 'keep')")?

# Create savepoint, insert second row, then rollback to savepoint
tx.savepoint("sp1")?
tx.execute("INSERT INTO tx5 VALUES (2, 'discard')")?
tx.rollback_to("sp1")?

# Insert third row after rollback
tx.execute("INSERT INTO tx5 VALUES (3, 'also_keep')")?
tx.commit()?

# Should have rows 1 and 3 but not 2
val rows = db.query("SELECT id FROM tx5 ORDER BY id", [])?
expect(rows.len()).to_equal(2)
```

</details>

#### releases savepoint on success

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx savepoint
5. tx execute
6. tx release savepoint
7. tx commit
   - Expected: rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx6 (id INTEGER)", [])?

var tx = db.begin()?
tx.savepoint("sp_release")?
tx.execute("INSERT INTO tx6 VALUES (1)")?
tx.release_savepoint("sp_release")?
tx.commit()?

val rows = db.query("SELECT id FROM tx6", [])?
expect(rows.len()).to_equal(1)
```

</details>

#### query within transaction

#### reads inserted data within transaction

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx execute
   - Expected: rows.len() equals `1`
5. tx commit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx7 (id INTEGER, val TEXT)", [])?

var tx = db.begin()?
tx.execute("INSERT INTO tx7 VALUES (1, 'inside_tx')")?

val rows = tx.query("SELECT val FROM tx7 WHERE id = 1")?
expect(rows.len()).to_equal(1)

tx.commit()?
```

</details>

#### error after completion

#### returns error on commit after commit

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx execute
5. tx commit
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx8 (id INTEGER)", [])?

var tx = db.begin()?
tx.execute("INSERT INTO tx8 VALUES (1)")?
tx.commit()?

val result = tx.commit()
expect(result.is_err()).to_equal(true)
```

</details>

#### returns error on rollback after commit

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx commit
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx9 (id INTEGER)", [])?

var tx = db.begin()?
tx.commit()?

val result = tx.rollback()
expect(result.is_err()).to_equal(true)
```

</details>

#### returns error on execute after rollback

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx rollback
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx10 (id INTEGER)", [])?

var tx = db.begin()?
tx.rollback()?

val result = tx.execute("INSERT INTO tx10 VALUES (1)")
expect(result.is_err()).to_equal(true)
```

</details>

#### returns error on query after rollback

1. var db = Database memory
2. db exec
3. var tx = db begin
4. tx rollback
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
db.exec("CREATE TABLE tx11 (id INTEGER)", [])?

var tx = db.begin()?
tx.rollback()?

val result = tx.query("SELECT * FROM tx11")
expect(result.is_err()).to_equal(true)
```

</details>

#### is_active

#### is active after begin

1. var db = Database memory
2. var tx = db begin
   - Expected: tx.is_active() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var tx = db.begin()?
expect(tx.is_active()).to_equal(true)
```

</details>

#### is not active after commit

1. var db = Database memory
2. var tx = db begin
3. tx commit
   - Expected: tx.is_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var tx = db.begin()?
tx.commit()?
expect(tx.is_active()).to_equal(false)
```

</details>

#### is not active after rollback

1. var db = Database memory
2. var tx = db begin
3. tx rollback
   - Expected: tx.is_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = Database.memory()?
var tx = db.begin()?
tx.rollback()?
expect(tx.is_active()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
