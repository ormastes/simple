# Simple DB Server Tier — Increment 2: Durable Commit

> Increment 1 of the server tier could open a session, run a transaction and answer `OK applied=1` — and then lose the write completely if the process died a moment later, because COMMIT only ever touched memory. This manual covers the increment that fixes that: **a COMMIT is acknowledged only after the store has been written to durable media.**

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple DB Server Tier — Increment 2: Durable Commit

Increment 1 of the server tier could open a session, run a transaction and answer `OK applied=1` — and then lose the write completely if the process died a moment later, because COMMIT only ever touched memory. This manual covers the increment that fixes that: **a COMMIT is acknowledged only after the store has been written to durable media.**

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / Infrastructure |
| Status | In Progress (increment 2 of the server tier) |
| Design | `.spipe/db_durability/state.md` |
| Source | `test/03_system/database/server/db_durability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Increment 1 of the server tier could open a session, run a transaction and
answer `OK applied=1` — and then lose the write completely if the process died
a moment later, because COMMIT only ever touched memory. This manual covers
the increment that fixes that: **a COMMIT is acknowledged only after the store
has been written to durable media.**

The interesting question is not "does the happy path work". It is "what does
the database look like if the machine dies in the middle". So most of this
manual is a crash-point matrix: the process is killed at each step of the
commit pipeline, the database file is then re-read from disk by a brand new
reader, and the value it finds is compared against an absolute expected value.

## The commit pipeline and where we kill it

| Step | What happens |
|------|--------------|
| P1 precheck | every buffered write still matches the row version it observed |
| P2 undo | the pre-image of every touched key is snapshotted |
| P3 apply | the overlay is applied to the in-memory tables |
| P4 persist | `save()` — lock, write `<path>.tmp`, fsync, rename over `<path>` |
| P5 ack | `OK applied=N` goes back to the client |

The **commit point** is the rename in P4. Everything before it is invisible to
a restarted process; everything after it is permanent.

## What a reader may observe

Never a torn mixture. Either every value of the transaction is there, or none
of them is. Two independent mechanisms enforce this: the half-written bytes
only ever exist under the name `<path>.tmp`, which no reader opens; and the
file body carries a crc32 header, so a torn file that somehow did reach
`<path>` is refused outright instead of being parsed into a half-new state.

## The honest gap

A crash after P4 but before P5 leaves the data permanently stored while the
client is told nothing. The client cannot distinguish that from a crash before
P4. A legacy COMMIT without \`commit_id\` is therefore **at-least-once** at the
connection level. A validated \`commit_id\` records a principal-bound durable
receipt, so the same authenticated principal may safely retry after reconnect;
another principal or different transaction content is rejected as a conflict.

## Related Specifications

- `test/03_system/database/server/db_server_tier_spec.spl` — increment 1:
  sessions, capabilities, transaction isolation.
- `std.database.core` / `std.database.atomic` — the store and the locking this
  tier reuses. No second storage or locking engine was written.

## Scenarios

### DB durability — the acknowledged commit is permanent

#### stores a committed row where a brand new reader finds it

- stores a committed row where a brand new reader finds it


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores a committed row where a brand new reader finds it")
val path = "build/dbdur_happy.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
# The oracle is a fresh load, not the server's own memory.
assert_equal(on_disk(path, "u1"), "old")
```

</details>

#### stores an update over an already durable row

- stores an update over an already durable row


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores an update over an already durable row")
val path = "build/dbdur_update.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=new")
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
assert_equal(on_disk(path, "u1"), "new")
```

</details>

#### makes a committed delete permanent too

- makes a committed delete permanent too


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("makes a committed delete permanent too")
val path = "build/dbdur_delete.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")
assert_equal(on_disk(path, "u1"), "old")
server.handle_message("BEGIN session=1")
server.handle_message("DEL session=1 tbl=users id=u1")
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
assert_equal(on_disk(path, "u1"), ABSENT)
```

</details>

#### persists every write of a multi-row transaction or none of them

- persists every write of a multi-row transaction or none of them


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("persists every write of a multi-row transaction or none of them")
val path = "build/dbdur_multi.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=a name=one")
server.handle_message("PUT session=1 tbl=users id=b name=two")
server.handle_message("PUT session=1 tbl=users id=c name=three")
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=3")
assert_equal(on_disk(path, "a"), "one")
assert_equal(on_disk(path, "b"), "two")
assert_equal(on_disk(path, "c"), "three")
```

</details>

#### never writes anything a transaction rolled back

- never writes anything a transaction rolled back


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("never writes anything a transaction rolled back")
val path = "build/dbdur_rollback.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=rolled_back")
assert_equal(server.handle_message("ROLLBACK session=1"), "OK")
assert_equal(on_disk(path, "u1"), "old")
```

</details>

### DB durability — crash-point matrix

#### crash BEFORE persist leaves the old value on disk

- crash BEFORE persist leaves the old value on disk
- kill the process after the overlay is applied, before save()
- a restarted reader sees the OLD value, and no new key leaked


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("crash BEFORE persist leaves the old value on disk")
val path = "build/dbdur_crash_before.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")
assert_equal(on_disk(path, "u1"), "old")

step("kill the process after the overlay is applied, before save()")
var crashed = DbServerCapsule.new_with_durability(
    SdnDatabase.load(path) ?? fresh_store(path),
    alice_policy(),
    durability_crash_at(CRASH_BEFORE_PERSIST)
)
crashed.handle_message("OPEN as=alice credential=alice-secret")
crashed.handle_message("BEGIN session=1")
crashed.handle_message("PUT session=1 tbl=users id=u1 name=new")
val reply = crashed.handle_message("COMMIT session=1")
assert_contains(reply, "code=crashed")

step("a restarted reader sees the OLD value, and no new key leaked")
assert_equal(on_disk(path, "u1"), "old")
```

</details>

#### crash MID persist leaves the old value on disk and never exposes the temp file

- crash MID persist leaves the old value on disk and never exposes the temp file
- kill the process between writing <path>.tmp and renaming it
- the torn bytes exist, but only under the temp name
- the database file itself is intact and still holds the OLD value


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("crash MID persist leaves the old value on disk and never exposes the temp file")
val path = "build/dbdur_crash_mid.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")

step("kill the process between writing <path>.tmp and renaming it")
var crashed = DbServerCapsule.new_with_durability(
    SdnDatabase.load(path) ?? fresh_store(path),
    alice_policy(),
    durability_crash_at(CRASH_MID_PERSIST)
)
crashed.handle_message("OPEN as=alice credential=alice-secret")
crashed.handle_message("BEGIN session=1")
crashed.handle_message("PUT session=1 tbl=users id=u1 name=new")
assert_contains(crashed.handle_message("COMMIT session=1"), "code=crashed")

step("the torn bytes exist, but only under the temp name")
assert_true(temp_path_exists(path))
step("the database file itself is intact and still holds the OLD value")
assert_true(durable_file_loads(path))
assert_equal(on_disk(path, "u1"), "old")
file_delete(path + ".tmp")
```

</details>

#### crash AFTER persist but before the acknowledgement leaves the NEW value on disk

- crash AFTER persist but before the acknowledgement leaves the NEW value on disk
- kill the process after the rename, before OK reaches the client
- the client is never acknowledged
- yet the write IS permanent — this is the at-least-once gap


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("crash AFTER persist but before the acknowledgement leaves the NEW value on disk")
val path = "build/dbdur_crash_after.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")

step("kill the process after the rename, before OK reaches the client")
var crashed = DbServerCapsule.new_with_durability(
    SdnDatabase.load(path) ?? fresh_store(path),
    alice_policy(),
    durability_crash_at(CRASH_AFTER_PERSIST)
)
crashed.handle_message("OPEN as=alice credential=alice-secret")
crashed.handle_message("BEGIN session=1")
crashed.handle_message("PUT session=1 tbl=users id=u1 name=new")
step("the client is never acknowledged")
assert_contains(crashed.handle_message("COMMIT session=1"), "code=crashed")

step("yet the write IS permanent — this is the at-least-once gap")
assert_equal(on_disk(path, "u1"), "new")
```

</details>

#### a recoverable persist failure rolls memory back to the last durable state

- a recoverable persist failure rolls memory back to the last durable state
- save() fails but the process keeps running
- the client is told the commit did NOT happen
- disk still holds the old value
- and the live server's memory agrees with disk — no split brain


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a recoverable persist failure rolls memory back to the last durable state")
val path = "build/dbdur_persist_fail.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")

step("save() fails but the process keeps running")
var failing = DbServerCapsule.new_with_durability(
    SdnDatabase.load(path) ?? fresh_store(path),
    alice_policy(),
    durability_crash_at(CRASH_PERSIST_FAILS)
)
failing.handle_message("OPEN as=alice credential=alice-secret")
failing.handle_message("BEGIN session=1")
failing.handle_message("PUT session=1 tbl=users id=u1 name=new")
val reply = failing.handle_message("COMMIT session=1")
step("the client is told the commit did NOT happen")
assert_contains(reply, "code=durability")

step("disk still holds the old value")
assert_equal(on_disk(path, "u1"), "old")
step("and the live server's memory agrees with disk — no split brain")
failing.handle_message("BEGIN session=1")
assert_equal(
    failing.handle_message("GET session=1 tbl=users id=u1 col=name"),
    "OK value=old"
)
```

</details>

<details>
<summary>Advanced: rolls an insert back out of memory when the persist fails</summary>

#### rolls an insert back out of memory when the persist fails

- rolls an insert back out of memory when the persist fails
- the row that only ever existed in the failed commit is gone


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rolls an insert back out of memory when the persist fails")
val path = "build/dbdur_persist_fail_insert.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")

var failing = DbServerCapsule.new_with_durability(
    SdnDatabase.load(path) ?? fresh_store(path),
    alice_policy(),
    durability_crash_at(CRASH_PERSIST_FAILS)
)
failing.handle_message("OPEN as=alice credential=alice-secret")
failing.handle_message("BEGIN session=1")
failing.handle_message("PUT session=1 tbl=users id=ghost name=phantom")
assert_contains(failing.handle_message("COMMIT session=1"), "code=durability")

step("the row that only ever existed in the failed commit is gone")
failing.handle_message("BEGIN session=1")
assert_contains(
    failing.handle_message("GET session=1 tbl=users id=ghost col=name"),
    "code=not_found"
)
assert_equal(on_disk(path, "ghost"), ABSENT)
```

</details>


</details>

#### refuses a torn database file instead of parsing half of it

- refuses a torn database file instead of parsing half of it
- simulate a torn file reaching <path> despite the rename design
- the crc32 header makes the reader fail closed, not read a mixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a torn database file instead of parsing half of it")
val path = "build/dbdur_torn.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=old")
server.handle_message("COMMIT session=1")
assert_true(durable_file_loads(path))

step("simulate a torn file reaching <path> despite the rename design")
file_write(path, "#sdn-crc32:12345\nusers |id, name, valid|\n    u1, ha")
step("the crc32 header makes the reader fail closed, not read a mixture")
assert_false(durable_file_loads(path))
assert_equal(on_disk(path, "u1"), ABSENT)
scrub(path)
```

</details>

### DB durability — the transaction guarantees are unchanged

#### still refuses a conflicting commit, and persists nothing when it does

- still refuses a conflicting commit, and persists nothing when it does
- session 2 observed a version that session 1 has since moved
- only the winner is on disk


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("still refuses a conflicting commit, and persists nothing when it does")
val path = "build/dbdur_conflict.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=first")
server.handle_message("BEGIN session=2")
server.handle_message("PUT session=2 tbl=users id=u1 name=second")
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
step("session 2 observed a version that session 1 has since moved")
assert_contains(server.handle_message("COMMIT session=2"), "code=conflict")
step("only the winner is on disk")
assert_equal(on_disk(path, "u1"), "first")
```

</details>

#### still hides an uncommitted write from a peer, on disk as well as in memory

- still hides an uncommitted write from a peer, on disk as well as in memory
- the peer sees nothing before COMMIT
- and everything after it


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("still hides an uncommitted write from a peer, on disk as well as in memory")
val path = "build/dbdur_isolation.sdn"
var server = DbServerCapsule.new_with_durability(
    fresh_store(path), alice_policy(), durability_on()
)
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=private")
step("the peer sees nothing before COMMIT")
assert_contains(
    server.handle_message("GET session=2 tbl=users id=u1 col=name"),
    "code=not_found"
)
assert_equal(on_disk(path, "u1"), ABSENT)
step("and everything after it")
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
assert_equal(
    server.handle_message("GET session=2 tbl=users id=u1 col=name"),
    "OK value=private"
)
assert_equal(on_disk(path, "u1"), "private")
```

</details>

### DB durability — the contract is explicit about what it did

#### reports a pathless store as in-memory only rather than as durable

- reports a pathless store as in-memory only rather than as durable
- it committed, and it says plainly that nothing was persisted


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a pathless store as in-memory only rather than as durable")
var db = SdnDatabase.new("")
db.set_table("users", SdnTable.new("users", ["id", "name", "valid"]))
var state: TxnState = begin_txn()
state = txn_record(state, TxnWrite(
    table: "users", key: "u1", kind: WRITE_PUT,
    fields: {"name": "ephemeral"}, base_version: -1
))
val outcome: DurableOutcome = durable_commit(db, state, durability_on())
assert_true(outcome.ok)
assert_equal(outcome.applied, 1)
step("it committed, and it says plainly that nothing was persisted")
assert_false(outcome.persisted)
```

</details>

#### reports a durable commit as persisted

- reports a durable commit as persisted


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a durable commit as persisted")
val path = "build/dbdur_flag.sdn"
var db = fresh_store(path)
var state: TxnState = begin_txn()
state = txn_record(state, TxnWrite(
    table: "users", key: "u1", kind: WRITE_PUT,
    fields: {"name": "kept"}, base_version: -1
))
val outcome: DurableOutcome = durable_commit(db, state, durability_on())
assert_true(outcome.ok)
assert_true(outcome.persisted)
assert_equal(on_disk(path, "u1"), "kept")
```

</details>

#### does not touch the disk when durability is switched off

- does not touch the disk when durability is switched off


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not touch the disk when durability is switched off")
val path = "build/dbdur_off.sdn"
var db = fresh_store(path)
var state: TxnState = begin_txn()
state = txn_record(state, TxnWrite(
    table: "users", key: "u1", kind: WRITE_PUT,
    fields: {"name": "memory_only"}, base_version: -1
))
val outcome: DurableOutcome = durable_commit(db, state, durability_off())
assert_true(outcome.ok)
assert_false(outcome.persisted)
assert_false(file_exists(path))
```

</details>

### DB durability — restart-safe versions and commit identity

#### fails closed on missing or invalid declared persisted versions

- fails closed on missing or invalid declared persisted versions


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed on missing or invalid declared persisted versions")
for persisted in ["", "not-a-version", "-1"]:
    var db = SdnDatabase.new("")
    var users = SdnTable.new("users", ["id", "name", "valid", DURABLE_VERSION_COLUMN])
    var fields: Dict<text, text> = {"id": "u1", "name": "old", "valid": "true"}
    if persisted != "":
        fields[DURABLE_VERSION_COLUMN] = persisted
    users.add_row(SdnRow(fields: fields, _version: 0))
    db.set_table("users", users)
    assert_equal(store_version(db, "users", "u1"), INVALID_PERSISTED_VERSION)
    var server = DbServerCapsule.new(db, alice_policy())
    server.handle_message("OPEN as=alice credential=alice-secret")
    server.handle_message("BEGIN session=1")
    server.handle_message("PUT session=1 tbl=users id=u1 name=new")
    assert_contains(server.handle_message("COMMIT session=1 commit_id=invalid-version"), "code=conflict")
```

</details>

#### rejects a malformed durable receipt schema on replay

- rejects a malformed durable receipt schema on replay


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a malformed durable receipt schema on replay")
val path = "build/dbdur_bad_receipt.sdn"
var db = fresh_store(path)
var receipts = SdnTable.new(COMMIT_TABLE, ["id", "principal", "applied", "identity", "valid"])
val bad = SdnRow(fields: {
    "id": "bad-receipt", "principal": "alice", "applied": "not-a-number",
    "identity": "short", "valid": "true"
}, _version: 0)
receipts.add_row(bad)
db.set_table(COMMIT_TABLE, receipts)
assert_true(db.save())
val reopened = SdnDatabase.load(path) ?? SdnDatabase.new("")
var server = DbServerCapsule.new(reopened, alice_policy())
server.handle_message("OPEN as=alice credential=alice-secret")
assert_contains(server.handle_message("COMMIT session=1 commit_id=bad-receipt"), "code=conflict")
```

</details>

#### rejects a new commit id when durable receipt retention is full

- rejects a new commit id when durable receipt retention is full


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a new commit id when durable receipt retention is full")
val path = "build/dbdur_receipt_capacity.sdn"
var db = fresh_store(path)
val filler = SdnRow(fields: {
    "id": "filler", "principal": "alice", "applied": "1",
    "identity": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "valid": "true"
}, _version: 0)
val full = SdnTable(
    name: COMMIT_TABLE,
    columns: ["id", "principal", "applied", "identity", "valid"],
    rows: [filler; MAX_COMMIT_RECEIPTS], index: {}
)
db.set_table(COMMIT_TABLE, full)
var server = DbServerCapsule.new(db, alice_policy())
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=blocked")
assert_contains(server.handle_message("COMMIT session=1 commit_id=over-cap"), "code=conflict")
assert_equal(on_disk(path, "u1"), ABSENT)
```

</details>

#### persists optimistic row versions across reopen

- persists optimistic row versions across reopen


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("persists optimistic row versions across reopen")
val path = "build/dbdur_versions.sdn"
var first = DbServerCapsule.new(fresh_store(path), alice_policy())
first.handle_message("OPEN as=alice credential=alice-secret")
first.handle_message("BEGIN session=1")
first.handle_message("PUT session=1 tbl=users id=u1 name=one")
first.handle_message("COMMIT session=1 commit_id=version-1")
first.handle_message("BEGIN session=1")
first.handle_message("PUT session=1 tbl=users id=u1 name=two")
first.handle_message("COMMIT session=1 commit_id=version-2")
val reopened = SdnDatabase.load(path) ?? SdnDatabase.new("")
assert_equal(store_version(reopened, "users", "u1"), 1)
```

</details>

#### answers a reconnect retry from the durable commit receipt

- answers a reconnect retry from the durable commit receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("answers a reconnect retry from the durable commit receipt")
val path = "build/dbdur_commit_identity.sdn"
var first = DbServerCapsule.new(fresh_store(path), alice_policy())
first.handle_message("OPEN as=alice credential=alice-secret")
first.handle_message("BEGIN session=1")
first.handle_message("PUT session=1 tbl=users id=u1 name=once")
assert_equal(first.handle_message("COMMIT session=1 commit_id=stable-42"), "OK applied=1")
val reopened = SdnDatabase.load(path) ?? SdnDatabase.new("")
var retry = DbServerCapsule.new(reopened, alice_policy())
retry.handle_message("OPEN as=alice credential=alice-secret")
assert_equal(retry.handle_message("COMMIT session=1 commit_id=stable-42"), "OK applied=1")
assert_equal(on_disk(path, "u1"), "once")
var cross_policy = alice_policy()
cross_policy.register_authenticated(capability_with("bob", [grant_key("users", "read")]), "bob-secret")
var cross = DbServerCapsule.new(reopened, cross_policy)
cross.handle_message("OPEN as=bob credential=bob-secret")
assert_contains(cross.handle_message("COMMIT session=1 commit_id=stable-42"), "code=conflict")
```

</details>

#### rejects reuse of one commit id for different transaction content

- rejects reuse of one commit id for different transaction content


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects reuse of one commit id for different transaction content")
val path = "build/dbdur_commit_identity_conflict.sdn"
var server = DbServerCapsule.new(fresh_store(path), alice_policy())
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=first")
server.handle_message("COMMIT session=1 commit_id=stable-conflict")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u2 name=second")
assert_contains(server.handle_message("COMMIT session=1 commit_id=stable-conflict"), "code=conflict")
assert_equal(on_disk(path, "u2"), ABSENT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** ``.spipe/db_durability/state.md``


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-DBSERVER-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7f3ab0390f16537b6936cfb8dce0e6c93ddc1777de0709fff2589ebd7c6b38e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f3ab0390f16537b6936cfb8dce0e6c93ddc1777de0709fff2589ebd7c6b38e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f3ab0390f16537b6936cfb8dce0e6c93ddc1777de0709fff2589ebd7c6b38e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/database/server/db_durability_spec.spl
mirror: doc/06_spec/03_system/database/server/db_durability_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/database/server/db_durability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/database/server/db_durability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/database/server/db_durability_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/database/server/db_durability_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores a committed row where a brand new reader finds it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/database/server/db_durability_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores an update over an already durable row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/database/server/db_durability_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes a committed delete permanent too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
