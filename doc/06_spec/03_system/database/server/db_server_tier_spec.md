# Simple DB Server Tier — Increment 1

> The Simple DB embedded SDN store (`std.database.core`) has always been a single-process library: one program opens a file, mutates tables in memory and saves.  The **server tier** is what turns it into something several clients can talk to at once without seeing each other's half-finished work.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple DB Server Tier — Increment 1

The Simple DB embedded SDN store (`std.database.core`) has always been a single-process library: one program opens a file, mutates tables in memory and saves.  The **server tier** is what turns it into something several clients can talk to at once without seeing each other's half-finished work.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / Infrastructure |
| Status | In Progress (increment 1 of the server tier) |
| Design | .spipe/db_server_tier/state.md |
| Source | `test/03_system/database/server/db_server_tier_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Simple DB embedded SDN store (`std.database.core`) has always been a
single-process library: one program opens a file, mutates tables in memory and
saves.  The **server tier** is what turns it into something several clients can
talk to at once without seeing each other's half-finished work.

This manual covers the first increment: a client opens a session, is checked
against a capability, runs a transaction, and either commits it (making the
change visible to everyone) or rolls it back (making it visible to nobody).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Session | One client connection.  Has a principal, a capability and at most one open transaction. |
| Capability | The explicit set of (table, read/write) grants a principal holds.  Deny-wins: anything not granted is refused. |
| Write overlay | A transaction's private buffer.  Peers cannot see it; only COMMIT moves it into the store. |
| Isolation | Read-committed: a peer session observes committed data only. |

## Related Specifications

- `std.database.core` — the embedded store this tier sits on top of.  The
  server tier adds no storage of its own.

## Scenarios

### DB server tier — connection lifecycle

#### rejects a known principal without its credential

- rejects a known principal without its credential


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a known principal without its credential")
var server = make_server()
assert_contains(server.handle_message("OPEN as=alice"), "code=auth")
```

</details>

#### rejects a known principal with the wrong credential

- rejects a known principal with the wrong credential


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a known principal with the wrong credential")
var server = make_server()
assert_contains(server.handle_message("OPEN as=alice credential=bob-secret"), "code=auth")
```

</details>

#### stores only a fixed digest and returns an authenticated principal proof

- stores only a fixed digest and returns an authenticated principal proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores only a fixed digest and returns an authenticated principal proof")
val policy = make_policy()
assert_equal(policy.credential_digests["alice"].chars().len(), 64)
assert_false(policy.credential_digests["alice"] == "alice-secret")
val proof = policy.authenticate_principal("alice", "alice-secret")
assert_true(proof.?)
assert_equal((proof ?? AuthenticatedPrincipal(principal: "", capability: empty_capability(""))).principal, "alice")
```

</details>

#### gives each client its own session id

- gives each client its own session id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gives each client its own session id")
var server = make_server()
val first = server.handle_message("OPEN as=alice credential=alice-secret")
val second = server.handle_message("OPEN as=bob credential=bob-secret")
assert_equal(first, "OK session=1")
assert_equal(second, "OK session=2")
```

</details>

#### polls accept timeouts until explicit shutdown becomes observable

- polls accept timeouts until explicit shutdown becomes observable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("polls accept timeouts until explicit shutdown becomes observable")
var owner = DbStopControl.new()
val accept_owner = owner
assert_false(accept_owner.is_stopped())
owner.request_stop()
assert_true(accept_owner.is_stopped())
```

</details>

#### terminates the connection and cleans sessions after a write failure

- terminates the connection and cleans sessions after a write failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("terminates the connection and cleans sessions after a write failure")
var server = make_server()
val outcome = server.serve(MemoryTransport.with_failed_writes([
    "OPEN as=alice credential=alice-secret", "PING session=1"
]))
assert_equal(outcome.served, 0)
assert_equal(server.registry.open_session_count(), 0)
```

</details>

#### refuses to work for a session that was never opened

- refuses to work for a session that was never opened


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses to work for a session that was never opened")
var server = make_server()
val reply = server.handle_message("BEGIN session=99")
assert_contains(reply, "code=no_session")
```

</details>

#### refuses to work for a session that has been closed

- refuses to work for a session that has been closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses to work for a session that has been closed")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
assert_equal(server.handle_message("CLOSE session=1"), "OK")
assert_contains(server.handle_message("BEGIN session=1"), "code=no_session")
```

</details>

#### discards an abandoned transaction when the connection closes

- discards an abandoned transaction when the connection closes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("discards an abandoned transaction when the connection closes")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=ghost name=nobody")
server.handle_message("CLOSE session=1")
# Absolute oracle: the store itself never received the row.
val store = server.store
assert_nil(store_read(store, "users", "ghost"))
```

</details>

#### answers every message on a connection driven by the transport port

- answers every message on a connection driven by the transport port


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("answers every message on a connection driven by the transport port")
var server = make_server()
var channel = MemoryTransport.with_messages([
    "OPEN as=alice credential=alice-secret",
    "PING session=1",
    "CLOSE session=1"
])
val served = server.serve(channel)
assert_equal(served, 3)
assert_equal(channel.sent_count(), 3)
assert_equal(channel.all_sent()[0], "OK session=1")
```

</details>

### DB server tier — request framing is fail-closed

#### rejects an unknown operation instead of executing anything

- rejects an unknown operation instead of executing anything


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an unknown operation instead of executing anything")
var server = make_server()
val reply = server.handle_message("DROPTABLE session=1 tbl=users")
assert_contains(reply, "code=malformed")
assert_contains(reply, "unknown op")
```

</details>

#### rejects an unterminated quote instead of crashing

- rejects an unterminated quote instead of crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an unterminated quote instead of crashing")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
val reply = server.handle_message('PUT session=1 tbl=users id="oops name=x')
assert_contains(reply, "code=malformed")
# The connection is still usable afterwards — no poisoned state.
assert_equal(server.handle_message("PING session=1"), "OK")
```

</details>

#### rejects an argument with no equals sign

- rejects an argument with no equals sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an argument with no equals sign")
val parsed = parse_request("PUT session=1 garbage")
assert_true(parsed.is_err())
```

</details>

#### rejects a duplicated argument rather than silently picking one

- rejects a duplicated argument rather than silently picking one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a duplicated argument rather than silently picking one")
val parsed = parse_request("PUT session=1 tbl=users tbl=audit id=u1")
assert_true(parsed.is_err())
```

</details>

#### rejects an empty request

- rejects an empty request


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an empty request")
assert_true(parse_request("   ").is_err())
```

</details>

#### rejects a non-numeric session id

- rejects a non-numeric session id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a non-numeric session id")
var server = make_server()
val reply = server.handle_message("BEGIN session=notanumber")
assert_contains(reply, "code=malformed")
```

</details>

#### keeps quoted values containing spaces intact

- keeps quoted values containing spaces intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps quoted values containing spaces intact")
val parsed = parse_request('PUT session=1 tbl=users id=u1 name="ada lovelace"')
match parsed:
    Ok(request):
        assert_equal(request.arg("name") ?? "", "ada lovelace")
    Err(message):
        assert_true(false)
```

</details>

#### encodes response fields in a stable order

- encodes response fields in a stable order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encodes response fields in a stable order")
# Dict iteration order is not stable across processes; the wire form
# must be.  Encoding the same response twice must match.
val response = err_response("conflict", "boom")
assert_equal(encode_response(response), encode_response(response))
assert_equal(encode_response(response), 'ERR code=conflict msg=boom')
```

</details>

### DB server tier — transaction isolation between two sessions

#### hides one session's uncommitted write from the other session

- hides one session's uncommitted write from the other session


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hides one session's uncommitted write from the other session")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")   # session 1, read+write
server.handle_message("OPEN as=bob credential=bob-secret")     # session 2, read-only
server.handle_message("BEGIN session=1")
assert_equal(server.handle_message("PUT session=1 tbl=users id=u1 name=ada"), "OK")

# The writer reads its own uncommitted write ...
assert_equal(
    server.handle_message("GET session=1 tbl=users id=u1 col=name"),
    "OK value=ada"
)
# ... the peer does not.
assert_contains(
    server.handle_message("GET session=2 tbl=users id=u1 col=name"),
    "code=not_found"
)
# Absolute oracle, independent of the server's own read path:
# the underlying store holds nothing.
val store = server.store
assert_nil(store_read(store, "users", "u1"))
```

</details>

#### shows the write to the other session once it is committed

- shows the write to the other session once it is committed


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shows the write to the other session once it is committed")
# UNCONDITIONAL CONTROL for the test above.  This uses the exact same
# peer read path.  If that path were simply incapable of observing a
# row, this assertion would fail too — so the "not_found" above cannot
# be a false green.
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("OPEN as=bob credential=bob-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=ada")
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
assert_equal(
    server.handle_message("GET session=2 tbl=users id=u1 col=name"),
    "OK value=ada"
)
```

</details>

#### would go red if an uncommitted write reached the store

- would go red if an uncommitted write reached the store


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("would go red if an uncommitted write reached the store")
# DELIBERATE-RED CALIBRATION.  We inject the isolation violation by
# hand — writing straight into the store while session 1's transaction
# is still open — and assert that the isolation oracle now REPORTS the
# leak.  This proves the two assertions in the isolation test above are
# capable of failing.
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("OPEN as=bob credential=bob-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=ada")

# --- inject the violation the server is designed to prevent ---
var store = server.store
match store.get_table_mut("users"):
    Some(table_value):
        var table: SdnTable = table_value
        var leaked = SdnRow(fields: {}, _version: 0)
        leaked.set("id", "u1")
        leaked.set("name", "ada")
        leaked.set("valid", "true")
        table.add_row(leaked)
        store.set_table("users", table)
    nil:
        assert_true(false)
server.store = store

# The oracle used by the isolation test now sees the leak: red.
assert_true(store_read(server.store, "users", "u1").?)
# And the peer read now observes the uncommitted value: red.
assert_equal(
    server.handle_message("GET session=2 tbl=users id=u1 col=name"),
    "OK value=ada"
)
```

</details>

#### discards a rolled-back transaction entirely

- discards a rolled-back transaction entirely


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("discards a rolled-back transaction entirely")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("OPEN as=bob credential=bob-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=ada")
assert_equal(server.handle_message("ROLLBACK session=1"), "OK")
assert_nil(store_read(server.store, "users", "u1"))
assert_contains(
    server.handle_message("GET session=2 tbl=users id=u1 col=name"),
    "code=not_found"
)
```

</details>

#### keeps two concurrent transactions from seeing each other's writes

- keeps two concurrent transactions from seeing each other's writes


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps two concurrent transactions from seeing each other's writes")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")   # session 1
server.handle_message("OPEN as=alice credential=alice-secret")   # session 2, same principal
server.handle_message("BEGIN session=1")
server.handle_message("BEGIN session=2")
server.handle_message("PUT session=1 tbl=users id=r1 name=one")
server.handle_message("PUT session=2 tbl=users id=r2 name=two")

assert_contains(
    server.handle_message("GET session=1 tbl=users id=r2 col=name"),
    "code=not_found"
)
assert_contains(
    server.handle_message("GET session=2 tbl=users id=r1 col=name"),
    "code=not_found"
)
# Both commit; both rows land.
assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
assert_equal(server.handle_message("COMMIT session=2"), "OK applied=1")
assert_equal(
    server.handle_message("GET session=1 tbl=users id=r2 col=name"),
    "OK value=two"
)
```

</details>

#### aborts a commit whose row was changed underneath it

- aborts a commit whose row was changed underneath it


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aborts a commit whose row was changed underneath it")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("OPEN as=alice credential=alice-secret")
# Seed a committed row.
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=v0")
server.handle_message("COMMIT session=1")

# Both sessions now stage a write over the SAME row version.
server.handle_message("BEGIN session=1")
server.handle_message("BEGIN session=2")
server.handle_message("PUT session=1 tbl=users id=u1 name=fromOne")
server.handle_message("PUT session=2 tbl=users id=u1 name=fromTwo")

assert_equal(server.handle_message("COMMIT session=1"), "OK applied=1")
# The loser must be told, not silently overwrite the winner.
val loser = server.handle_message("COMMIT session=2")
assert_contains(loser, "code=conflict")
assert_equal(
    server.handle_message("GET session=1 tbl=users id=u1 col=name"),
    "OK value=fromOne"
)
```

</details>

#### requires an open transaction before any write

- requires an open transaction before any write


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires an open transaction before any write")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
assert_contains(
    server.handle_message("PUT session=1 tbl=users id=u1 name=ada"),
    "code=no_txn"
)
assert_contains(server.handle_message("COMMIT session=1"), "code=no_txn")
assert_contains(server.handle_message("ROLLBACK session=1"), "code=no_txn")
```

</details>

#### refuses to nest transactions on one session

- refuses to nest transactions on one session


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses to nest transactions on one session")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
assert_equal(server.handle_message("BEGIN session=1"), "OK")
assert_contains(server.handle_message("BEGIN session=1"), "code=txn_open")
```

</details>

#### makes a committed delete invisible

- makes a committed delete invisible


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("makes a committed delete invisible")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("PUT session=1 tbl=users id=u1 name=ada")
server.handle_message("COMMIT session=1")
server.handle_message("BEGIN session=1")
server.handle_message("DEL session=1 tbl=users id=u1")
server.handle_message("COMMIT session=1")
assert_nil(store_read(server.store, "users", "u1"))
```

</details>

### DB server tier — capability-checked access is deny-wins

#### refuses a write from a read-only principal

- refuses a write from a read-only principal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a write from a read-only principal")
var server = make_server()
server.handle_message("OPEN as=bob credential=bob-secret")
server.handle_message("BEGIN session=1")
val reply = server.handle_message("PUT session=1 tbl=users id=u1 name=eve")
assert_contains(reply, "code=denied")
# Nothing was staged, so committing changes nothing.
server.handle_message("COMMIT session=1")
assert_nil(store_read(server.store, "users", "u1"))
```

</details>

#### refuses every data reach from a principal with no grants

- refuses every data reach from a principal with no grants


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses every data reach from a principal with no grants")
var server = make_server()
server.handle_message("OPEN as=mallory credential=mallory-secret")
server.handle_message("BEGIN session=1")
assert_contains(
    server.handle_message("GET session=1 tbl=users id=u1 col=name"),
    "code=denied"
)
assert_contains(
    server.handle_message("PUT session=1 tbl=users id=u1 name=x"),
    "code=denied"
)
```

</details>

#### refuses a table the principal was never granted

- refuses a table the principal was never granted


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a table the principal was never granted")
var server = make_server()
server.handle_message("OPEN as=bob credential=bob-secret")   # read on users only
server.handle_message("BEGIN session=1")
assert_contains(
    server.handle_message("GET session=1 tbl=audit id=a1 col=event"),
    "code=denied"
)
```

</details>

#### refuses an unregistered principal before data reach

- refuses an unregistered principal before data reach


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses an unregistered principal before data reach")
var server = make_server()
assert_equal(
    server.handle_message("OPEN as=stranger credential=guess"),
    "ERR code=auth msg=\"authentication failed\""
)
assert_contains(server.handle_message("BEGIN session=1"), "code=no_session")
```

</details>

#### refuses a data operation that names no table

- refuses a data operation that names no table


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a data operation that names no table")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
# An absent table is never read as "unrestricted".
assert_contains(server.handle_message("GET session=1 id=u1"), "code=missing_arg")
assert_false(capability_allows(empty_capability("x"), "", "read"))
```

</details>

#### does not let write access imply read access

- does not let write access imply read access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not let write access imply read access")
val write_only = capability_with("w", [grant_key("users", "write")])
assert_true(capability_allows(write_only, "users", "write"))
assert_false(capability_allows(write_only, "users", "read"))
```

</details>

#### maps each operation to the access it needs

- maps each operation to the access it needs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps each operation to the access it needs")
assert_equal(op_access("GET"), "read")
assert_equal(op_access("PUT"), "write")
assert_equal(op_access("DEL"), "write")
assert_equal(op_access("BEGIN"), "")
```

</details>

#### does not let a session widen its own capability

- does not let a session widen its own capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not let a session widen its own capability")
# capability_grant returns a NEW value; the registered one is unchanged.
var policy = make_policy()
val bob = policy.lookup_or_empty("bob")
assert_false(capability_allows(bob, "users", "write"))
val widened = capability_with("bob", [grant_key("users", "write")])
assert_true(capability_allows(widened, "users", "write"))
# The policy table still holds the narrow capability.
assert_false(capability_allows(policy.lookup_or_empty("bob"), "users", "write"))
```

</details>

### DB server tier — bounded batch and range requests

#### accounts for multibyte UTF-8 values in encoded responses

- accounts for multibyte UTF-8 values in encoded responses


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accounts for multibyte UTF-8 values in encoded responses")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("BATCH_PUT session=1 tbl=users ids=u1,u2 name=猫")
assert_equal(server.handle_message("BATCH_GET session=1 tbl=users ids=u1,u2 col=name"), "OK values=猫,猫")
```

</details>

#### rejects an invalid commit identity before durability work

- rejects an invalid commit identity before durability work


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an invalid commit identity before durability work")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
assert_contains(server.handle_message("COMMIT session=1 commit_id=bad/id"), "code=malformed")
```

</details>

#### applies one capability and transaction boundary to a bounded batch

- applies one capability and transaction boundary to a bounded batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies one capability and transaction boundary to a bounded batch")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
assert_equal(server.handle_message("BATCH_PUT session=1 tbl=users ids=u1,u2 name=batched"), "OK queued=2")
assert_equal(server.handle_message("BATCH_GET session=1 tbl=users ids=u1,u2 col=name"), "OK values=batched,batched")
assert_equal(server.handle_message("COMMIT session=1 commit_id=batch-1"), "OK applied=2")
```

</details>

#### rejects an oversized batch before touching the transaction

- rejects an oversized batch before touching the transaction


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an oversized batch before touching the transaction")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
var ids: [text] = []
for i in 0..65:
    ids.push("u{i}")
assert_contains(server.handle_message("BATCH_PUT session=1 tbl=users ids={ids.join(',')} name=x"), "code=limit")
```

</details>

#### returns a bounded ordered key range

- returns a bounded ordered key range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a bounded ordered key range")
var server = make_server()
server.handle_message("OPEN as=alice credential=alice-secret")
server.handle_message("BEGIN session=1")
server.handle_message("BATCH_PUT session=1 tbl=users ids=u3,u1,u2 name=x")
assert_equal(server.handle_message("RANGE_GET session=1 tbl=users start=u1 end=u3 limit=2"), "OK ids=u1,u2")
server.handle_message("COMMIT session=1 commit_id=range-seed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `.spipe/db_server_tier/state.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-DBSERVER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8235e8bf4d07026ee4dda502fae1c1503ec4192948ac0eef9a1a26ff7be4b71d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8235e8bf4d07026ee4dda502fae1c1503ec4192948ac0eef9a1a26ff7be4b71d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8235e8bf4d07026ee4dda502fae1c1503ec4192948ac0eef9a1a26ff7be4b71d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/database/server/db_server_tier_spec.spl
mirror: doc/06_spec/03_system/database/server/db_server_tier_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/database/server/db_server_tier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/database/server/db_server_tier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/database/server/db_server_tier_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/database/server/db_server_tier_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a known principal without its credential' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/database/server/db_server_tier_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a known principal with the wrong credential' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/database/server/db_server_tier_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores only a fixed digest and returns an authenticated principal proof' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
