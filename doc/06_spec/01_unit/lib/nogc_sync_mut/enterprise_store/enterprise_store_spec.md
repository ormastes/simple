# Enterprise Store — migrations, idempotency, outbox, and audit chain

> The enterprise store is the durable foundation of the Simple Enterprise Suite: schema migrations with a version table, a unit of work, idempotency keys, the transactional outbox, and a sha256-chained audit log (`std.enterprise_store`, default-tier wrapper over `std.nogc_sync_mut.enterprise_store`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Store — migrations, idempotency, outbox, and audit chain

The enterprise store is the durable foundation of the Simple Enterprise Suite: schema migrations with a version table, a unit of work, idempotency keys, the transactional outbox, and a sha256-chained audit log (`std.enterprise_store`, default-tier wrapper over `std.nogc_sync_mut.enterprise_store`).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The enterprise store is the durable foundation of the Simple Enterprise
Suite: schema migrations with a version table, a unit of work, idempotency
keys, the transactional outbox, and a sha256-chained audit log
(`std.enterprise_store`, default-tier wrapper over
`std.nogc_sync_mut.enterprise_store`).

The store PROBES its backend at open and records `acid` honestly: the
interpreter's rt_sqlite emulation cannot roll back
(doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md),
so atomicity scenarios in this manual first read the probe and assert the
HONEST answer for the running backend; commit/rollback-atomicity PASS
evidence requires an ACID backend (real SQLite in native mode, later
PostgreSQL). Everything else in this manual — migration idempotence, replay
detection, tenant scoping, restart survival, audit chain integrity and
tamper detection — holds on both backends and is asserted unconditionally.

## Examples

```simple
val store = store_open("erp.db")
uow_begin(store)
if idempotency_seen(store, tenant, key):
    return idempotency_result(store, tenant, key)   # replay: one effect only
# ... domain mutation ...
outbox_append(store, tenant, "sales.order.created", payload)
idempotency_record(store, tenant, key, "accepted")
audit_append(store, tenant, actor, "order.create", detail)
uow_commit(store)
```

## Troubleshooting

- `store_backend_acid(store) == false` — the backend cannot roll back;
  durability claims are limited to append/replay semantics. Run natively
  with real SQLite for ACID evidence.
- `audit_verify_chain == false` — a record was altered or the chain was
  broken; every record's hash covers its predecessor's hash.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Wave B, AC-5/AC-6/AC-7).

## Scenarios

### enterprise store — open and backend capability probe

#### opens an in-memory store with system tables ready

- Open the enterprise store
- Verify system tables exist and start empty
   - Expected: store_rows(store, "outbox", "id, tenant_id, event_type, payload").len() equals `0`
   - Expected: store_rows(store, "audit_log", "id, tenant_id, actor, action, detail, prev_hash, hash").len() equals `0`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open the enterprise store")
val store = store_open(":memory:")
expect(store.open_ok).to_be(true)
step("Verify system tables exist and start empty")
expect(store_rows(store, "outbox", "id, tenant_id, event_type, payload").len()).to_equal(0)
expect(store_rows(store, "audit_log", "id, tenant_id, actor, action, detail, prev_hash, hash").len()).to_equal(0)
store_close(store)
```

</details>

#### reports backend transaction honesty from a live probe

- Open the store and read the ACID capability
- Cross-check the probe against a direct rollback experiment
- uow begin
- outbox append
- uow rollback
   - Expected: leaked equals `0`
   - Expected: leaked equals `1`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open the store and read the ACID capability")
val store = store_open(":memory:")
# The probe inserted under begin and rolled back; acid is true only
# when the rollback actually removed the row. On the interpreter's
# rt_sqlite emulation this is false (tracked bug) — asserting the
# probe agrees with a direct rollback experiment keeps it honest.
step("Cross-check the probe against a direct rollback experiment")
uow_begin(store)
outbox_append(store, "probe-tenant", "probe.event", "x")
uow_rollback(store)
val leaked = outbox_pending(store, "probe-tenant").len()
if store_backend_acid(store):
    expect(leaked).to_equal(0)
else:
    expect(leaked).to_equal(1)
store_close(store)
```

</details>

### enterprise store — migrations apply once

#### applies a named migration and records it

- Apply the products-table migration
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = store_open(":memory:")
step("Apply the products-table migration")
val ok = store_migrate(store, "001_products", "CREATE TABLE products (id INTEGER PRIMARY KEY, sku TEXT, price TEXT)")
expect(ok).to_be(true)
expect(store_migration_applied(store, "001_products")).to_be(true)
store_close(store)
```

</details>

#### re-running the same migration is a no-op

- store migrate
- Apply the same migration a second time
- Verify it was recorded exactly once
   - Expected: count equals `1`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = store_open(":memory:")
store_migrate(store, "001_products", "CREATE TABLE products (id INTEGER PRIMARY KEY, sku TEXT, price TEXT)")
step("Apply the same migration a second time")
val again = store_migrate(store, "001_products", "CREATE TABLE products (id INTEGER PRIMARY KEY, sku TEXT, price TEXT)")
expect(again).to_be(true)
step("Verify it was recorded exactly once")
var count = 0
for row in store_rows(store, "schema_migrations", "id, name, applied_seq"):
    count = count + 1
expect(count).to_equal(1)
store_close(store)
```

</details>

### enterprise store — idempotency keys detect replay

#### records a command key and detects the replay

- Record the first execution of command key ord-1
- idempotency record
- Replay the same key
   - Expected: idempotency_result(store, "tenant-a", "ord-1") equals `accepted:order-100`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = store_open(":memory:")
step("Record the first execution of command key ord-1")
expect(idempotency_seen(store, "tenant-a", "ord-1")).to_be(false)
idempotency_record(store, "tenant-a", "ord-1", "accepted:order-100")
step("Replay the same key")
expect(idempotency_seen(store, "tenant-a", "ord-1")).to_be(true)
expect(idempotency_result(store, "tenant-a", "ord-1")).to_equal("accepted:order-100")
store_close(store)
```

</details>

#### scopes keys per tenant — tenant B does not see tenant A's key

- idempotency record
- Check the same key under a different tenant
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = store_open(":memory:")
idempotency_record(store, "tenant-a", "ord-1", "accepted")
step("Check the same key under a different tenant")
expect(idempotency_seen(store, "tenant-b", "ord-1")).to_be(false)
store_close(store)
```

</details>

### enterprise store — outbox events are tenant-scoped and ordered

#### returns a tenant's events in append order

- Append two events for tenant A and one for tenant B
- outbox append
- outbox append
- outbox append
- Read tenant A's pending events
   - Expected: pending.len() equals `2`
   - Expected: pending[0].0 equals `sales.order.created`
   - Expected: pending[1].0 equals `inventory.stock.reserved`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = store_open(":memory:")
step("Append two events for tenant A and one for tenant B")
outbox_append(store, "tenant-a", "sales.order.created", "o1")
outbox_append(store, "tenant-b", "sales.order.created", "other")
outbox_append(store, "tenant-a", "inventory.stock.reserved", "o1")
step("Read tenant A's pending events")
val pending = outbox_pending(store, "tenant-a")
expect(pending.len()).to_equal(2)
expect(pending[0].0).to_equal("sales.order.created")
expect(pending[1].0).to_equal("inventory.stock.reserved")
store_close(store)
```

</details>

### enterprise store — audit chain integrity

#### chains records with sha256 over the predecessor

- Append two audit records
- audit append
- audit append
- Verify the whole chain recomputes
- Verify the second record covers the first record's hash
   - Expected: audit_last_hash(store, "tenant-a") equals `h2`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = store_open(":memory:")
step("Append two audit records")
audit_append(store, "tenant-a", "user-1", "order.create", "order-100")
audit_append(store, "tenant-a", "user-1", "order.pay", "order-100")
step("Verify the whole chain recomputes")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
step("Verify the second record covers the first record's hash")
val h1 = audit_hash("", "tenant-a", "user-1", "order.create", "order-100")
val h2 = audit_hash(h1, "tenant-a", "user-1", "order.pay", "order-100")
expect(audit_last_hash(store, "tenant-a")).to_equal(h2)
store_close(store)
```

</details>

#### detects a tampered chain

- audit append
- Forge a record whose prev_hash skips the chain head
   - Expected: forged.len() equals `1`
- "INSERT INTO audit log
- Verify the chain check fails closed
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = store_open(":memory:")
audit_append(store, "tenant-a", "user-1", "order.create", "order-100")
step("Forge a record whose prev_hash skips the chain head")
# Direct forged insert (bypassing audit_append) with a wrong prev_hash.
val forged = store_rows(store, "audit_log", "id, tenant_id, actor, action, detail, prev_hash, hash")
expect(forged.len()).to_equal(1)
# Append a record with a broken linkage by hashing from an empty prev.
val bad_hash = audit_hash("", "tenant-a", "mallory", "order.refund", "order-100")
store_insert_row(store,
    "INSERT INTO audit_log (tenant_id, actor, action, detail, prev_hash, hash) VALUES (?, ?, ?, ?, ?, ?)",
    ["tenant-a", "mallory", "order.refund", "order-100", "", bad_hash])
step("Verify the chain check fails closed")
expect(audit_verify_chain(store, "tenant-a")).to_be(false)
store_close(store)
```

</details>

### enterprise store — state survives close and reopen

#### reopens a file-backed store with all records intact

- Start from a clean database file
- dir create all
- file delete
- Open a file-backed store and write records
- store migrate
- idempotency record
- outbox append
- audit append
- store close
- Reopen the same database file (simulated restart)
- Verify migration, idempotency, outbox, and audit all survived
   - Expected: outbox_pending(store2, "tenant-a").len() equals `1`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "build/test-artifacts/enterprise_store_restart.db"
step("Start from a clean database file")
dir_create_all("build/test-artifacts")
if file_exists(db_path):
    file_delete(db_path)
step("Open a file-backed store and write records")
val store = store_open(db_path)
expect(store.open_ok).to_be(true)
store_migrate(store, "001_products", "CREATE TABLE products (id INTEGER PRIMARY KEY, sku TEXT, price TEXT)")
idempotency_record(store, "tenant-a", "restart-key", "accepted")
outbox_append(store, "tenant-a", "sales.order.created", "o-restart")
audit_append(store, "tenant-a", "user-1", "order.create", "o-restart")
store_close(store)

step("Reopen the same database file (simulated restart)")
val store2 = store_open(db_path)
expect(store2.open_ok).to_be(true)

step("Verify migration, idempotency, outbox, and audit all survived")
expect(store_migration_applied(store2, "001_products")).to_be(true)
expect(idempotency_seen(store2, "tenant-a", "restart-key")).to_be(true)
expect(outbox_pending(store2, "tenant-a").len()).to_equal(1)
expect(audit_verify_chain(store2, "tenant-a")).to_be(true)
store_close(store2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
