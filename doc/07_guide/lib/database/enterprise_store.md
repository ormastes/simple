# Enterprise Store — Durable Persistence for the Enterprise Suite

`std.enterprise_store` (impl: `src/lib/nogc_sync_mut/enterprise_store/`,
default-tier wrapper in `nogc_async_mut`) is the durable foundation of the
Simple Enterprise Suite (assessment:
`doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md` §4;
lane: `.spipe/simple_enterprise_suite`).

## Surface

| Function | Purpose |
|----------|---------|
| `store_open(path)` / `store_close` | Open with WAL/busy-timeout/FK pragmas + system tables |
| `store_backend_acid(store)` | Honest live probe: can this backend actually roll back? |
| `uow_begin` / `uow_commit` / `uow_rollback` | Unit of work |
| `store_migrate(store, name, sql)` | Named migration, applied once, re-run no-op |
| `idempotency_seen` / `idempotency_result` / `idempotency_record` | Command replay guard |
| `outbox_append` / `outbox_pending` | Transactional outbox (append in the same UoW as the mutation) |
| `audit_append` / `audit_verify_chain` | sha256-chained append-only audit log |
| `store_rows` / `store_insert_row` | Prepared-bind low-level access |

`std.enterprise_sale` builds the first proving vertical on top:
catalog → stock ledger → guarded order (session → rbac → validation →
idempotency → effects in one UoW) → payment → balanced journal → refund.
System spec: `test/03_system/app/enterprise/goods_sale_vertical_spec.spl`.

## Backend honesty — read this before trusting durability evidence

The interpreter's `rt_sqlite_*` externs are a **non-ACID emulation**:
transactions no-op, constraints unenforced, WHERE-equality ignored, UPDATE
unsupported, and open databases are cached per path in-process (deleting the
file does not reset state within a process). Tracked:
`doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md`.

Consequences baked into the design:

- `store_open` probes rollback honesty and records `acid`; atomicity claims
  require `acid=true` (real SQLite in native builds, later PostgreSQL).
- Tables are **insert-only**; state is derived (stock = sum of deltas,
  order status = last event). Rows are filtered **in pure Simple** so tenant
  scoping cannot be silently dropped by the emulation's WHERE handling.
- All values go through prepared-statement binds — no inline SQL literals.
- Specs must use a distinct database path per scenario.

## Production posture

PostgreSQL is the intended production system of record (assessment §4.2);
this module's surface is the frozen Repository/UnitOfWork contract a future
PostgreSQL adapter implements. No fake driver exists — the adapter is an
explicit open gap, not a green checkbox. Simple DB (SDN/embedded) is a
research track and must not carry finance/PII/stock truth.
