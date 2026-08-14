# Enterprise Store — TL;DR

`std.enterprise_store`: durable foundation (migrations, UoW, idempotency,
outbox, sha256 audit chain) + `std.enterprise_sale` goods-sale vertical
(guarded orders, stock ledger, balanced journal). Insert-only tables,
prepared binds, pure-Simple tenant filtering, honest ACID backend probe.

```sdn
diagram: {
  command -> guard: "session -> rbac -> validation -> idempotency"
  guard -> uow: "effects in ONE unit of work"
  uow -> tables: {order_events, stock_moves, journal, outbox, audit_log, idempotency_keys}
  store_open -> acid_probe: "insert -> rollback -> count (honest capability)"
  backend: {interpreter_emulation: "NON-ACID (bug filed)", native_sqlite: "real", postgresql: "frozen interface, no driver yet"}
}
```

Interpreter rt_sqlite is a non-ACID toy (rollback no-op, constraints
unenforced) — bug:
`doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md`.
ACID evidence needs native/real SQLite; atomicity specs read the probe.

Specs: `enterprise_store_spec` 10/10,
`goods_sale_vertical_spec` 7/7 (replay = exactly one effect; tenant
isolation; restart survival). Full guide: `enterprise_store.md`.
