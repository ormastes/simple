# Interpreter rt_sqlite_* externs are a non-ACID SQL emulation (transactions no-op, constraints unenforced)

- Date: 2026-08-14
- Area: runtime / interpreter externs / database
- Severity: high (blocks honest durability evidence for any interpreter-mode
  spec built on `std.nogc_sync_mut.io.sqlite_sffi`)
- Found by: `.spipe/simple_enterprise_suite` Wave B probe
  (enterprise durable-store lane)

## Symptom

Probe (`bin/release/aarch64-apple-darwin/simple run` on an in-memory db):

```
begin=true ins2=true rollback=true count_after_rollback=2   # rollback did NOT undo the insert
dup_insert=true err=                                        # UNIQUE violation reported as SUCCESS
fk_default=                                                 # PRAGMA returns nothing
```

## Root cause

The interpreter does not bind the real SQLite runtime
(`src/runtime/runtime_sqlite.c` / rusqlite). Instead
`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs` implements a
hand-rolled SQL emulation (`sqlite_parse_create`, `sqlite_parse_insert`,
`sqlite_like`, serialize-to-file), and:

- `rt_sqlite_begin_fn` / `rt_sqlite_commit_fn` / `rt_sqlite_rollback_fn`
  ignore their arguments and return `Ok(Int(1))` — transactions are no-ops
  (sffi_db.rs:1445-1455).
- Column constraints (UNIQUE, FOREIGN KEY, CHECK) are not parsed or
  enforced; a violating INSERT succeeds.
- PRAGMA statements return nothing.

Native builds link the real SQLite, so behavior diverges interpreter-vs-native
(a differential-correctness hazard on top of the honesty hazard).

## Impact

- Any interpreter-mode spec that asserts commit/rollback atomicity,
  idempotency-key uniqueness via UNIQUE constraints, or FK integrity will
  false-green (success returns) while proving nothing.
- The enterprise durable-store lane (AC-5/AC-6 of
  `.spipe/simple_enterprise_suite/state.md`) must classify ACID evidence as
  `environment-blocked` under the interpreter and gate real evidence on a
  native-mode run with the real SQLite runtime.

## Suggested fix

Bind the interpreter externs to the real bundled SQLite (rusqlite is already
a seed dependency for native tooling), or at minimum implement
begin/commit/rollback snapshotting and UNIQUE enforcement in the emulation
and make unsupported PRAGMAs/constraints return an explicit error instead of
silent success. Until then, specs should probe transaction honesty first
(insert → rollback → count) and fail closed / classify blocked when the
backend cannot roll back.

## Workaround used by the enterprise store lane

`std.nogc_sync_mut.enterprise_store` runs a self-probe
(`store_backend_capabilities`) at open: it detects non-transactional backends
and reports `acid=false`, and its specs assert application-level invariants
(idempotency replay via SELECT-before-INSERT, audit sha256 chain) that hold
on both backends, while atomicity/constraint specs require `acid=true`.
