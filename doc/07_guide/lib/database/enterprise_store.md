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

## Failure-path hardening (AC-18, 2026-08-16)

- **Corruption detection**: `store_open` writes a store-format marker row
  (`__store_format_v1` in `acid_probe`). `store_verify(store)` returns `""`
  when healthy, else an explicit `corrupt store: ...` error; it checks every
  system table is readable (real SQLite: a bad-magic/truncated file fails the
  COUNT probe) AND the marker is present (portable detector — the interpreter
  emulation silently answers COUNT=0 for any table on any file, so table
  presence alone proves nothing there). `store_open_verified(path)` opens an
  EXISTING store without creating tables and rejects blank/garbage/foreign
  files with `open_ok=false` plus the error — never silent acceptance.
- **Write-failure seam**: the interpreter's rt_sqlite externs cannot inject a
  real disk-full/short-write (non-ACID emulation, tracked bug). The
  composition seam is `BufferedUow` + `StoreFaults`: stage writes with
  `buffered_write`, apply all-or-nothing with
  `buffered_commit(store, uow, faults)`. `store_faults_failing_commit()`
  simulates the write-layer failure; a failed commit applies NOTHING, so
  zero-partial-effects holds on BOTH backends.
- **Native-ACID resume condition**: real short-write/crash injection and
  rollback-atomicity PASS evidence stay environment-blocked until the specs
  run `--mode=native` against real SQLite (linked C sqlite3). Resume:
  `bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl --mode=native`
  on a host where native codegen + real rt_sqlite are green.

## Cross-OS runnability (AC-17, audited 2026-08-16)

`std.enterprise_{store,sale}` is ONE codebase targeting the SimpleOS
**userland** tier (ring-3 app over libc/syscalls; no kernel-path code, so the
freestanding discipline in `doc/07_guide/os/simpleos_host_os_guide.md` does
not constrain it). Full import audit:

| Dependency | Facade | Both-OS status |
|---|---|---|
| SQLite access | `std.nogc_sync_mut.io.sqlite_sffi` (rt_sqlite_* externs) | Host: yes (emulation/native). SimpleOS: **blocked** — no `rt_sqlite_*` provider in `src/os/` (libc has no sqlite; DBFS is a filesystem, not this extern surface) |
| Audit hashing | `std.common.crypto.sha256` (pure Simple) | Both |
| Foundation contracts (`enterprise_sale.foundation`) | none (pure Simple, zero imports) | Both |
| Filesystem / env / process / time | **not used** by the library (specs use `std.io_runtime` on the host harness only) | n/a |

Evidence: minimal entry `src/app/enterprise/store_probe_main.spl` —
host run prints `enterprise store open=true verify=[]`; SimpleOS-target
cross-compile succeeds:
`bin/simple compile --target=x86_64-unknown-simpleos src/app/enterprise/store_probe_main.spl -o build/test-artifacts/enterprise_entry_simpleos`
(SMF module artifact, magic `SMF\0`). Remaining blocked row: link/run inside
SimpleOS requires an in-guest `rt_sqlite_*` extern provider; resume = provide
that surface (or a DBFS-backed adapter behind the same facade), then rerun
the compile + boot the probe per the host-OS guide. No per-OS fork exists.

Spec manuals (generated via spipe-docgen into `doc/06_spec/`):
`enterprise_store_spec.md` (repository/UoW/migration/outbox surface) and
`enterprise_store_harden_spec.md` (corruption/fault-injection seams); system
level: `store_app_spec.md`, `store_web_harden_spec.md`,
`goods_sale_vertical_spec.md`.
