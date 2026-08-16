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
| SQLite access | `std.nogc_sync_mut.io.sqlite_sffi` (rt_sqlite_* externs) | Host: yes (emulation/native). SimpleOS: no `rt_sqlite_*` provider in `src/os/` — **unblocked by the file backend fallback below** |
| Storage fallback | `enterprise_store.file_backend` (pure Simple over `rt_file_exists`/`rt_file_size`/`rt_file_read_text_at`/`rt_file_atomic_write`) | Both — `store_open(path)` composes it automatically when sqlite is unavailable; explicit via `store_open_file(path)` |
| Audit hashing | `std.common.crypto.sha256` (pure Simple) | Both |
| Foundation contracts (`enterprise_sale.foundation`) | none (pure Simple, zero imports) | Both |
| Filesystem / env / process / time | **not used** by the library (specs use `std.io_runtime` on the host harness only) | n/a |

Vertical modules audited the same way (W4-B, 2026-08-16):

| Module | Imports | Both-OS status |
|---|---|---|
| `std.enterprise_booking` (`booking.spl`) | `enterprise_store.{store,records}`, `sqlite_sffi.sqlite_row_get`, `enterprise_sale.foundation` | Both — cross-compiles after the audit-hash facade fix below |
| `std.enterprise_restaurant` (`restaurant.spl`) | same as booking + `enterprise_sale.goods_sale` | Both — same |
| `std.enterprise_outbox` (`outbox_worker.spl`) | `enterprise_store.{store,records}`, `sqlite_sffi.sqlite_row_get` | Both — same |
| Audit hashing (`records.spl`) | `enterprise_store.audit_hash` (self-contained pure-Simple SHA-256, SMF-safe) | Both — **finding fixed 2026-08-16**: the previous `std.common.crypto.sha256.sha256_text` import dragged `string_core` slice helpers (`s[a:b]` → CollectionOps) and the sized literal `[0; n]` in `sha256_bytes` (CollectionLiteral) into the closure, so every vertical probe FAILED standalone-SMF cross-compilation. `audit_hash.audit_sha256_hex` is digest-identical (verified vs `sha256_text` on FIPS vectors incl. `abc` and multi-block inputs) and uses only SMF-safe constructs |

### Continuously enforced gate (W4-B)

`sh scripts/check/check-enterprise-cross-os.shs` — fail-closed, verdict last
on stdout (`PASS — <n> probe(s) checked ...` 0 / `FAIL — ...` 1 /
`ERROR — nothing was checked` 2; 0 probes = ERROR). `--selftest` runs before
every scan and is fatal (well-formed fixture must compile both targets; a
deliberately host-only fixture importing a slice-using module must be
rejected with `cannot compile to standalone SMF`). Probe roster (every
`src/app/enterprise/*_probe_main.spl`, each compiled for the host default
target AND `--target=x86_64-unknown-simpleos`, artifact non-empty with
`SMF\0` magic):

- `store_probe_main.spl` — host run prints `enterprise store open=true verify=[]`
- `booking_probe_main.spl` — `enterprise booking probe open=true setup=true status=[]`
- `restaurant_probe_main.spl` — `enterprise restaurant probe open=true setup=true state=[]`
- `outbox_probe_main.spl` — `enterprise outbox probe open=true setup=true pending=0`

Current verdict (2026-08-16, Rust seed):
`PASS — 4 probe(s) checked, each compiles host + x86_64-unknown-simpleos with SMF magic`.
No per-OS fork exists.

### Arch matrix (2026-08-16, lane W4-C)

SimpleOS arch-completeness for the enterprise probe. The compiler's target
table (`src/compiler_rust/common/src/target.rs`) maps six arches to
`TargetOS::SimpleOS`; each was attempted with
`bin/simple compile --target=<arch>-unknown-simpleos src/app/enterprise/store_probe_main.spl -o build/test-artifacts/ent_probe_<arch>`
(Rust seed, `bin/release/x86_64-unknown-linux-gnu/simple`, 59,497,616 bytes,
mtime 2026-08-15 12:46:55Z). Artifact format for PASS rows is an SMF module
(magic `SMF\0`) — a portable Simple module, not a per-arch ELF; the arch
selection still exercises the target-specific codegen path.

| Target triple | Artifact | Verdict |
|---|---|---|
| x86_64-unknown-simpleos | SMF\0, 121,854 B | PASS |
| aarch64-unknown-simpleos | SMF\0, 127,662 B | PASS |
| riscv64-unknown-simpleos | SMF\0, 137,726 B | PASS |
| riscv32-unknown-simpleos | none | BLOCKED (toolchain): `codegen: Unsupported target architecture: Cranelift native builds do not support hosted riscv32 yet; use --backend llvm for this lane` — but the seed's `compile` emits the same error with `--backend llvm` (flag not honored) |
| i686-unknown-simpleos (`x86`) | none | BLOCKED (toolchain): `codegen: Compilation error: Support for this target has not been implemented yet` |
| armv7-unknown-simpleos (`arm`) | none | BLOCKED (toolchain): same Cranelift riscv32-style error for hosted armv7; `--backend llvm` likewise not honored by the seed |

All three BLOCKED rows are toolchain gaps, not enterprise-code defects — the
identical single-codebase probe compiles unchanged on every arch the backend
supports. Host-OS breadth, honestly: evidence exists for linux-x86_64 only
(this host, interpreter-mode specs). macOS/FreeBSD rows are external-host
gates and are NOT claimed; the FreeBSD QEMU wrapper
(`scripts/check/check-freebsd-bootstrap-qemu.shs`) is a bootstrap check, not
an enterprise gate — it is the future lane for a FreeBSD row.

### File backend fallback (2026-08-16, lane W2-A)

`enterprise_store/file_backend.spl` is a pure-Simple append-only store
(one file, `SPLSTORE1` magic line, percent-encoded `table\tcol=val` rows)
behind the SAME `store.spl` API. `store_open(path)` selects it by
composition when `sqlite_open` yields an invalid handle (no rt_sqlite
provider — SimpleOS in-guest); `store_open_file(path)` selects it
explicitly. Raw uow begin/rollback do not undo appends, so the honest
ACID probe reports `acid=false` (same contract as the interpreter sqlite
emulation); atomic multi-write is the `BufferedUow` layer, and each single
insert is whole-file `rt_file_atomic_write`. `store_open_verified`
recognizes a file-backend store by its magic line and never feeds it to
sqlite. Spec: `enterprise_store_file_backend_spec.spl` (6 cases — records
layer unchanged, separator round-trip, buffered all-or-nothing, migration
no-op, restart survival). It deliberately declares its externs locally
(file_ops' `??` TryOperator blocks standalone-SMF cross-compilation).

### Guest-side extern provider (2026-08-16, lane W3-A)

`src/os/userlib/rt_file_facade.spl` (wired into `os.userlib.mod`) now
provides all four externs as `@export("C")` ring-3 wrappers over the
direct file syscalls (`rt_simpleos_file_*_bytes` + close/fsync);
`rt_file_atomic_write` = temp file + fsync + rename. It deliberately does
NOT ride `os.userlib.fs` — that VFS IPC client's `?`/sized-array bodies
are rejected by codegen ("constructs that require the interpreter"), so
the facade declares its externs locally (same precedent as
`file_backend.spl`). Proof at the artifact level: the probe
`src/app/enterprise/rt_file_facade_probe_main.spl` importing the facade
cross-compiles to a SimpleOS SMF artifact carrying all 4 names.

Remaining honest gap for an in-guest RUN: no OVMF boot lane yet builds a
guest image containing `os.userlib.rt_file_facade` or execs an SMF app
(existing lanes boot the ssh_ring3 clang ELF-exec entry); no guest
transcript exists, so AC-17 in-guest execution is still evidence-pending
(cross-compile + guest-owner rows are green).

## Outbox worker — dispatch + reconciliation (W2-F, 2026-08-16)

`std.enterprise_outbox` (sync-tier impl
`src/lib/nogc_sync_mut/enterprise_outbox/outbox_worker.spl`, default-tier
wrapper in `nogc_async_mut/enterprise_outbox/`) drains the store's outbox:

- `outbox_worker_setup(store)` — idempotent migrations for the insert-only
  side tables `outbox_dispatch` and `outbox_retry` (no UPDATE anywhere; a
  dispatch is a NEW row keyed by the outbox row id, pending = rows minus
  dispatch records, filtered in pure Simple).
- `outbox_worker_pending(store, tenant)` — undispatched `OutboxEvent`s
  (`outbox_id`, `event_type`, `payload`) in insertion order. Named
  `outbox_worker_pending` because `records.outbox_pending` (tuple view of
  ALL rows) already owns the shorter name and the interpreter resolves
  same-named imports ambiguously.
- `outbox_dispatch_batch(store, tenant, target, now_epoch, max_batch)` —
  at-least-once delivery to a `DispatchTarget` (composition seam like
  `StoreFaults`: mode = "ok" | "fail_all" | "fail_payload"). Success
  commits the dispatch record atomically WITH an audit-chain entry in one
  unit of work; failure records an `outbox_retry` row and leaves the event
  pending. Exactly-once EFFECT is the consumer's dedup on `outbox_id`.
- `reconcile_report(store, tenant, max_retries)` — data (not prints):
  counts, dead-letter candidates (pending with retries > N), and
  dispatch-without-outbox-row corruption (`orphan_dispatch_ids`).

Spec: `test/01_unit/lib/nogc_sync_mut/enterprise_outbox/outbox_worker_spec.spl`
(8/8; deliberate-red run with the dedup filter sabotaged failed 6/8 first).

## Spec manuals (generated, doc/06_spec)

`enterprise_store_spec`, `enterprise_store_harden_spec`,
`enterprise_store_file_backend_spec`, `outbox_worker_spec`,
`goods_sale_vertical_spec`, `booking_vertical_spec`,
`restaurant_vertical_spec`, `store_app_spec`, `store_web_harden_spec` —
regenerate via `bin/simple spipe-docgen <spec> --output doc/06_spec
--no-index` (0 stubs required; on the Rust seed the subcommand argv-drop
workaround is documented in
`doc/08_tracking/bug/spipe_docgen_subcommand_argv_drop_2026-08-16.md`).
