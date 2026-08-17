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
- **Native-ACID status: UNBLOCKED (measured 2026-08-17, lane W10-C).**
  `sh scripts/check/check-sqlite-backend-acid.shs` now prints
  **`ACID — rollback removed the row, UNIQUE violation rejected`** (exit 0) on
  this host. The W9-B analysis below was correct in every particular; its one
  prerequisite has now been implemented. Read this block first, then W9-B for
  the reasoning that got here.

  **What was wrong, and where it was fixed:**
  1. *Link line (Rust seed — flagged as a deliberate seed edit).* The
     single-file `--native` path links the archive from
     `build_core_c_runtime_library`, i.e. `include_stage4_hosted = false`, which
     deliberately omits `runtime_sqlite.c`; and the Linux platform default
     library list (`common/src/platform/link_config.rs:301`) carries no
     `-lsqlite3`. Hence `codegen: undefined symbol: rt_sqlite_open`. This had to
     land in the seed: `bin/simple` is the Rust seed, and the pure-Simple
     equivalent (`src/compiler/70.backend/linker/_LinkerWrapper/`, which *does*
     already list `-lsqlite3`) is never reached by `compile --native`. Fix:
     `linker/native_binary/linker.rs` gained `object_requires_sqlite` (an
     UNDEFINED-symbol test mirroring `is_sqlite_runtime_symbol`) and, only when
     it fires, adds an on-demand `runtime_sqlite.o` plus `-lsqlite3`;
     `native_project/tools.rs` gained `build_sqlite_runtime_object` to compile
     that one translation unit with flags identical to the archive members.
     Ordinary native binaries are unaffected and acquire no `libsqlite3`
     dependency.
  2. *Tagging convention (C runtime — `src/runtime/runtime_sqlite.c`).* Once it
     linked, the file turned out to have **never been exercised**: it tagged
     every integer (`v << 3`) and returned `SPECIAL_TRUE`/`SPECIAL_FALSE`
     (11/19), but `sqlite_sffi.spl` declares these as `extern fn ... -> i64`
     and the native codegen passes scalars RAW. So `column_count` returning 1
     was read as 8, `query_next` as 11, `while has_row == 1` never entered, and
     **every query returned zero rows**. `from_int`/`as_int` are now identities
     and `query_next` returns 1/0. Pointer and string values keep their tagging
     and were always correct.

  **Still broken, do not use as evidence: `sqlite_count`.** It does
  `int(count_str)` on a runtime-produced string and gets the ASCII code of the
  first digit — an empty table counts **48**, a one-row table **49**. Verified
  the same day that `int("142")` on a *literal* correctly yields 142, so the
  defect is in `int()` over an `rt_string`, not in sqlite. Note this also
  retires W9-B's reading of `start_count=48` as "a global emulation counter":
  it was ASCII `'0'` all along. The probe therefore reads presence as TEXT via
  `sqlite_query_value`, whose path is sound.

  **The gate now carries real atomicity evidence, and cannot pass vacuously.**
  `test/fixture/enterprise_store/sqlite_acid_probe.spl` asserts that a rolled
  back INSERT leaves no row and that a UNIQUE violation is rejected — the two
  assertions W9-B rightly refused to write under the emulation. Both are
  guarded by a **non-vacuity precondition** checked first: the probe must show
  `in_tx_row1=[alpha]` and `committed_row2=[beta]`, i.e. writes and reads
  demonstrably work, or the script reports `BLOCKED — probe is vacuous` rather
  than crediting an ACID verdict to a backend that simply never writes.
  Discrimination was confirmed by running the identical probe through the
  interpreter emulation, which produces `after_rollback_row1=[alpha]` and
  `dup_insert_ok=true` — a NONACID reading. The native result was additionally
  cross-checked out-of-band with CPython's `sqlite3` reading the same file:
  a real `sqlite_autoindex_t_1` UNIQUE index, `alpha` absent, `beta` present.

  **Scope limit — the specs still run on the emulation.** `bin/simple test`
  executes in the interpreter, so `enterprise_store_spec` (10/10),
  `enterprise_store_harden_spec` (5/5) and `goods_sale_vertical_spec` (10/10)
  stay green and correctly see `store_backend_acid == false`. Real SQLite is
  reachable today only through an AOT `--native` binary.

  **Refined blocked row — `store_backend_acid` is false even natively, and it
  is not sqlite's fault.** Measured 2026-08-17 in an AOT `--native` binary,
  every primitive `probe_backend_acid` uses is correct end to end:
  `store_count_text` before=`[0]`, `sqlite_begin` true, `store_insert2` true,
  mid=`[1]`, `sqlite_rollback` true, after=`[0]` — run by hand that is exactly
  `before == after` returning **true**. Yet `store_open()` reports
  `acid=false` with `is_file=false`, i.e. a genuine sqlite connection, not the
  file-backend fallback. The defect is therefore inside `store_open`'s in-situ
  call to `probe_backend_acid` (`store.spl:103`, `:135-143`). Leading suspect:
  the state `store_open` establishes immediately before it — the WAL pragma,
  the `CREATE TABLE` batch, and the `marker_present` / `store_insert2` marker
  write, which may leave a statement unfinalized so the probe's `BEGIN`
  behaves differently from the clean standalone sequence. Next step:
  instrument those three values inside `probe_backend_acid` under `--native`
  and diff against the known-good sequence above. The store stays insert-only
  with pure-Simple filtering until that resolves.

- **Native-ACID status (VERIFIED BLOCKED, measured 2026-08-16, lane W9-B) — superseded by the W10-C block above, retained for its reasoning).**
  The earlier text here stated a resume condition — run the specs
  `--mode=native` — as though `--mode=native` were the missing ingredient. It
  is not, and following it would have produced *false* native evidence. What
  was actually measured on this host (`bin/simple` = the Rust seed,
  `bin/release/x86_64-unknown-linux-gnu/simple`, 59497616 bytes, 2026-08-15,
  whose own `--version` prints the "bootstrap seed only" warning):

  1. **`--mode=native` does not reach real SQLite.** An ACID probe
     (create table with `PRIMARY KEY`/`UNIQUE NOT NULL`, `begin`, insert,
     `rollback`, count; then a deliberate duplicate insert) produces
     **byte-identical non-ACID output under `--mode=native` and under the
     default interpreter**: `start_count=48` on a freshly deleted db file
     (a global emulation counter, not this file's rows),
     `in_tx_count=49` -> `after_rollback_count=49` (**rollback did nothing**),
     and `dup_insert_ok=true` (**UNIQUE not enforced**). `--mode=native` is
     in-process JIT; its externs resolve to the same Rust emulation table
     (`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`, where
     e.g. `rt_sqlite_begin_fn(_args)` ignores its argument entirely).
  2. **Real SQLite is physically absent from the seed process.**
     `ldd $(readlink -f bin/simple) | grep -i sqlite` -> nothing; no
     `rusqlite`/`libsqlite3-sys` in any `src/compiler_rust` `Cargo.toml`. No
     mode flag can make an unlinked library appear.
  3. **`--mode=native` on this module silently degrades to the interpreter
     anyway.** Running `store_open` + `store_backend_acid` with
     `--mode=native` emits
     `[jit-fallback] unresolved external symbol 'store_open': whole module
     dropped to the interpreter` and
     `[INFO] JIT compilation failed, falling back to interpreter`. So a
     `--mode=native` spec run of the enterprise store **is an interpreter run
     wearing a native label** — do not record it as native evidence.
     `store_backend_acid` correctly returns **`false`** there; the honest
     probe holds under both modes.
  4. **The AOT path is the right route and is blocked one step earlier.**
     `bin/simple compile <src> -o <out>` emits an `SMF` bytecode module
     (magic `S M F \0`), not an ELF, so it re-enters the same interpreter.
     `bin/simple compile <src> --native -o <out>` does build an ELF, and is
     the only path whose linker knows about sqlite
     (`pipeline/native_project/linker.rs:1534` and `tools.rs:1317` pass
     `-lsqlite3`) — but for a single-file `--native` compile it fails with
     **`error: codegen: undefined symbol: rt_sqlite_open`** (a real lld
     error parsed by `linker/native.rs:628` and re-prefixed `codegen:`). The
     link line for single-file `--native` includes neither
     `src/runtime/runtime_sqlite.o` nor `-lsqlite3`; that wiring exists only
     in the separate `native_project` pipeline.

  The host is otherwise ready: `libsqlite3.so`/`libsqlite3.a` and
  `/usr/include/sqlite3.h` are installed, `src/runtime/runtime_sqlite.c`
  `#include <sqlite3.h>` (real header, not a shim), and
  `sh scripts/build/build_simple_runtime_sqlite_sffi.shs` builds the provider
  cleanly to `build/sffi/libsimple_runtime_sqlite_wm.so` with its own
  `rt_sqlite_open`/`rt_sqlite_query_next` presence assertions passing.
  Staging that provider does **not** fix the `--native` link (retried; same
  undefined symbol) because the single-file link line never references it.

  **Concrete prerequisite (one change, not an environment wish):** make the
  single-file `compile --native` link line include the compiled
  `src/runtime/runtime_sqlite.c` object (or the staged
  `libsimple_runtime_sqlite_wm.so`) plus `-lsqlite3`, exactly as
  `native_project/linker.rs` already does when it detects an
  `rt_sqlite_*`/`sqlite3_*` undefined symbol
  (`is_sqlite_runtime_symbol`, linker.rs:500). Until then, real
  rollback-atomicity and real constraint-rejection assertions **cannot be
  written honestly** — under the emulation both would pass vacuously
  (rollback is a no-op that leaves the row, and a UNIQUE violation returns
  success), which is the precise reason the store is insert-only with
  pure-Simple filtering and why `acid=false` is recorded rather than assumed.
  Verification is mechanised — do not re-derive it by hand:
  `sh scripts/check/check-sqlite-backend-acid.shs` builds
  `test/fixture/enterprise_store/sqlite_acid_probe.spl` via
  `compile --native` and prints one of `ACID` (exit 0) / `NONACID` (exit 1) /
  `BLOCKED` (exit 2) as its last line. It gates nothing; it only answers
  whether this host reaches real ACID SQLite. **Today it prints
  `BLOCKED — AOT native build failed: error: codegen: undefined symbol:
  rt_sqlite_open`.** When it flips to `ACID`, the rollback-atomicity and
  constraint-rejection specs become writable and this section must be
  rewritten with their verdicts.

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

### In-guest execution — CLOSED (W10-B, 2026-08-17)

AC-17 in-guest execution is no longer evidence-pending. Under real OVMF
pflash -> GRUB-EFI -> multiboot1 (never `-kernel`, never isa-debug-exit),
against an EMPTY `mkfs.vfat` FAT32-on-NVMe volume, the whole file backend
(`fb_open` -> `fb_insert` -> `fb_count` -> `fb_is_store`) runs inside
SimpleOS. All six rungs of
`scripts/check/check-enterprise-store-in-guest-ovmf.shs` pass; retained
transcript
`doc/09_report/2026/ent_store_in_guest_ovmf_l4_2026-08-17.serial.log`:

    [ent-store] head read-back=SPLSTORE1
    [ent-store] facade write+read-back=OK
    [ent-store] open=OK
    [ent-store] insert=OK
    [ent-store] count=2 OK
    [ent-store] magic=OK
    enterprise store open=true verify=[] (file-backend, in-guest FAT32)

#### Why two of the four externs are provided in C, not Simple

The last blocker (rung L4) was a link-graph defect worth remembering, and
it is the reason the kernel-tier facade is deliberately SPLIT across two
languages. `nm` on the failing kernel showed the split precisely:

| symbol | resolved to | outcome |
|---|---|---|
| `rt_file_atomic_write` | facade `@export("C")` | correct |
| `rt_file_read_text_at` | facade `@export("C")` | correct |
| `rt_file_exists` | `NOP1` stub in `boot/rt_extras.c` | always false |
| `rt_file_size` | `TRAP_STUB_RET` in `boot/baremetal_stubs.c` | would halt the CPU |

Two independent causes stacked:

1. **Link order under `-z muldefs`.** The freestanding link passes
   `-z muldefs` (`pipeline/native_project/linker.rs`), so a Simple
   `@export("C")` provider and a hand-written C stub of the same name are
   BOTH strong definitions and do not collide — the first in link order
   silently wins, and the boot C objects precede the Simple module
   objects. (`@export` does keep the unmangled name: `mangle.rs`'s
   `keeps_abi_name`.)
2. **ABI.** `rt_file_exists` and `rt_file_size` are in codegen's
   `text_arg_indices` table (`codegen/instr/calls.rs` and its LLVM twin),
   so every Simple call site lowers `rt_file_exists(p)` into
   `rt_file_exists(rt_string_data(p), rt_string_len(p))` — a raw
   (ptr, len) pair. A Simple provider `fn rt_file_exists(path: text)`
   takes ONE boxed RuntimeValue and would receive the raw data pointer
   instead, so it is unfixable at the Simple layer regardless of who wins
   the link. `rt_file_read_text_at` and `rt_file_atomic_write` are NOT in
   that table (nor in `boxed_text_arg_indices`, which holds only
   `rt_string_builder_push`), pass boxed values, and are correctly
   provided by the Simple facade.

So `rt_file_exists`/`rt_file_size` are now real C definitions in
`boot/baremetal_stubs.c` over the FAT32-on-NVMe API, with the (ptr, len)
signature their call sites emit; the two competing stubs were deleted, so
each name has exactly ONE definition and no longer depends on link order.
The facade declares them `extern fn` instead. `file_backend.spl` was NOT
changed — its local extern declarations remain correct, and the recorded
reason for them (importing the io facade drags `?`-TryOperator readers
that break standalone-SMF cross-compilation) still holds; the cross-OS
gate still passes 8/8.

Generalisation of the defect class first recorded for `mmio_read8`: an
`extern fn` declared in a `.spl` file binds to the same-named C symbol,
never to a same-named Simple module function — and a Simple
`@export("C")` competing with a C stub of the same name is decided
silently by link order, not by an error.

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
