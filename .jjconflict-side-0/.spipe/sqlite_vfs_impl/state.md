# Lane SQLVFS — SQLite `sqlite3_vfs` from contract to implementation

Status: **survey complete, implementation landed, spec green** (see §5/§6).
Owner paths: `src/os/port/sqlite/**`, `test/01_unit/os/port/sqlite/**`,
one `database:` note line in `doc/08_tracking/os/production_status.sdn`,
`build/sqlvfs_*`.

---

## 1. Step-1 survey — what was contract-only vs. backed by behaviour

`src/os/port/sqlite/sqlite_vfs_contract.spl` (325 lines) is **100% declarative**.
Every one of its 17 `*_report()` functions returns a `VfsMethodReport` string
triple. There is no `extern`, no file handle, no byte moved. Its own header says
so: *"This module is NOT the port. It is the typed target… No live IO."*

So the honest before-state is: **0 of 17 methods backed by real behaviour.**
The contract's `status` column described what the *SimpleOS FsDriver/POSIX
matrix* could support in principle, not what this port did.

### Facility survey (what the OS actually offers today)

| Need | Facility found | Verdict |
|---|---|---|
| byte-level read | `rt_file_read_bytes(path) -> [u8]?` | real, probed OK |
| byte-level write | `rt_file_write_bytes(path, [u8]) -> bool` | real, probed OK |
| size | `rt_file_size(path) -> i64` | real, probed OK |
| durable flush | `rt_file_sync(path) -> bool` | real, probed OK |
| **directory** fsync | `rt_file_sync(<dir>)` returns **true** on a directory | real, probed OK — so `xDelete(syncDir=1)` can be honest |
| exists / delete / rename | `rt_file_exists`, `rt_file_delete`, `rt_file_rename` | real |
| advisory lock | `FileLock` in `src/lib/nogc_sync_mut/database/atomic.spl` | real: `O_EXCL` lockfile + pid-liveness + 2h staleness. **EXCLUSIVE-ONLY** |
| randomness | `rt_random_i64()` | real (`rt_random_bytes` does **not** exist) |
| sleep | `rt_sleep_ms(i64)` | real |
| clock | `rt_time_now_micros() -> i64` | real (`rt_time_now_seconds_f64` does **not** exist) |
| shared mmap | — | absent by design (lane MMAP2) |

Probes live in `build/sqlvfs_probe/p1.spl`, `p2.spl`, `p3.spl`.

### The lock primitive — read, not rebuilt (§4)

`FileLock.for_file(path)` → `.acquire()` / `.try_acquire(ms)` / `.release()`.
Probed: acquire true, a second `FileLock` on the same path `try_acquire(50)` →
**false** (fails closed, no blocking), release removes the lockfile.

**It is exclusive-only.** There is no `LOCK_SH` equivalent. The contract assumed
BSD `flock()` with a real `LOCK_SH`; the primitive that actually exists does not
have one. Rather than write a second locking engine (explicitly forbidden), the
implementation **over-approximates**: `SHARED` takes the same exclusive lock as
`EXCLUSIVE`. This is *safe* (strictly more restrictive — it can never admit a
conflicting pair) and *degraded* (two readers serialize; the loser gets
`SQLITE_BUSY`, which SQLite is required to handle). That trade is recorded on
the method as `partial`, not laundered into `supported`.

### The durability pattern to stay consistent with (§3)

`src/lib/nogc_sync_mut/database/server/durability.spl` + `atomic.spl`:
`atomic_write` = `FileLock` → write `<path>.tmp` → `rt_file_sync(tmp)` →
`rt_file_rename(tmp, path)`. Commit point = the rename.

**Where this VFS follows it:** `xTruncate` uses exactly that tmp+sync+rename
sequence, so a crash mid-truncate leaves the old length, never a torn length.

**Where this VFS deliberately does NOT, and why:** `xWrite` is an *in-place*
read-modify-write, not tmp+rename. Rename-per-page-write would be wrong, not
just slow: SQLite's atomicity mechanism **is** the rollback journal, and it
requires that a db page write land in place so the journal's pre-image remains
the recovery source. Swapping the whole db file under SQLite on every page write
destroys the journal protocol. Durability for `xWrite` comes from `xSync`
(`rt_file_sync`) at the points SQLite chooses. Documented in the module header
so the divergence from the house pattern reads as a decision, not drift.

---

## 2. What got implemented — `src/os/port/sqlite/sqlite_vfs_impl.spl`

A real VFS object over the facilities above. Handle table is **parallel arrays
indexed by handle id**, deliberately: mutating through 2+ field hops loses the
write on the interpreter, so there is exactly one mutable object (`SqliteVfs`)
and no nested-struct mutation anywhere.

Implemented for real, moving real bytes:
`xOpen` `xClose` `xRead` `xWrite` `xTruncate` `xSync` `xFileSize` `xDelete`
`xAccess` `xFullPathname` `xRandomness` `xSleep` `xCurrentTime`
`xSectorSize` `xDeviceCharacteristics` `xFileControl`
`xLock` `xUnlock` `xCheckReservedLock`.

Still fail-closed, unchanged: `xShmMap` `xShmLock` `xShmBarrier` `xShmUnmap`
→ `SQLITE_IOERR_SHM*`. WAL stays gated. Not faked (§4).

Error codes are the real `sqlite3.h` values, including extended codes
(`SQLITE_IOERR_SHORT_READ` = 522, `SQLITE_IOERR_SHMMAP` = 5386, …), so the
numbers are checkable against the amalgamation when it unblocks.

## 3. The durability guard (the reason a VFS is worth having)

The rollback-journal invariant — *the journal is durable before the database
page it protects is overwritten* — is **enforced**, not merely documented.

`SqliteVfs` records an ordered event log (`op`, `path`, `offset`, `length`,
`seq`) and tracks, per journal path, whether it has bytes written since its last
`xSync`. `x_write` to a MAIN_DB handle checks the associated journal
(`<db>-journal`): if that journal has unsynced bytes, the page write is
**refused** with `SQLITE_IOERR` and the violation is recorded. A correct caller
(write journal → `xSync` journal → write page) is unaffected.

`enforce_journal_sync_before_page_write` is a field on the VFS, defaulting true.
Setting it false is the calibration lever used in §5.

## 4. Honest per-method table (before → after)

`before` = the contract's claim, which was backed by nothing.
`after` = what the implementation actually does.

| method | contract said | now | backed by |
|---|---|---|---|
| xOpen | supported | **supported (real)** | handle table + `rt_file_create_excl`/`rt_file_exists` |
| xClose | supported | **supported (real)** | handle release + DELETEONCLOSE + lock release |
| xRead | supported | **supported (real)** | `rt_file_read_bytes` + offset slice, zero-fill + `SQLITE_IOERR_SHORT_READ` |
| xWrite | supported | **supported (real)** | in-place read-modify-write via `rt_file_write_bytes`, hole zero-fill |
| xTruncate | **unsupported** | **supported (real)** | tmp + `rt_file_sync` + rename (house pattern) — contract was wrong, FsDriver was not the only route |
| xSync | partial | **supported (real)** | `rt_file_sync` on the file; FULL also dir-fsyncs the parent |
| xFileSize | supported | **supported (real)** | `rt_file_size` |
| xDelete | (not modeled) | **supported (real)** | `rt_file_delete` + parent `rt_file_sync` when `syncDir` |
| xAccess | (not modeled) | **supported (real)** | `rt_file_exists`, EXISTS/READ/READWRITE |
| xFullPathname | (not modeled) | **supported (real)** | normalizer: abs-ify, collapse `//`, `.`, `..`, strip trailing `/` |
| xRandomness | (not modeled) | **supported (real)** | `rt_random_i64` |
| xSleep | (not modeled) | **supported (real)** | `rt_sleep_ms` |
| xCurrentTime | (not modeled) | **supported (real)** | `rt_time_now_micros` → Julian Day |
| xLock | partial | **partial (real)** | `FileLock`; SHARED over-approximated to exclusive |
| xUnlock | partial | **partial (real)** | `FileLock.release`; EX→SH downgrade is release+reacquire, not atomic |
| xCheckReservedLock | partial | **partial (real)** | lockfile presence; RESERVED indistinguishable from EXCLUSIVE |
| xSectorSize | supported | **supported (real)** | published 512 |
| xDeviceCharacteristics | partial | **partial (real)** | returns 0 — no IOCAP bit is proven, conservative and correct |
| xFileControl | partial | **partial (real)** | SIZE_HINT / HAS_MOVED handled, unknown → `SQLITE_NOTFOUND` |
| xShmMap | unsupported | **unsupported (fail-closed)** | no shared mmap — lane MMAP2 |
| xShmLock | unsupported | **unsupported (fail-closed)** | ditto |
| xShmBarrier | unsupported | **unsupported (fail-closed)** | ditto |
| xShmUnmap | unsupported | **unsupported (fail-closed)** | ditto |

## 5. Spec + deliberate-red calibration

`test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl` — absolute oracles for
read-after-write, short-read, truncate, sync ordering (crash-point style), lock
acquire/conflict/release, `xAccess` on missing files, `xFullPathname`
normalization, and fail-closed for every unsupported method.
Every test uses a **pid+seq-unique temp path** (a shared `/tmp` path caused
FileLock contention across concurrent spec runs today).

Calibration: dropping the journal-before-page ordering
(`enforce_journal_sync_before_page_write = false`) must turn the ordering
tests red, then reverting must return them green. Verdicts recorded in §6.

## 6. Verdicts

### Spec — `bin/simple test test/01_unit/os/port/sqlite/sqlite_vfs_impl_spec.spl`

| run | result | log |
|---|---|---|
| baseline | **35 total, 35 passed, 0 failed** (exit 0) | `build/sqlvfs_jit.log` |
| RED-A (guard dropped in source) | 35 total, 34 passed, **1 failed** | `build/sqlvfs_red_A.log` |
| RED-B (log verdict broken in source) | 35 total, 34 passed, **1 failed** | `build/sqlvfs_red_B.log` |
| after revert | **35 total, 35 passed, 0 failed** (exit 0) | `build/sqlvfs_green_final.log` |
| after the FSK002 named-struct refactor + join fix (§6b) | **35 total, 35 passed, 0 failed** (exit 0) | `build/sqlvfs_final.log` |

Six describe blocks: file IO (5), xTruncate (3), durability ordering (5),
locking (5), namespace methods (10), fail-closed surface (7).

### Deliberate-red calibration — two independent mechanisms, two exact hits

**RED-A.** `x_write`'s ordering guard was disabled at the source
(`if false and self.enforce_… and self.journal_is_dirty(jp)`). Exactly ONE test
went red, and it was the load-bearing one:

> ✗ REFUSES a page write while the journal still has unsynced bytes

Nothing else moved — which is itself the finding: the correct-sequence test and
the crash-point assertions do NOT depend on the guard, so they were not
silently propping it up. Reverted, re-verified 35/35.

**RED-B.** The independent log-based oracle
`journal_before_page_ordering_holds` was broken instead (`if journal_dirty and
false`). Again exactly ONE test went red, and a DIFFERENT one:

> ✗ CALIBRATION: with the ordering guard dropped, the page write succeeds and the log verdict goes FALSE

So the runtime guard and the post-hoc log verdict are genuinely independent:
breaking either is caught, and neither test covers for the other. Reverted,
re-verified 35/35, and `grep` confirms no `if false` / `and false` remains in
the module.

### Direct oracle driver — `build/sqlvfs_probe/drv2.spl`

40 named PASS/FAIL oracles (ordering, crash point, refusal, calibration,
locking, cross-VFS locking, fail-closed, open flags, status counts):
**40 PASS / 0 FAIL**, re-confirmed **40 PASS / 0 FAIL** after the revert.
Logs `build/sqlvfs_drv2.log`, `build/sqlvfs_drv2_interp.log`,
`build/sqlvfs_drv2_post.log`.

### A/B across engines

The two harnesses did not run on the same engine, which is what makes this an
A/B rather than a repeat:

* The **driver** logs `JIT compilation failed, falling back to interpreter:
  unresolved external symbol 'rt_sleep_ms'` — so all 40 oracles executed on the
  **interpreter**.
* The **spec** run contains **no** such fallback line, so it executed on the
  test runner's default (JIT) path.

Same verdicts on both. **Finding worth carrying:** `rt_sleep_ms` is unresolved
in the Cranelift JIT, so any module that merely *declares* it is demoted to the
interpreter wholesale — not just the sleeping function. That is a JIT-coverage
hole affecting far more than this lane; it is why `x_sleep` costs the whole
module its JIT path.

### Durability / ordering evidence (the part that matters)

The crash-point test asserts, at the instant before the page write is issued,
by reading the real filesystem and bypassing the VFS entirely:

* `read_all_bytes(<db>-journal)` == the pre-image, AND
* `read_all_bytes(<db>)` == still the OLD page.

Then the page write is issued and the database becomes the new page, and only
then is the journal deleted with a parent-directory fsync. A power cut anywhere
before that delete leaves a durable pre-image on disk.

The negative half is the stronger evidence: with the journal written but
deliberately NOT synced, `x_write` on the database returns `SQLITE_IOERR` and
`read_all_bytes(<db>)` still shows `OLDPAGE.` — the refusal is real, not
cosmetic. After the journal is synced the identical write is accepted and the
database moves. One violation is recorded.

**Honest limit on this evidence.** The tests prove ORDERING (which bytes are on
the filesystem, in which order, and what is refused). They do NOT prove that
`rt_file_sync` reached the physical platter, because nothing at this layer can
observe a disk controller that lies about its own write cache — the same
non-guarantee `durability.spl` states for the DB server tier. Proving that needs
a real power-cut rig, and is not claimed here.

## 6b. Lint — one finding was a real target bug, not style

`bin/simple lint src/os/port/sqlite/sqlite_vfs_impl.spl` produced three classes:

Re-lint after the fixes (`build/sqlvfs_lint2.log`) confirms the tally for this
file: **FSK002 5 → 0**, COLL006 3 (unchanged, false positives), STUB002 3
(false positives), RAW-RT-001 10 warnings (deliberate). The headline
"Found 58 error(s)" is a whole-dependency-graph total, not this file's.

**FSK002 × 5 — FIXED, and it mattered.** *"entry-closure defect C4: anonymous
tuple return positional members read swapped under freestanding codegen — use a
named struct"* (`doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`).

Five methods returned anonymous tuples: `x_read` `(i64,[u8])`, `x_file_size`
`(i64,i64)`, `x_access` `(i64,bool)`, `x_full_pathname` `(i64,text)`,
`x_check_reserved_lock` `(i64,bool)`. Under freestanding codegen — which is
*precisely the target this VFS exists for* — those members read back SWAPPED, so
`(code, data)` arrives as `(data, code)` and SQLite would read its result code
out of a byte buffer. On the host it would have passed every test in this spec
and failed only on SimpleOS.

Replaced with named structs `VfsReadResult` / `VfsSizeResult` / `VfsBoolResult`
/ `VfsPathResult` (fields `code` + one payload), spec and driver updated. This
is the lane's one genuine near-miss: the tests could not have caught it, only
the lint could.

**COLL006 × 3 — FALSE POSITIVES. I initially mis-read these; correcting the
record.** I first assumed one of the three was `normalize_full_path`'s
`outp = outp + "/" + s` and "fixed" it with `"/" + stack.join("/")`. The
re-lint disproves that: COLL006 stayed at **3 before and after**, and mapping
the reported lines through the +24/+27 line shift the struct block introduced
shows they were always the SAME three functions — `parent_dir_of`,
`bytes_equal`, `filled_bytes`. **None of those three concatenates a string at
all**; they compare a one-char slice or push bytes in a `while` loop. So
"string concat in loop (O(n^2))" is firing on loop-with-indexing, not on
`str = str + x`, and `normalize_full_path` — the one function that genuinely
did concat in a loop — was never flagged.

The join rewrite was kept anyway (it is genuinely O(n) instead of O(n²) and
shorter), and all 9 normalization oracles were re-verified green after it
(`build/sqlvfs_probe/p8.spl`). But it cleared no lint hit, and claiming
otherwise would have been the exact kind of unverified "fixed" this repo's
rules warn about.

**RAW-RT-001 × 7 — NOT fixed, recorded.** *"application code must not declare
raw runtime intrinsic `rt_file_*` directly; use the std wrapper."* `std.io_runtime`
does provide `file_read_bytes` / `file_write_bytes` wrappers, but there is no
wrapper for `rt_file_sync`, which is the single most load-bearing call in this
module — swapping only the two that have wrappers would leave the warning
standing while adding a dependency. Note `atomic.spl`, the house durability
module, declares the same intrinsics directly for the same reason. Left as-is
deliberately; the honest fix is a `std.io_runtime.file_sync` wrapper, which is
not this lane's file to add.

**STUB002 × 3 — false positive, not fixed.** Fires on `sqlite_ok() -> i64: 0`,
`access_exists() -> i64: 0`, `lock_none() -> i64: 0`. All three are named
sqlite3.h constants whose real value IS 0; they are not stubs. `pass_do_nothing`
does not apply to a value-returning function.

## 7. What stays blocked (unchanged by this lane)

* **The SQLite amalgamation build itself.** Still blocked on the C toolchain;
  this lane did not touch it and does not claim it. What this lane delivers is
  the VFS the amalgamation will bind to when it unblocks.
* **WAL mode.** Gated on shared mmap (`MAP_SHARED`/`shm_open`), lane MMAP2.
  `xShmMap` deliberately still fails closed.
* **Reader concurrency.** Needs a shared-mode advisory lock; `FileLock` is
  exclusive-only and building a second locking engine is out of scope (§4).
* **IOCAP flags.** `xDeviceCharacteristics` returns 0 until the block layer
  proves atomic-write / safe-append / powersafe-overwrite.

---

# REDIRECT (2026-07-27): pure-Simple SQL engine found — VFS priority revised

The premise that "SQLite work is blocked on a C toolchain" was too strong.
**SQL itself is not blocked. The C amalgamation is.**

## 8. Survey — `pure_sql`, and which tier is live

**Exactly ONE implementation is live.** The `nogc_async_mut` copy is *not* a
mirror and *not* a fork — it is a single line re-exporting the sync tier:

| Path | Lines | Role |
|---|---|---|
| `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl` | 2,973 | engine |
| `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl` | 1,467 | parsers / expr eval / row codec |
| `src/lib/nogc_sync_mut/database/pure_sql/database.spl` | 8 | re-export of the two above |
| `src/lib/nogc_async_mut/database/pure_sql/__init__.spl` | 1 | `export use nogc_sync_mut...{PureDatabase}` |

The async directory contains **only** `__init__.spl` — no `_PureDatabase/`. So
the usual shadowed-tier trap does not apply: editing the sync copy is correct
and is the only option.

Capability is well beyond the brief's description — besides CREATE/INSERT/
SELECT/UPDATE/DELETE/DROP/WHERE and BEGIN/COMMIT/ROLLBACK it has JOIN, DISTINCT,
LIKE, ORDER BY, LIMIT/OFFSET, aggregates, CASE, scalar functions, ALTER TABLE
ADD COLUMN, INSERT OR REPLACE, UNIQUE indexes with real enforcement, MVCC
snapshots, a typed key API, FTS/BM25 search, and file persistence.

### Spec verdicts (per describe block, seed binary — see §11)

| Spec | Result | Note |
|---|---|---|
| `test/02_integration/storage/dbfs/pure_db_spec.spl` — describe "PureDatabase" | **69 examples, 67 passed, 2 failed** | 2 failures PRE-EXISTING (baseline before any edit: 63/61/2) |
| `test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl` — describe "PureDatabase extended SQL" | **10 total, 9 passed, 1 failed** | unchanged from baseline |
| `test/02_integration/storage/dbfs/db_cache_invalidation_spec.spl` | **6 total, 6 passed** | clean |

Pre-existing failures, NOT caused by this lane and NOT fixed by it:
* `supports parameterized queries` — `semantic: array index out of bounds: index is 0 but length is 0`
* `full SQL feature integration` — `expected 9 to equal 2`
* extended: `persists rows and FTS metadata then rebuilds BM25 search after reopen` — `expected false to equal true`

## 9. Fix — IF NOT EXISTS / IF EXISTS

Root cause: `CREATE TABLE` goes through the real tokenizing `sql_parser.spl`,
which has proper `If`/`Not`/`Exists` tokens — so `CREATE TABLE IF NOT EXISTS`
always worked (an existing green test proves it). But `CREATE INDEX`,
`DROP INDEX` and `DROP TABLE` are handled *before* the parser by bespoke
string-splitting helpers in `row_value_helpers.spl`, and those never learned the
guard clause. `_parse_create_index` sliced off `"CREATE INDEX"`, then read the
remaining `"IF NOT EXISTS idx ON t (c)"` positionally: `parts[0]`→`"IF"` as the
index name, `parts[1]`→`"NOT"` ≠ `"ON"`, so it returned `[]` and the statement
fell through to the tokenizing parser, which rejects it.

Three defects of the same family, all fixed:
1. `CREATE [UNIQUE] INDEX IF NOT EXISTS` — was rejected outright.
2. `DROP INDEX IF EXISTS` — the guard was never stripped, so `"IF EXISTS foo"`
   became the index name and lookup failed.
3. `DROP TABLE IF EXISTS` — the guard *was* stripped but the flag was discarded,
   so a missing table still errored.

Parser return shapes changed (`_parse_create_index` now returns
`[is_unique, if_not_exists, name, table, cols...]`; `_parse_drop_index` and
`_parse_drop_table` now return `[if_exists, name]` instead of a `""` sentinel),
and `_do_create_index` / `_do_drop_index` / `_do_drop` take the flag and return
`Ok(0)` instead of `Err` on the no-op path — matching SQLite. Each has exactly
one call site, all updated.

### Calibration (deliberate red)

Guards disabled in place (`if false:`), specs unchanged → **69 examples, 5
failures**: exactly the 3 new IF-NOT-EXISTS tests flipped red
(`supports CREATE INDEX IF NOT EXISTS`, `supports CREATE UNIQUE INDEX IF NOT
EXISTS and still enforces uniqueness`, `supports DROP INDEX IF EXISTS`) on top
of the 2 pre-existing. Guards restored → back to 67/2. The 3 negative-guard
tests (duplicate name, unknown table, unknown column) stayed green under the
break, which is correct — they are regression guards, not bug detectors, and the
calibration proves they cannot mask the bug.

Absolute oracles used (not "no error"): the index must really exist after a
repeat `IF NOT EXISTS`, so `DROP INDEX` must succeed exactly once and fail the
second time; `IF NOT EXISTS` must not weaken a UNIQUE constraint, so a duplicate
insert must still be rejected and row counts must be exact.

## 10. This does NOT unblock `UiAccessStore` — the blocker is a different engine

`src/lib/nogc_sync_mut/ui/access_store.spl` imports
`std.database.sql.connection.{Database}`. That `Database` is an **SFFI wrapper
over C SQLite** (`std.io.sqlite_sffi` → `sqlite_open`/`sqlite_execute`/...), and
under the seed it lands on the Rust shim that lane UIQUERY found only implements
CREATE TABLE / DELETE / INSERT. It does **not** touch `pure_sql` at all.

So the pure_sql fix is correct and worth having on its own merits, but the
honest statement is: `UiAccessStore` is unblocked by either pointing it at
`PureDatabase` (it needs no C library, and pure_sql supports every statement in
`_init_schema`) or by fixing the shim. Both are outside this lane's owned paths
(`src/lib/nogc_sync_mut/ui/**`, `src/compiler_rust/**`). Recommended: point it
at `PureDatabase` — that is the whole point of having a pure engine.

## 11. Revised view — what the VFS is actually for

The VFS work already landed and verified in §1–§7 stands and is kept. But its
value is **contingent on the C amalgamation ever being built**, because a
`sqlite3_vfs` is by definition an interface *that C SQLite calls*. Nothing else
calls it. With no amalgamation, no byte reaches it in production.

Meanwhile the durable-storage path that actually runs in-guest today is
`pure_sql` (`_persist`/`_load_from_disk`/`checkpoint`) plus `atomic.spl` /
`FileLock`. **That** is where journal-before-page ordering, sync reaching
durable media, and lock-conflict behaviour actually matter, and it is reachable
now. Priority is therefore inverted from the original brief: harden the pure_sql
durability path before implementing more `sqlite3_vfs` methods.

Concretely, on the pure_sql path (next work, NOT claimed done):

* **CONFIRMED DEFECT — `_persist()` is not atomic and not durable.** It is
  literally `if file_write(self._path, self._serialize_disk())`. That is a plain
  whole-file overwrite: **no `FileLock`, no `.tmp`, no `rt_file_sync`, no
  rename** — it does not use the house `atomic_write` pattern from
  `atomic.spl`/`durability.spl` at all, and `file_ops.file_write` is its only
  storage import. Consequences: a crash mid-write leaves a **truncated,
  half-serialized database file** and the previous good copy is already gone, so
  this is not "lose the last transaction", it is "lose the whole database";
  `_load_from_disk` would then fail the `simple-pure-db-v1` header/format check
  and the data is unrecoverable. There is also no cross-process exclusion, so
  two processes persisting the same path interleave. This is the single highest-
  value durability fix available on the reachable path, and it is strictly more
  important than any remaining `sqlite3_vfs` method — the VFS enforces careful
  journal-before-page ordering for a C library that cannot be built, while the
  engine that actually runs overwrites its own database in place.
* No journal at all in pure_sql: `_snapshot_tables`/`_restore_from_snapshot` are
  **in-memory** rollback. A crash between `COMMIT` and `_persist` loses the
  transaction with no recovery record.
* Lock conflict behaviour on the database file across processes is unverified.

## 12. Caveats on this evidence

* **Binary identity:** `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
  which prints *"this Rust-built Simple binary is a bootstrap seed only"*. All
  verdicts above are **SEED** verdicts. Re-verify on the self-hosted binary.
* **A/B disagreement, engine landmine:** `bin/simple run` (JIT) mis-reads
  `Result` from `PureDatabase.exec_sql` — a probe reported `is_ok=false` even for
  a plainly-successful `CREATE TABLE`, both when the `Result` was passed to a
  helper `fn` and when it was bound to an intermediate `val`. The test runner,
  which has a credible 61-passing baseline using exactly the
  `val r = ...; expect(r.is_ok())` pattern, is the trustworthy oracle here. Do
  not calibrate this engine with `bin/simple run` probes. Consistent with the
  standing "neither engine trustworthy" note.
* **Lane collision:** `.spipe/pure_sql_hardening/` (lane PURESQL) is surveying
  the same engine and reached the same one-live-tier conclusion. Its state file
  was created while this work was in flight. Coordinate before landing —
  overlapping edits to `pure_sql/**` are likely.
* No commits made. `.git/index.lock` was held by another process throughout;
  it was left alone (not deleted) per the VCS rule.
