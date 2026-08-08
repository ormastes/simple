# Lane DBDUR — Simple DB server tier, increment 2: durable commit

Date: 2026-07-27
Predecessor: `.spipe/db_server_tier/state.md` (lane DBTIER, increment 1)
Scope: roadmap Phase 6 blocked row "full Simple DB server tier" — durability only.

## 1. The defect this increment closes

Increment 1 shipped an **in-process model**: `sys_commit` called `txn_commit`,
which replayed the session overlay into the in-memory `SdnDatabase` tables and
returned `OK applied=N`. `save()` was never called. A process that died one
instruction after the `OK` lost the write completely, and a client that read
the `OK` had been told something untrue.

## 2. What was built

| File | Role |
|---|---|
| `src/lib/nogc_sync_mut/database/server/durability.spl` (NEW, ~300 L) | the durability contract (module docstring), the commit pipeline, undo pre-images, the fault-injection points, and the on-disk oracle |
| `src/lib/nogc_sync_mut/database/server/server.spl` | `DbServerCapsule` gained a `durability: DurabilityPolicy` port; `sys_commit` now persists before it acknowledges |
| `src/lib/nogc_sync_mut/database/server/protocol.spl` | two error codes: `durability`, `crashed` |
| `test/system/database/server/db_durability_spec.spl` (NEW) | 16 examples across 4 describe blocks |

**No second storage or locking engine** (§4 of the increment-1 ledger). The
durable write is `SdnDatabase.save()`, which is `atomic_write()` from
`std.database.atomic`: `FileLock` (O_EXCL + pid liveness) around
temp-file -> `rt_file_sync` -> `rt_file_rename`.

## 3. The durability contract (as written into durability.spl)

The commit pipeline, with the **commit point** at the rename inside P4:

```
P1 precheck   optimistic version check over the whole overlay
P2 undo       snapshot the pre-image of every key the overlay touches
P3 apply      overlay -> in-memory tables
P4 persist    SdnDatabase.save() == FileLock + temp + fsync + rename
P5 ack        OK applied=N goes back to the client
```

**Guaranteed once COMMIT returns OK:** every write of that transaction is in
the database file on durable media, and a fresh `SdnDatabase.load(path)` — in
this process or in a new one after a power cut — observes ALL of them.
All-or-nothing, because the durable step is a single whole-file rename.

**When COMMIT returns ERR:** nothing of the transaction is durable, and the
in-memory store has been returned to its last durable state.

**A reader mid-commit** never sees a torn mixture. In-process, the capsule
serves one message at a time, so a peer only observes the store between
commits. Cross-process, a reader takes the SAME `FileLock` on the SAME path and
the visible swap is `rename(2)`; the half-written bytes only ever exist at
`<path>.tmp`, which no reader opens; and the crc32 header makes a torn file
that somehow reached `<path>` load as `nil` rather than parse into a half-new
state.

**Stated non-guarantees (do not let these get quietly dropped):**
- `SdnRow._version` is NOT durable — `SdnTable.to_sdn()` serializes declared
  columns only, so versions restart at 0 after a reload. The optimistic-version
  check protects a process lifetime, not a restart. (Follow-up, §7.)
- A field whose column is not in `SdnTable.columns` is NOT durable.
- Durability is per-COMMIT, not per-PUT.
- "Durable" = fsync before rename. It says nothing about a lying disk cache.
- A crash after P4 and before P5 leaves the data stored while the client is
  told nothing: this tier is **at-least-once** at the connection level. A
  client that reconnects MUST re-read; a retry is not free. Making it
  idempotent needs a commit id in the protocol — NOT done here.

### Why the WAL is deliberately not the commit point

`std.database.wal` has entry types Insert/Update/Delete/Checkpoint and **no
transaction-boundary record**. A multi-write transaction appended entry by
entry is therefore torn by a crash mid-append: replay would resurrect a prefix
of a transaction that never committed. Making the WAL the commit point needs a
Begin/Commit marker in `wal.spl`, which this lane does not own. The WAL keeps
its existing role (checkpointed by `save()`), and whole-file atomic rename is
the commit point. Recorded as a reason, not an oversight.

## 4. Crash-point matrix (all verdicts from a FRESH load off disk)

| # | Injected failure | On-disk state after restart | Client saw | Verdict |
|---|---|---|---|---|
| 1 | `before_persist` — die after P3, before `save()` | OLD everywhere (`name=old`; no new key leaked) | nothing | PASS |
| 2 | `mid_persist` — die between writing `<path>.tmp` and the rename | OLD everywhere; `<path>.tmp` exists and is ignored; `<path>` still loads | nothing | PASS |
| 3 | `after_persist` — die after the rename, before the ack | NEW everywhere (`name=new`) | nothing | PASS (this is the at-least-once gap, made explicit) |
| 4 | `persist_fails` — `save()` returns false, process survives | OLD on disk AND in memory (`GET` returns `old`) | `ERR code=durability` | PASS |
| 5 | `persist_fails` on an INSERT | key absent on disk and in memory (`GET` -> `code=not_found`) | `ERR code=durability` | PASS |
| 6 | torn file forced into `<path>` | `load()` returns nil — refuses rather than reads a mixture | n/a | PASS |

No row produced a torn mixture. Every expected value is absolute
(`"old"` / `"new"` / `"<absent>"`), read by `durable_value()`, which does a
fresh `SdnDatabase.load` and never consults the running server's memory.

## 5. Deliberate-red calibration (mutants applied, run, reverted)

| Mutant | Injected violation | Red tests | Survivors |
|---|---|---|---|
| M1 | acknowledge before persisting (`return durable_ok(...)` inserted immediately before P4) | **12 of 16** — all 5 "acknowledged commit is permanent", all 6 crash-point rows, and "reports a durable commit as persisted" | only the 2 in-memory-only examples, which persist nothing by design |
| M2 | persist failure ignored (return OK, skip `restore_undo`) | exactly the 2 rollback rows (#4, #5 above) | 14 |
| M3 | mid-persist crash renames the torn bytes over `<path>` instead of leaving them at `<path>.tmp` | exactly the mid-persist row (#2) | 15 |

Each mutant was reverted and the suite re-verified green in both engines.

## 6. Verification

```
bin/simple run test/system/database/server/db_durability_spec.spl
  5 examples, 0 failures    (acknowledged commit is permanent)
  6 examples, 0 failures    (crash-point matrix)
  2 examples, 0 failures    (increment-1 guarantees unchanged)
  3 examples, 0 failures    (durability is reported, never assumed)

SIMPLE_EXECUTION_MODE=interpreter bin/simple run <same>   — same 4 lines
```

### Findings handed to lane DBTIER (NOT caused by this increment)

- `test/system/database/server/db_server_tier_spec.spl:114`
  `assert_nil(store_read(store, "users", "ghost"))` **fails under
  `bin/simple run` in BOTH engines** with `assert_nil failed: got
  Option::None` — i.e. the value is correct and the matcher rejects a typed
  `Option::None`. Proven independent of this lane with a standalone probe
  built with `durability_off()`; the failing `it` never issues a COMMIT, so
  `durable_commit` is not on its path. `assert_false(found.?)` on the same
  value passes. Workaround for DBTIER: assert `.?` rather than `assert_nil`.
  The runner aborts the file at that point, so the rest of the increment-1
  spec is unobserved under `run`. The two properties most exposed by the
  `sys_commit` rewrite (optimistic conflict, peer isolation) are re-covered in
  this lane's spec instead.

  **UPDATE 2026-07-28 (lane DBHANG closed this).** The hang is fixed and
  `db_server_tier_spec.spl` runs 30/30, so the compensation motive is gone.
  Lane DBHANG §6 offered to revert the two re-covered examples. **Reviewed and
  DECLINED — they stay.** They are not duplicates: the tier spec builds its
  server with `DbServerCapsule.new(...)` (no durability port) and asserts only
  against the in-memory `server.store` and its own GET path — it never re-reads
  the file. §3's "the transaction guarantees are unchanged" pair is the only
  place either property is checked against `on_disk()` (a fresh
  `SdnDatabase.load`): that a conflict-rejected COMMIT leaves the loser's write
  off disk, and that an uncommitted peer write is absent from disk. The tier
  spec is at least as strong on the in-memory half (it adds an unconditional
  control and a deliberate-red calibration) and strictly weaker on the disk
  half. Deleting them would drop real coverage. Rationale recorded in the
  `@manual_section` header above the describe block so it is not re-proposed.
- `make_store()` in the increment-1 spec uses the SHARED path
  `/tmp/dbtier_spec.sdn`. Now that COMMIT really writes, two concurrent runs
  of that spec contend on `FileLock` (5-minute acquire timeout). DBTIER should
  give each run a unique path; this lane's spec already uses one file per
  scenario under `build/dbdur_*`.

## 7. Remaining steps

`.spipe/db_server_tier/state.md` had no §5 when this lane read it (it ends at
"## 4. Results", unfilled), so this ordering is reconstructed from the lane
brief. Durability was step 1 and is done.

1. ~~Durability — commit persists through the store under `FileLock`.~~ DONE.
2. **Listener / accept loop.** There is still no listener: `serve()` drains one
   in-memory `MemoryTransport`. Needs a real socket port and a connection
   accept loop. When it lands, the "in-process, one message at a time" half of
   the mid-commit visibility argument stops being free — a concurrent reader
   could observe the window between P3 and P4. That obligation is recorded in
   the durability docstring and must be discharged by the listener increment,
   not assumed.
3. **Concurrency primitive.** No lock/latch guards the capsule's own state;
   `SessionRegistry` and the store are single-threaded by assumption.
4. **Auth handshake.** `OPEN as=<principal>` still trusts the claimed
   principal. Capability lookup is deny-wins, so an unknown principal gets an
   empty capability, but a KNOWN principal can be impersonated by name.
5. **Multi-row / range operations.** GET/PUT/DEL are single-row only. No scan,
   no predicate, no batch.
6. **Snapshot isolation.** Currently read-committed with a per-session write
   overlay and a commit-time optimistic version check. Read skew is possible.
7. **Durable row versions (opened by this increment).** `_version` is not
   serialized by `SdnTable.to_sdn()`, so the optimistic check resets across a
   restart. Either persist `_version` as a real column or move the conflict
   check onto a durable token. Needs `core.spl`, which is not this lane's.
8. **Idempotent commit ids.** Required to close the at-least-once gap in §3.

## 8. Files

- `src/lib/nogc_sync_mut/database/server/durability.spl` (new)
- `src/lib/nogc_sync_mut/database/server/server.spl` (durability port + `sys_commit`)
- `src/lib/nogc_sync_mut/database/server/protocol.spl` (2 error codes)
- `test/system/database/server/db_durability_spec.spl` (new, 16 examples)
- `doc/08_tracking/os/production_status.sdn` — the one `database:` note line
