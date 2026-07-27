# Lane DBTIER — Simple DB server tier, increment 1

Date: 2026-07-27
Scope: roadmap Phase 6 blocked row "full Simple DB server tier"
(ledger `database:` = partial, "server tier absent").

## 1. Survey (done BEFORE coding)

### What already exists (embedded store)
`src/lib/nogc_sync_mut/database/` — the SDN embedded store, ~30 modules:

| Module | Provides |
|---|---|
| `core.spl` (636 L) | `StringInterner`, `SdnRow` (`Dict<text,text>` + `_version`), `SdnTable` (rows + pk index, `insert/update_row/update_row_if/get_row/mark_deleted/valid_rows`), `SdnDatabase` (path, `Dict<text,SdnTable>`, interner, `modified`, optional WAL/metrics, `load`/`save`/`get_table`/`get_table_mut`/`set_table`) |
| `atomic.spl` (337 L) | `atomic_read/write/write_batch/append`, `FileLock` w/ pid liveness |
| `wal.spl` (260 L) | `WalEntry`, `WriteAheadLog.open/append/pending_entries/replay`, row<->payload codec |
| `index.spl`, `fts.spl` | secondary + trigram indexes |
| `query.spl` (401 L) | in-memory row filter/select surface |
| `compaction.spl`, `checker.spl`, `stats.spl`, `db_metrics.spl` | maintenance |
| `simple_db_if/storage_api.spl` | traits `PageStore`/`BufferManager`/`WalWriter`/`Checkpointer`/… (page-level contract, unused by the SDN store) |
| `database/sql/**` | SQLite **client** side (pool/connection over FFI) — different product, out of scope |
| `src/os/services/database/simple_db_service.spl` | a single-process HTTP-ish request stringifier, no sessions/txn/capability. NOT owned by this lane (`src/os/services/**` excluded). |

### Verdict: the store CAN support a server tier without refactoring
`SdnDatabase` is an in-memory table map with an explicit `save()` boundary and
per-row `_version` optimistic locking. That is enough to build session-scoped
transactions **above** it as a write overlay. No second storage engine needed.

### Gap analysis — what a server tier must own (none of it exists today)
1. **Connection lifecycle** — open/close, session identity, resource release.
2. **Session state** — which principal, which capability, which open txn.
3. **Request framing** — a wire message -> typed request; malformed must be
   *rejected*, never crash the loop.
4. **Transaction scoping** — per-session begin/commit/rollback, and *isolation*:
   session A's uncommitted writes invisible to session B.
5. **Access control** — capability-checked, deny-wins, per table+op.

The embedded store owns: storage, durability, indexes, query evaluation.
The server tier owns items 1-5 and NOTHING of storage.

## 2. Design (MDSOC+)

Placement: `src/lib/nogc_sync_mut/database/server/` (same tier as the store).

### MDSOC outer capsule
`DbServerCapsule` (`server.spl`) — the only object that touches the outside
world. Owns ports:
- **transport port** — `DbTransport` trait, shaped exactly like the established
  `std.mcp_sdk.transport.transport.Transport` (`read_message/write_message/close`).
  We deliberately mirror that shape rather than inventing a parallel IPC idea; a
  direct import of mcp_sdk from the database tier would invert the dependency
  (db -> mcp), so the trait is restated with an adapter note and an in-memory
  `MemoryTransport` for specs (BufferTransport-equivalent).
- **store port** — the existing `SdnDatabase`. Never bypassed.
- **policy port** — `CapabilityTable`.

### ECS business layer
- Entity  = `SessionId` (i64).
- Components (parallel `Dict<i64, _>` stores in `SessionRegistry`):
  `SessionIdentity` (principal, open flag), `SessionCapability`, `SessionTxn`
  (open flag + write overlay + tables touched).
- Systems (pure functions over the registry + request):
  `sys_open`, `sys_auth_check`, `sys_begin`, `sys_write`, `sys_read`,
  `sys_commit`, `sys_rollback`, `sys_close`.

### Isolation model (increment 1, honest scope)
**Read-committed with per-session write overlay + commit-time
optimistic-version check.** Each open txn buffers `TxnWrite` records; reads see
`overlay-then-store`, so a peer session reading the same key sees only the
committed store value. Commit replays the overlay into `SdnDatabase` through
`SdnTable.update_row_if` / `insert`, so a concurrent commit that moved the row
version fails the whole txn (no lost update). Rollback drops the overlay.
Not serializable, not MVCC snapshot — documented as such in the ledger.

### Wire protocol (SDN-ish line framing, per project SDN rule)
Request:  `OP k=v k=v ...`   e.g. `PUT tbl=users id=u1 name=ada`
Response: `OK ...` / `ERR code=<code> msg=<...>`
Fail-closed: unknown op, missing required key, unbalanced quoting, unknown
session -> `ERR`, connection stays alive, store untouched.

### Landmine compliance
- No `obj.field += v` anywhere (JIT loads 0).
- Component stores are mutated **extract -> mutate -> write back** into the
  Dict; never a mutating method through 2+ field hops.
- No new `extern fn rt_*`.

## 3. Deliverables
- `src/lib/nogc_sync_mut/database/server/protocol.spl`
- `src/lib/nogc_sync_mut/database/server/capability.spl`
- `src/lib/nogc_sync_mut/database/server/session.spl`
- `src/lib/nogc_sync_mut/database/server/transport.spl`
- `src/lib/nogc_sync_mut/database/server/server.spl`
- `src/lib/nogc_sync_mut/database/server/__init__.spl`
- `test/system/database/server/db_server_tier_spec.spl`
- one `database:` note line in `doc/08_tracking/os/production_status.sdn`

## 4. Results

### Spec verdicts — `test/system/database/server/db_server_tier_spec.spl`
4 describe blocks, **30 examples, 0 failures**, identical on both lanes:

| Lane | connection lifecycle | framing fail-closed | txn isolation | capability |
|---|---|---|---|---|
| `bin/simple run` (JIT) | 5 / 0 | 8 / 0 | 9 / 0 | 8 / 0 |
| `SIMPLE_EXECUTION_MODE=interpreter` | 5 / 0 | 8 / 0 | 9 / 0 | 8 / 0 |

### Deliberate-red calibration (mutant, not a claim)
Injected ONE isolation violation into `DbServerCapsule.sys_write` — apply the
write straight to the store in addition to the overlay — and re-ran:

| block | clean | mutant |
|---|---|---|
| connection lifecycle | 5 / 0 | **5 / 1** (abandoned-txn leak caught) |
| framing fail-closed | 8 / 0 | 8 / 0 (unrelated concern — correctly unmoved) |
| txn isolation | 9 / 0 | **9 / 6** |
| capability | 8 / 0 | 8 / 0 (unrelated concern — correctly unmoved) |

7 tests went red across 2 blocks, including the primary
*"hides one session's uncommitted write from the other session"*.  The two
blocks that stayed green are the two that do not test isolation — the signal is
targeted, not a blanket break.  Mutant reverted; clean re-run re-verified green.

In addition the spec carries an in-file calibration
(*"would go red if an uncommitted write reached the store"*) and an
unconditional control (*"shows the write to the other session once it is
committed"*) that uses the exact same peer read path, so a `not_found` in the
isolation test cannot be a false green from a dead read path.

### Two real defects the spec caught (both fixed)
1. **fail-OPEN session parsing.** `text.to_int()` is typed `i64?` but returns
   **0, not nil**, for a non-numeric string on this runtime.  `session=notanumber`
   was therefore admitted as session 0.  Fixed with an explicit
   `protocol.is_decimal_digits` gate before `to_int()`.  (The same latent
   pattern exists in `database/core.spl` `get_i32`/`get_i64` — NOT touched by
   this lane, but worth a follow-up.)
2. **transport mutation lost across a parameter.** `serve()` mutated a copy of
   the transport, so the caller's handle saw `sent_count() == 0`.  Fixed by
   returning the drained channel: `channel = server.serve(channel)`.

### Compiler bug hit (already filed, not silently worked around)
A **trait-typed parameter has no vtable on the JIT**:
`serve(transport: DbTransport)` dies with *"duck-typed virtual method call
(trait has no `impl Trait for ...` in unit; no vtable)"* — bug
`jit_game2d_backend_method_dispatch_sigsegv_2026-07-02`.  Reproduced minimally
in `build/dbtier_probe.spl`: the identical drain loop returns 3 with a concrete
parameter and faults with a trait-typed one.  `DbTransport` remains the port
contract (`MemoryTransport with DbTransport`); `serve()` is concretely typed
until that bug is fixed.  This is recorded, not normalized.

### Linter status (pre-existing tool defect, with control)
`bin/simple lint` reports
`error: semantic: method 'get' not found on type 'str' (receiver value: <ClassName>)`
for **every file that declares a `class`**.  Control run: the same error appears
on untouched `database/core.spl` (`StringInterner`) and `database/wal.spl`
(`WriteAheadLog`).  The two new files with no `class` (`protocol.spl`,
`txn.spl`) lint clean.  This is a linter defect, not a defect in this lane's
code — which compiles and runs green on both execution lanes.

### Binary-identity caveat
All runs above were produced by `bin/simple`, which currently prints
*"this Rust-built Simple binary is a bootstrap seed only"*.  Evidence therefore
attributes to the SEED, not to the self-hosted binary.  No `extern fn rt_*` was
added, so no bootstrap rebuild is required by this lane.

### Honest scope of what shipped
IN-PROCESS MODEL, not a production server:
- transport is the in-memory `MemoryTransport`; **no socket/IPC listener bound**
- commit lands in the in-memory store and does **not** call `save()` — nothing
  is durable yet, and the existing WAL is not wired to session commits
- sessions are interleaved in one thread; there is **no concurrency primitive**
- query surface is single-row `GET`/`PUT`/`DEL` only
- `OPEN` trusts the claimed principal — **no auth handshake**

## 5. Next increment (precise, in order)

1. **Durability**: call `SdnDatabase.save()` (or append to the existing
   `WriteAheadLog`) inside `txn_apply` under a `FileLock` from
   `database/atomic.spl`, and add a crash-point spec: kill between precheck and
   apply, replay, assert all-or-nothing.
2. **Real transport binding**: adapter class forwarding
   `std.mcp_sdk.transport.transport.Transport` (or a socket transport) onto
   `DbTransport`, plus a listener that gives each accepted connection its own
   session.  Blocked on the JIT trait-vtable bug for dynamic dispatch; a
   concrete-typed adapter can land first.
3. **Authentication**: replace `OPEN as=<principal>` with a token/capability
   handshake so a client cannot name an arbitrary principal.
4. **Isolation upgrade**: snapshot reads (record the store version each txn
   first observed per key and refuse reads that would show a newer commit) to
   remove read skew, then a serializable option.
5. **Query surface**: route `SELECT`-shaped requests through the existing
   `database/query.spl` rather than growing a second evaluator.
6. **Follow-up defect**: `text.to_int()` returning 0 for non-numeric input
   (typed `i64?`) — fix at the runtime or audit every `to_int()` call site.

