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
(filled in after implementation — see bottom of file)
