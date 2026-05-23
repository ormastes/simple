# SStack State: simple-db-hardening

## User Request
> research and plan complete and harden simple db. what feature missing, where not properly features harden. research first and improve.

## Refined Goal
> Audit the Simple DB two-tier system (embedded stdlib + full engine) for completeness and hardening gaps. Identify missing features, incomplete implementations, untested paths, and security/durability weaknesses. Then implement the highest-priority fixes to harden the database stack.

## Task Type
code-quality

## Acceptance Criteria
- [ ] AC-1: Research phase produces a gap analysis of Simple DB embedded (stdlib database/) vs what a production-quality embedded DB needs (transactions, crash recovery, schema validation, concurrent access)
- [ ] AC-2: Research phase produces a gap analysis of Simple DB Full (examples/simple_db/) vs PostgreSQL-compatible engine requirements (MVCC correctness, WAL recovery, vacuum, TOAST, connection handling)
- [ ] AC-3: Research phase audits simple_db_if trait surface for completeness — are all traits implemented, do both tiers actually conform?
- [ ] AC-4: Research phase audits test coverage — which DBFS/database specs pass, which are stub-only or skipped?
- [ ] AC-5: Top 3-5 hardening fixes are implemented (prioritized by: crash safety > data correctness > missing features)
- [ ] AC-6: All existing database/DBFS tests still pass after changes
- [ ] AC-7: New tests added for any hardening fix

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-23
- [x] 2-research (Analyst) — 2026-05-23
- [x] 3-arch (Architect) — 2026-05-23
- [x] 4-spec (QA Lead) — 2026-05-23
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Task type: code-quality. Refined the user's broad "harden simple db" request into a structured audit + fix pipeline. Key focus areas: crash safety, data correctness, trait conformance, test coverage. ACs cover both tiers (embedded + full) and the shared interface.

### 2-research
4 parallel research agents completed. Reports in `.spipe/simple-db-hardening/`:

**Embedded tier** (`research_embedded.md`): P0: WAL replay drops all field data (blank rows), TodoDB bypasses atomic ops. P1: no fsync before rename, TOCTOU lock race, SDN silently drops unparseable sections. P2: FeatureDB update appends duplicates, WAL never truncated.

**Full engine + DBFS** (`research_full_engine.md`): P0: Full engine submodule is empty (design-only), BTree has no delete rebalancing. P1: recovery uses module-level `var` globals (BSS zero on baremetal), pager in-process only, WAL group-commit simulated. NVFS S2-S7 are stubs.

**Trait surface** (`research_trait_surface.md`): P0: `wal_group_commit` missing from WalWriter, zero concrete implementations in either tier. P1: BufferManager missing release/pin_count, PageStore missing page_read, Checkpointer returns bool not result.

**Test coverage** (`research_test_coverage.md`): P0: BoundedChannel close unimplemented, HTTP worker placeholder paths. P1: database sync design-only, unit coverage smoke-level only, SDN at 60% coverage. 27/33 DBFS specs populated. All 3 hardening design docs are design-only.

**Consolidated P0 list (crash safety > correctness > missing):**
1. WAL replay drops field data (embedded)
2. TOCTOU lock race (embedded)
3. BTree delete underflow (DBFS)
4. Zero trait implementations (simple_db_if)
5. Full engine submodule empty (design-only)
6. WalWriter missing group_commit (trait surface)

### 3-arch

#### Top 5 Hardening Fixes (crash safety > data correctness > missing features)

- **F1** — WAL replay row materialization (crash safety P0, embedded)
- **F2** — Atomic lock creation via O_EXCL (crash safety P0, embedded)
- **F3** — fsync before rename in atomic write (crash safety P1, embedded)
- **F4** — BTree delete rebalancing (data correctness P0, DBFS)
- **F5** — Trait surface completion (missing features P0, simple_db_if)

#### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| WAL codec helpers | `src/lib/nogc_sync_mut/database/wal.spl` | Add `row_to_wal_payload` / `wal_payload_to_row` codec pair; update `WriteAheadLog.append` to serialize row fields into `WalEntry.data` | Modified |
| SdnDatabase WAL replay | `src/lib/nogc_sync_mut/database/core.spl` | Fix `SdnDatabase.load` replay branch to call `wal_payload_to_row` instead of constructing blank `SdnRow(fields: {}, _version: 0)` | Modified |
| FileLock O_EXCL | `src/lib/nogc_sync_mut/database/atomic.spl` | Replace `try_create_lock` body: use `rt_file_create_excl` instead of `file_exists` + `file_write` | Modified |
| Runtime extern (create_excl) | `src/runtime/rt_file.c` (or equivalent) | Add `rt_file_create_excl(path, content) -> bool` — `open(O_CREAT\|O_EXCL\|O_WRONLY)` + write + close | Modified |
| Atomic fsync | `src/lib/nogc_sync_mut/database/atomic.spl` | Add `rt_file_sync(path) -> bool` call after `file_write(temp_path, ...)` and before `rt_file_rename` in `atomic_write`, `atomic_write_batch`, and `atomic_append` | Modified |
| Runtime extern (fsync) | `src/runtime/rt_file.c` (or equivalent) | Add `rt_file_sync(path) -> bool` — `open` + `fsync(fd)` + `close` | Modified |
| BTree rebalancing | `src/lib/nogc_sync_mut/storage/shared/btree.spl` | Add `ensure_min_keys`, `merge_children`, `borrow_from_left`, `borrow_from_right`; call `ensure_min_keys` from `delete_from_node` before descending into a child | Modified |
| WalWriter trait | `src/lib/nogc_sync_mut/simple_db_if/storage_api.spl` | Add `wal_group_commit(upto: Lsn) -> Lsn` to `WalWriter` trait | Modified |
| BufferManager trait | `src/lib/nogc_sync_mut/simple_db_if/storage_api.spl` | Add `buf_release(page: PageBuf) -> bool` and `buf_pin_count(rel: Rel, blk: BlkNo) -> i64` to `BufferManager` trait | Modified |
| PageStore trait | `src/lib/nogc_sync_mut/simple_db_if/storage_api.spl` | Add `page_read(rel: Rel, blk: BlkNo) -> [u8]` to `PageStore` trait | Modified |
| Checkpointer trait | `src/lib/nogc_sync_mut/simple_db_if/storage_api.spl` | Change `checkpoint_commit(at: Lsn) -> bool` to `checkpoint_commit(at: Lsn) -> Result<Lsn, text>` | Modified |

#### Dependency Map

- `database/core.spl` -> `database/wal.spl` (imports `wal_payload_to_row`, `WriteAheadLog`)
- `database/wal.spl` -> `database/atomic.spl` (imports `atomic_append`, `atomic_write`, `atomic_read`)
- `database/atomic.spl` -> runtime externs (`rt_file_create_excl`, `rt_file_sync`, `rt_file_rename`)
- `storage/shared/btree.spl` -> (self-contained, no new external deps)
- `simple_db_if/storage_api.spl` -> `simple_db_if/types.spl` (existing dep, unchanged)
- No circular dependencies: verified

#### Decisions

- **D-1:** WAL format version bump — Add a `#wal-version:2` header line to new WAL files. On replay, if the header is absent (version 1), skip entries silently. Version 2 entries carry serialized field data. Rationale: grep confirms no domain database ever calls `WriteAheadLog.append` — the WAL write path is entirely unwired in v1. The v1 replay was also broken (blank rows). Therefore v1 WAL files contain no recoverable data, and silent discard preserves the same observable behavior as the broken v1 replay.
- **D-2:** Two new runtime externs (`rt_file_create_excl`, `rt_file_sync`) — These require a bootstrap rebuild (`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`). Acceptable because: (a) both are small, self-contained C functions, (b) no pure-Simple fallback exists for O_EXCL or fsync semantics, (c) the bootstrap deploy is a known operational step per `feedback_extern_bootstrap_rebuild`.
- **D-3:** BTree rebalancing uses CLRS top-down proactive fix-up — Before descending into a child during delete, call `ensure_min_keys` to guarantee the child has at least `t` keys. This avoids bottom-up rebalancing and matches the existing code comment "Deletion: top-down proactive fix-up (CLRS-style)." which was stated but not implemented.
- **D-4:** TodoDB write-path migration is OUT OF SCOPE — The actual writer lives in `src/app/todo_scan/`, outside the three scoped directories (database/, dbfs_engine/, simple_db_if/). The `database/todo.spl` module's own header declares write-path migration out of scope. Follow-up task.
- **D-5:** Recovery module-level `var` globals (BSS-zero on baremetal) are OUT OF SCOPE — Known issue per `feedback_baremetal_module_val_zero`, but the DBFS recovery module is DBFS-layer code that runs in hosted environments, not baremetal targets. Baremetal DBFS recovery is a future milestone. Not blocking for this hardening pass.
- **D-6:** Trait conformance is Phase 5 work — F5 completes the trait *signatures* only. Concrete implementations (e.g. an embedded-tier shim mapping `SdnDatabase + WriteAheadLog -> WalWriter`) belong in Phase 5 (implement). The full engine submodule is explicitly out of scope.

#### Public API

**F1 — WAL codec (wal.spl):**
- `fn row_to_wal_payload(row: SdnRow, columns: [text]) -> text` — serialize row fields using SDN quoted-CSV format (reuses `quote_if_needed` from `core.spl`). Encoding: columns joined by `,` (comma), with values quoted if they contain `,`, `|`, `\n`, or `"`. This avoids conflict with the WAL line delimiter `|` because `wal_entry_from_line` already rejoins `data` from inner parts. The quoted-CSV format is round-trip safe with the existing `split_sdn_row` / `strip_quotes` helpers.
- `fn wal_payload_to_row(payload: text, columns: [text]) -> SdnRow?` — deserialize WAL payload using `split_sdn_row` + `strip_quotes` back into an `SdnRow` with populated `fields`

**F2 — Atomic lock (atomic.spl):**
- `extern fn rt_file_create_excl(path: text, content: text) -> bool` — create file atomically with O_CREAT|O_EXCL; returns false if file already exists

**F3 — fsync (atomic.spl):**
- `extern fn rt_file_sync(path: text) -> bool` — open file, fsync, close; returns false on error

**F4 — BTree rebalancing (btree.spl):**
- `me fn ensure_min_keys(parent_idx: i64, child_i: i64)` — guarantee child has at least `fanout` keys before descent; calls borrow or merge
- `me fn merge_children(parent_idx: i64, i: i64)` — merge child[i] + separator key + child[i+1] into one node
- `me fn borrow_from_left(parent_idx: i64, i: i64)` — rotate rightmost key of left sibling through parent into child[i]
- `me fn borrow_from_right(parent_idx: i64, i: i64)` — rotate leftmost key of right sibling through parent into child[i]

**F5 — Trait surface (storage_api.spl):**
- `WalWriter::fn wal_group_commit(upto: Lsn) -> Lsn` — flush WAL up to `upto`, return actual durable LSN
- `BufferManager::fn buf_release(page: PageBuf) -> bool` — unpin a page buffer
- `BufferManager::fn buf_pin_count(rel: Rel, blk: BlkNo) -> i64` — current pin count for a page
- `PageStore::fn page_read(rel: Rel, blk: BlkNo) -> [u8]` — read current version of a page
- `Checkpointer::fn checkpoint_commit(at: Lsn) -> Result<Lsn, text>` — commit checkpoint, return durable LSN or error (replaces `-> bool`)

#### Data Flow

**F1 — WAL replay (crash recovery):**
1. Writer calls `wal.append(entry)` where `entry.data = row_to_wal_payload(row, columns)`
2. `append` serializes to pipe-delimited line via `wal_entry_to_line` and calls `atomic_append`
3. On crash recovery, `SdnDatabase.load` calls `wal.replay()` to get pending entries
4. For each Insert/Update entry, `load` calls `wal_payload_to_row(entry.data, table.columns)` to reconstruct the row with fields populated
5. Reconstructed row is added via `table.add_row(row)` — no more blank rows

**F2 — Lock acquisition (concurrent access):**
1. `FileLock.try_create_lock` calls `rt_file_create_excl(lock_path, pid_content)`
2. Kernel guarantees atomicity: exactly one process succeeds; all others get EEXIST -> return false
3. Stale-lock check remains as fallback (process-alive + 2h timeout)

**F3 — Durable atomic write:**
1. `atomic_write` writes content to `path.tmp` via `file_write`
2. Calls `rt_file_sync(temp_path)` — data reaches stable storage
3. Calls `rt_file_rename(temp_path, path)` — atomic pointer swap
4. Same pattern in `atomic_write_batch` (sync each temp before any rename) and `atomic_append`

**F4 — BTree delete with rebalancing:**
1. `delete(key)` calls `delete_from_node(root, key)`
2. Before descending into `child[i]`, call `ensure_min_keys(node_idx, i)`
3. `ensure_min_keys` checks if child has < `fanout` keys; if so:
   a. Try `borrow_from_left` (left sibling has > `fanout` keys) — rotate through parent
   b. Else try `borrow_from_right` (right sibling has > `fanout` keys) — rotate through parent
   c. Else `merge_children` — merge child with a sibling + parent separator key
4. After fix-up, descend into the (possibly merged) child and continue

**F5 — Trait surface extension:**
1. Signature-only additions to `storage_api.spl`
2. No data flow changes — these are contract declarations
3. Concrete implementations deferred to Phase 5

#### Requirement Coverage

- F1 (WAL replay) -> `database/wal.spl`, `database/core.spl`
- F2 (O_EXCL lock) -> `database/atomic.spl`, `src/runtime/rt_file.c`
- F3 (fsync) -> `database/atomic.spl`, `src/runtime/rt_file.c`
- F4 (BTree rebalance) -> `storage/shared/btree.spl`
- F5 (trait surface) -> `simple_db_if/storage_api.spl`

### 4-spec

5 spec files created covering all 5 hardening fixes (F1-F5). 50 total `it` blocks across 5 files. All specs use built-in matchers only, no `skip()`. Tests are designed to fail (red phase) until Phase 5 implementation lands. F5 uses mock `impl Trait for Struct` blocks that fail to compile if trait methods are missing. F1 includes end-to-end SdnDatabase.load integration test plus WAL v1/v2 versioning tests (D-1). F4 uses correct `BTreeKey { a, b }` composite key API.

#### Spec Files
- `test/system/database/wal_replay_row_materialization_spec.spl` — 19 specs covering F1 (AC-5, AC-7): codec round-trip, special chars, WAL v1/v2 versioning, SdnDatabase.load integration
- `test/system/database/atomic_lock_excl_spec.spl` — 8 specs covering F2 (AC-5, AC-7): rt_file_create_excl O_EXCL semantics, FileLock acquire/release
- `test/system/database/atomic_fsync_spec.spl` — 7 specs covering F3 (AC-5, AC-7): rt_file_sync extern, atomic_write content integrity, temp file cleanup
- `test/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl` — 11 specs covering F4 (AC-5, AC-7): leaf/internal delete, borrow left/right, merge, cascade, order invariant
- `test/unit/lib/nogc_sync_mut/simple_db_if/storage_api_surface_spec.spl` — 5 specs covering F5 (AC-3, AC-5, AC-7): mock impl blocks verify wal_group_commit, buf_release, buf_pin_count, page_read, checkpoint_commit Result return

#### AC Coverage Matrix

| AC | Spec File | it blocks | Status |
|----|-----------|-----------|--------|
| AC-3 | `storage_api_surface_spec.spl` | "wal_group_commit is callable", "buf_release is callable", "buf_pin_count is callable", "page_read is callable", "checkpoint_commit returns Result not bool" | Failing (trait methods missing) |
| AC-5 | all 5 spec files | all 50 it blocks | Failing (no impl) |
| AC-7 | all 5 spec files | all 50 it blocks — these ARE the new tests | Failing (no impl) |

#### Coverage Markers
- F1: `# @cover src/lib/nogc_sync_mut/database/wal.spl`, `# @cover src/lib/nogc_sync_mut/database/core.spl`
- F2: `# @cover src/lib/nogc_sync_mut/database/atomic.spl`, `# @cover src/runtime/rt_file.c`
- F3: `# @cover src/lib/nogc_sync_mut/database/atomic.spl`, `# @cover src/runtime/rt_file.c`
- F4: `# @cover src/lib/nogc_sync_mut/storage/shared/btree.spl`
- F5: `# @cover src/lib/nogc_sync_mut/simple_db_if/storage_api.spl`

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
