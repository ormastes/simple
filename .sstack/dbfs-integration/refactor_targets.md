# DBFS Integration — Phase 6 Refactor Targets (Scout Report)

Snapshot taken at HEAD = `bbdd694a05` while a parallel Sonnet agent was finishing
Phase 5. Files in `src/lib/nogc_sync_mut/db/**` were read once and the analysis
below is anchored to that snapshot. Any later edits by the Phase-5 agent need a
re-scan before action.

## 0. Scope snapshot

| Path | LoC |
|---|---:|
| `src/lib/nogc_sync_mut/db/__init__.spl` | 11 |
| `src/lib/nogc_sync_mut/db/dbfs_driver/__init__.spl` | 4 |
| `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` | 507 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/__init__.spl` | 18 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint.spl` | ~165 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint_ring.spl` | ~210 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/intent_log.spl` | ~180 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/ns_btree.spl` | ~545 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/pager.spl` | ~225 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/recovery.spl` | ~115 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/schema.spl` | ~590 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/txn.spl` | ~185 |
| `src/lib/nogc_sync_mut/db/dbfs_engine/wal.spl` | ~165 |
| **Total** | **~2,820** |

No file was unparseable in the snapshot. All 13 modules are reviewable.

Read-only neighbours used for cross-reference:
`src/lib/nogc_sync_mut/fs_driver/instance.spl`,
`src/lib/nogc_sync_mut/storage/arena.spl`,
`examples/simple_db/src/engine/{wal,checkpoint,pmap}.spl`,
`examples/nvfs/src/core/{pmap_btree,ns_tree,intent_log,checkpoint}.spl`,
`.sstack/dbfs-integration/dbfs_architecture.md`.

---

## 1. Dedup opportunities

### 1.1 DbFsDriver handle-resolution boilerplate (HIGH-value)
The pattern
```
val fd_idx = _find_fd_idx(self.inst_id, handle.id as u64)
if fd_idx < 0:
    return Err(FsError.NotFound)
val inode_idx = _fd_inode_idx(self.inst_id, handle.id as u64)
if inode_idx < 0:
    return Err(FsError.NotFound)
```
appears at lines 236-242, 257-259, 279-286, 304-308, 344-348, 411-415 of
`dbfs_driver.spl` (roughly 10 sites total when counting the `_find_inode_idx`
variants at lines 161, 180, 365, 388-393).

**Suggested helper** (file-private, near line 100):
```
fn _resolve_fd(inst_id: i64, handle: u64) -> Result<(i32, i32), FsError>
fn _resolve_path(inst_id: i64, path: text) -> Result<i32, FsError>
```
returning `(fd_idx, inode_idx)` / `inode_idx` or `Err(FsError.NotFound)`.

**Estimated LoC reduction:** ~30-40 lines removed from `dbfs_driver.spl`.
**Risk:** LOW — pure local refactor, no behavioural change.

### 1.2 Schema linear-scan-by-key (MEDIUM-value)
`dbfs_engine/schema.spl` repeats an identical `while i < entries.len() as i32`
linear scan for INODE / EXTENT / BLOCK_BLOB / TXN / WAL_RECORD /
STORAGE_CLASS (single-i64-key tables — see lines 240-258, 367-378,
383-396, 458-475, 483-498, 502-535).

**Suggested helper:** a private `_find_by_id(entries, get_id, target) -> i32`
or one shared `SingleKeyTable<Row>` with `.entries: [(i64, Row)]`. Apply only
to the six single-i64-key tables. The five composite-key tables
(DENTRY, FILE_VERSION, EXTENT_REF, XATTR, ACL_ENTRY) keep their bespoke
scans — extracting them too would bloat the helper signature.

**Estimated LoC reduction:** ~30-50 lines (six tables × ~5-7 saved each).
Honest-mid number — the upper bound assumes the helper can be a
`SingleKeyTable` rather than just a function.
**Risk:** LOW-MEDIUM — touches the catalog schema; needs test re-run.

### 1.3 ns_btree vs pmap_btree (DEFERRED — out of 30-min scope)
`dbfs_engine/ns_btree.spl` is explicitly documented as a "structural copy of
`examples/nvfs/src/core/pmap_btree.spl`" (header comment lines 4-5). The two
files together account for ~1,400 LoC. A shared generic B-tree is a real
opportunity but:

- It crosses the D2/D3 architecture lock (DBFS owns its own ns_btree per the
  arch doc's "the B-tree is a hash index; the schema table is the
  authoritative store" note).
- Simple generics around B-tree nodes touch `<>`-on-struct corners that have
  historically been fragile.
- The two callers have diverged in compare semantics
  (DentryKey: parent_ino+name_hash i64 vs PmapKey).

**Recommendation:** file as a follow-up bug/feature request
(`fr_dbfs_btree_unify`) and **do not include in Phase 6 30-min cleanup**.

### 1.4 Module-static persistence boilerplate (DEFER — high risk, low gain)
`pager._pager_disk_pages`, `checkpoint_ring._ring_store_*`, and
`intent_log._intent_*` each implement the same "module-static list backing
write_through + reopen+scan" pattern. These are documented workarounds for
the interpreter's value-semantics field-mutation loss
(see header comments in all three files).

A shared helper would need to be parameterised over element type and key
(StorageClass vs PageId vs LSN) and would obscure the workaround
documentation that lives at each call site. **Recommendation:** keep
duplicated, add a single docstring header in
`dbfs_engine/__init__.spl` cross-linking the three sites. Net LoC delta: +5
docstring, no code change. Gain is zero LoC; clarity is positive.

---

## 2. Naming consistency check

- **`<T>` vs `[T]` generics:** all generic uses are `<>` form. No `[T]`
  brackets found in scope (grep verified).
- **`class` keyword:** Simple's class keyword is not in use here at all
  (Simple has no `class` declaration form per the language rules — only
  `struct`, `impl`, `trait`). No matches found.
- **`class` / `dclass` struct field name** (per memory
  `project_driver_framework`): **N/A** in this scope. The DbFsDriver struct
  in `dbfs_driver.spl` (line 54) does not currently expose a `class:` or
  `dclass:` field, and `src/lib/nogc_sync_mut/fs_driver/` likewise has no
  such field today. The convention is **not exercised** by DBFS code, so
  there is nothing to align. If/when the driver framework introduces a
  per-driver storage-class hint field, follow `dclass` per the memory note.
- **D3 schema names:** all 11 D3 tables (INODE, DENTRY, FILE_VERSION,
  EXTENT_REF, EXTENT, BLOCK_BLOB, XATTR, ACL_ENTRY, TXN, WAL_RECORD,
  STORAGE_CLASS) match the architecture doc verbatim. Key shapes match the
  D3 lock (e.g. `DentryKey(parent_ino, name: text)` for the schema table vs
  `DentryKey(parent_ino, name_hash: i64)` for `ns_btree` — this is by
  design and called out in `ns_btree.spl` header lines 7-9).

---

## 3. Style/lint issues

- **TODO / FIXME / XXX in scope:** **0**. (The string "skip" appears only in
  the recovery comment "skip uncommitted" — not a `skip()` call.)
- **`skip()` calls:** **0**.
- **Unused imports:** none obvious. Every `use` line is referenced. The
  `intent_log.spl` import of `WAL_RECORD_DATA` should be cross-checked once
  Phase 5 settles — at the snapshot moment it appears only in a doc
  comment. **Action: confirm and drop if unused.** (Estimated 1 LoC.)
- **Orphan `var` declarations:** the loops in `pager.spl`, `wal.spl`, and
  `schema.spl` use the `while i < x.len() as i32` idiom which leaves
  `var i: i32 = 0` as a single-purpose loop counter. This is the project's
  standard style (matched in Simple DB/nvfs neighbours), not an orphan. No
  action.
- **`fn` vs `me fn` for field-mutating methods:** automated scan
  (`self\.X =` inside a non-`me fn`) reported **0 violations**. All
  mutators (`record`, `append`, `flush_wal`, `set_intent_log_head`,
  `commit`, `abort`, `replace_node`, `insert`, `delete`, `write_slot`,
  `flush`, `close`, `flush_dirty`, `flush_page`, `checkpoint_now`,
  `group_commit`, `observe_steps`, `write_data`, `write_metadata_private`,
  `append_wal`, `publish_root`, `set_intent_log_head`) are correctly
  marked `me fn`. **Note:** `observe_steps` returns a `TxnStepOrder` and
  is `me fn` even though it could be `fn` — this is intentional
  (it threads the side-effect of recording the observation). No action.

**Total lint violations in scope: 0–1** (one possible unused import to
verify).

---

## 4. Single-cache discipline audit

Grepped for `page_cache_insert`, `kernel_cache`, `vm_cache`, `pagecache`
across `src/lib/nogc_sync_mut/db/**`:

- **Code matches: 0.**
- **Comment matches:** two — both in `pager.spl` lines 5-6 and 222-223,
  and they are negative declarations
  (*"pages are keyed (ino_id, page_id) and never inserted into the kernel
  page cache"* and *"DbfsPager does not expose kernel cache methods"*).
  These are the discipline assertions the architecture requires.

**Verdict: clean.** Single-cache discipline holds.

---

## 5. Inheritance scan

Grepped for `extends`, `inherits`, `super.`, `super(` across the db scope:

- **Matches: 0.**

All composition is done via `struct` + `impl` + concrete-driver `enum`
dispatch in `fs_driver/instance.spl::DriverInstance`. No vtable, no `dyn`,
no smell of inheritance. **Verdict: clean.**

---

## 6. Reuse opportunity callouts

| Site | Existing implementation | Recommendation |
|---|---|---|
| `dbfs_engine/wal.spl` write/flush/durable_lsn API | `examples/simple_db/src/engine/wal.spl` has the same shape (`append`, `flush`, `durable_lsn`, `recovery_cursor`) | **Do not swap** — DBFS WAL is intentionally embedded; Simple DB WAL is application-level. Keep as parallel implementations. Note in `dbfs_engine/wal.spl` header that the API mirrors Simple DB intentionally. (~3 LoC docstring) |
| `dbfs_engine/ns_btree.spl` whole module | `examples/nvfs/src/core/pmap_btree.spl` (CLRS B-tree) | Already noted as structural copy. **Defer to fr_dbfs_btree_unify** (see §1.3). |
| `dbfs_engine/checkpoint.spl` `latest_clean()` | `examples/nvfs/src/core/checkpoint.spl` | Already structurally aligned; behaviours match. No change needed. |
| `dbfs_engine/intent_log.spl` `append`/`scan_committed`/`flush` | `examples/nvfs/src/core/intent_log.spl` | Same observation as ns_btree — structurally similar but tied to its own host. Keep parallel; cross-reference in header. |
| `dbfs_driver` arena calls | `src/lib/nogc_sync_mut/storage/arena.spl::Arena` trait | DBFS does **not** currently call the `Arena` trait — it goes through `_pager_disk_pages` module-static (interpreter workaround). When the kernel-linked arena backend lands (`dbfs_kernel_linked` flag, mentioned in `checkpoint_ring.spl` header), wire the pager through `arena_append`/`arena_readv` instead of the module-static list. **Out of Phase 6 scope** (architecture-gated). |

---

## 7. Phase 6 work list (prioritised, 30-minute pass)

Realistic LoC totals — not aspirational.

| # | Action | Files | LoC delta | Risk |
|---|---|---|---:|:---:|
| 1 | Extract `_resolve_fd(inst_id, handle) -> Result<(i32,i32), FsError>` and `_resolve_path(inst_id, path) -> Result<i32, FsError>`; replace ~10 call sites | `dbfs_driver/dbfs_driver.spl` lines 156-460 | **−30 to −40** | LOW |
| 2 | Verify `WAL_RECORD_DATA` import in `intent_log.spl` line 19 is used; drop if not | `dbfs_engine/intent_log.spl` | **−1 or 0** | LOW |
| 3 | Add cross-reference docstring header in `dbfs_engine/__init__.spl` calling out the three module-static persistence sites (`pager`, `checkpoint_ring`, `intent_log`) and the Simple DB/nvfs structural mirrors (wal, ns_btree, intent_log) | `dbfs_engine/__init__.spl` | **+5 to +10** docstring | LOW |
| 4 | Extract single-key linear-scan helper for the six single-i64-key schema tables (INODE, EXTENT, BLOCK_BLOB, TXN, WAL_RECORD, STORAGE_CLASS) — either a `_find_by_id` private fn or shared `SingleKeyTable<Row>` | `dbfs_engine/schema.spl` lines 232-535 | **−30 to −50** | LOW-MED |
| 5 | Add a header comment in `ns_btree.spl` linking explicitly to the deferred `fr_dbfs_btree_unify` follow-up so the duplicate is intentional, not accidental | `dbfs_engine/ns_btree.spl` | **+3** | LOW |
| 6 | (DEFERRED — file as follow-up, parallel-agent risk per `feedback_jj_uncommitted_clobbered_by_parallel`) Tighten naming consistency: rename `_pager_disk_pages` / `_dbfs_inodes` / `_dbfs_fds` / `_ring_store_slots` / `_intent_*` to a single `_dbfs_persist_<module>_*` prefix. Broad cosmetic rename across 5+ files = clobber-fodder during parallel commits. Net LoC = 0; defer until Phase 5/6 fully settle | all engine + driver `.spl` | **0 net** | MED-HIGH (parallel race) |
| 7 | (DEFERRED — file as bug/FR, do not implement now) `fr_dbfs_btree_unify` — extract a generic CLRS B-tree shared with `pmap_btree.spl` | `dbfs_engine/ns_btree.spl`, `examples/nvfs/src/core/pmap_btree.spl` | est. **−400 to −600** if landed | HIGH |
| 8 | (DEFERRED — gated on `dbfs_kernel_linked`) Wire `pager.spl` through `storage/arena.spl::Arena` once the kernel-linked backend lands; remove `_pager_disk_pages` module-static | `dbfs_engine/pager.spl`, `storage/arena.spl` | est. **−40 to −70** | HIGH |

**Items 1–5 = the 30-minute Phase 6 pass.** Net LoC delta: **−85 to −115**.

Items 6-8 are flagged as deferred with the architecture, compiler, or
parallel-agent gate that unblocks them; they are **not** part of Phase 6.

---

## 8. Architecture lock respected

D1-D12 (per `dbfs_architecture.md`) are unchanged by all of items 1-6:
- D1 single-cache: untouched.
- D2 ns_btree+schema: only adds helper docstrings (item 6).
- D3 catalog tables: schema linear-scan helper preserves Key/Row shapes.
- D4 6-step txn protocol, D5 5-step recovery: untouched.
- D9 8 KiB pages: untouched.
- D12 R1/R2 (intent log + checkpoint ring persistence): untouched —
  module-static workaround is preserved per advisor guidance (§1.4).

---

## 9. Source labels for follow-up search

`refactor_targets`, `dbfs_driver_resolve_helper`, `schema_single_key_helper`,
`fr_dbfs_btree_unify`, `dbfs_kernel_linked_arena_wire`,
`dbfs_persist_naming_unify`.
