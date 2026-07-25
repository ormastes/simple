# simple_db_if Trait Surface Audit

**Audited:** 2026-05-23
**Scope:** `src/lib/*/simple_db_if/` across all 4 runtime families + both DB tiers

---

## 1. Trait Inventory

### Authoritative source: `nogc_sync_mut/simple_db_if/`

**`storage_api.spl`** — 8 traits + 1 struct:

| Name | Kind | Methods |
|------|------|---------|
| `PageBuf` | struct | fields: `arena_id`, `offset`, `length`, `generation` (all i64) |
| `BufferManager` | trait | `buf_get(rel, blk) -> PageBuf`, `buf_prefetch(rel, blk) -> bool` |
| `WalWriter` | trait | `wal_append(txn, payload: [u8]) -> Lsn` |
| `PageStore` | trait | `page_rewrite(rel, blk, new_bytes: [u8], wal_lsn) -> PhysPtr` |
| `PageMap` | trait | `pmap_publish(rel, blk, phys, wal_lsn) -> bool` |
| `TempStore` | trait | `temp_alloc(txn, bytes: i64) -> PhysPtr`, `temp_release(txn, phys) -> bool` |
| `Checkpointer` | trait | `checkpoint_begin() -> Lsn`, `checkpoint_commit(at: Lsn) -> bool` |
| `BlobStore` | trait | `blob_put(rel, bytes: [u8]) -> PhysPtr`, `blob_get(phys) -> [u8]` |
| `Vacuumer` | trait | `vacuum_range(rel, lo_blk, hi_blk) -> i64` |

Total: **12 methods** across 8 traits (matches the "twelve verbs" comment in file header).

**`types.spl`** — 5 newtype structs:

| Name | Fields | Helper methods |
|------|--------|----------------|
| `Rel` | `id: i64` | `null() -> Rel`, `is_null() -> bool` |
| `BlkNo` | `n: i64` | `first() -> BlkNo` |
| `Lsn` | `value: i64` | `zero() -> Lsn`, `precedes(other) -> bool` |
| `TxnId` | `id: i64` | `null() -> TxnId` |
| `PhysPtr` | `arena_id: i64`, `offset: i64` | `null() -> PhysPtr`, `is_null() -> bool` |

---

## 2. Cross-Variant Consistency

Re-export chain (authoritative → downstream):

```
nogc_sync_mut/simple_db_if/   ← authoritative (only real definitions)
    ↑ re-exported by
nogc_async_mut/simple_db_if/  ← re-exports nogc_sync_mut symbols by name
    ↑ re-exported by
gc_async_mut/simple_db_if/    ← re-exports nogc_async_mut symbols by name
    ↑ re-exported by
gc_sync_mut/simple_db_if/     ← compatibility facade, star-imports gc_async_mut
```

**Consistency verdict: CONSISTENT** — all 4 variants expose identical symbols via the re-export chain. No variant adds or removes methods. The chain is linear and unambiguous.

**Note:** `nogc_async_mut` re-exports by explicit named list (not star), which is correct — it cannot accidentally gain or lose new symbols when the source changes. `gc_sync_mut` uses `@allow(star_import)` with a rationale comment, which is acceptable for a pure facade.

---

## 3. Conformance Status

### Embedded tier (`database/`)

The `database/mod.spl` header explicitly states:
> "Shared interface: `std.simple_db_if` (trait contracts both tiers implement)"

However, **no actual conformance declarations were found**:
- `grep` for `simple_db_if`, `conform`, `BufferManager`, `WalWriter`, `PageStore`, etc. in `database/core.spl` and `database/mod.spl` returned **empty output**.
- The embedded tier (`nogc_sync_mut/database/` and `nogc_async_mut/database/`) is an SDN-file-backed BugDB/TestDB/FeatureDB system. Its storage model is entirely different from the WAL + MVCC + buffer pool model the traits describe.
- **The embedded tier does NOT implement the `simple_db_if` traits.** The claim in `mod.spl` that "both tiers implement" the shared interface is incorrect documentation — no concrete impl exists in the stdlib database module.

### Full engine (`examples/simple_db/`)

The submodule at `examples/simple_db/` is essentially **empty** — it contains only:
- `.git` (gitdir pointing to `../../.git/modules/examples/spostgre`)
- `.simple/` and `target/` directories

No `.spl` source files exist. The submodule was initialized but never populated. Note: the gitdir path reveals the submodule was created as `examples/spostgre` internally (see §5 below).

**Neither tier has any concrete conforming implementation of the `simple_db_if` traits.**

---

## 4. Test Coverage

### Unit tests (what they actually verify)

Two unit test files exist:
- `test/01_unit/lib/gc_async_mut/simple_db_if/simple_db_if_facade_spec.spl`
- `test/01_unit/lib/nogc_async_mut/simple_db_if/simple_db_if_facade_spec.spl`

Both are **identical in structure** — they verify:
1. Type constructors resolve (`Rel.null()`, `BlkNo.first()`, `Lsn.zero()`, `TxnId.null()`, `PhysPtr.null()`)
2. Helper methods work (`is_null()`, `.n`, `.precedes()`, `.id`)
3. `PageBuf` struct fields are accessible (`arena_id`, `offset`, `length`, `generation`)

**What tests do NOT verify:**
- No tests for `nogc_sync_mut` or `gc_sync_mut` variants (gap)
- No tests that any trait method is callable
- No conformance tests — no mock impl is constructed and exercised against the trait interface
- No tests of the 8 storage traits themselves

### Feature tests (`test/features/simple_db/`)

7 `.feature` files exist:
- `trait_surface.feature`, `wal_ordering.feature`, `vacuum.feature`, `mdsoc_outer.feature`, `ecs_components.feature`, `hot_slack.feature`, `tier_cache.feature`

All feature files are **pending** (no step definitions, scenarios reference `Status: pending — Phase 5 lands the skeleton`). They reference `spostgre_if` not `simple_db_if` (see §5).

### System tests

`test/03_system/simple_db_nvfs_constants_spec.spl` — verifies NVFS constant ordinals (`STORAGE_CLASS_DB_WAL=1`, `STORAGE_CLASS_META_DURABLE=2`, etc.). Unrelated to trait conformance.

### Performance benchmarks

`test/05_perf/bench/simple_db_shared_accel.spl`, `simple_db_wal_append.spl` — exist but are benchmark stubs, not conformance tests.

---

## 5. Missing Traits / Methods

### P0 — Critical (blocks any real use of the trait surface)

| ID | Gap | Detail |
|----|-----|--------|
| P0-1 | `WalWriter` missing `wal_group_commit` | Design doc (`simple_db_design.md §5`, line 365) lists `wal_group_commit(upto_lsn) -> Lsn` as an outer API verb. The trait only has `wal_append`. `wal_group_commit` is needed for durable-commit handshake (§6.3–6.5). Without it, callers cannot wait for WAL flush to complete. |
| P0-2 | No concrete impl in either tier | Both the embedded stdlib and the full engine (examples/simple_db) have zero conforming implementations. The interface is declaration-only. |

### P1 — High (correctness / usability gap)

| ID | Gap | Detail |
|----|-----|--------|
| P1-1 | `BufferManager` missing `buf_release` / `buf_pin_count` | A buffer pool that only has `buf_get` and `buf_prefetch` but no unpin/release is incomplete — pinned pages can never be evicted. Design doc mentions buffer pins but the trait surface has no release verb. |
| P1-2 | `PageStore` missing `page_read` | Traits expose `page_rewrite` (write) but not `page_read` (read). Reading the current version of a page is a fundamental operation that any backend must support. |
| P1-3 | `Checkpointer` returns `bool` for `checkpoint_commit` | Should return a result type (success/error) or the durable LSN, not `bool`. A caller cannot distinguish a failed checkpoint from a successful one that flushed to LSN=0. |

### P2 — Medium (design doc divergence)

| ID | Gap | Detail |
|----|-----|--------|
| P2-1 | Feature tests reference `spostgre_if`, not `simple_db_if` | `trait_surface.feature` and `mdsoc_outer.feature` target `src/lib/nogc_sync_mut/spostgre_if/`, which does not exist. These feature tests are misrouted. The trait namespace committed in code is `simple_db_if`. |
| P2-2 | `RelationOracle` trait absent | `trait_surface.feature` Scenario lists `RelationOracle` as a required trait (from `spostgre_design.md §2.1`). No `RelationOracle` appears in `simple_db_if`. If this is a valid requirement, it is missing entirely. |
| P2-3 | `pmap_publish` missing expected-generation parameter | `trait_surface.feature` Scenario states `pmap_publish` should take an `expected_gen` parameter for CAS-style safety. The current signature is `pmap_publish(rel, blk, phys, wal_lsn) -> bool` — no generation guard. |
| P2-4 | `examples/simple_db` gitdir maps to `spostgre` | The `.git` file in `examples/simple_db/` points to `../../.git/modules/examples/spostgre`. The directory was registered under the wrong name. |

### P3 — Low (test / documentation gaps)

| ID | Gap | Detail |
|----|-----|--------|
| P3-1 | No unit tests for `nogc_sync_mut` or `gc_sync_mut` variants | Tests exist only for `nogc_async_mut` and `gc_async_mut`. |
| P3-2 | Unit tests only verify struct field access, not trait callability | No trait mock or stub implementation is exercised. |
| P3-3 | `database/mod.spl` incorrectly claims embedded tier implements the interface | The comment "trait contracts both tiers implement" is aspirational, not current fact. |
| P3-4 | `BlkNo` missing `is_null` helper | `Rel`, `TxnId`, `PhysPtr` all have `is_null()`. `BlkNo` only has `first()`. A sentinel for "no block" may be needed. |

---

## 6. Recommendations (Prioritized)

### Immediate (before any impl work)

1. **Add `wal_group_commit(upto_lsn: Lsn) -> Lsn` to `WalWriter`** (P0-1) — the design doc requires it; omitting it breaks the WAL durability contract described in §6.3–6.5.

2. **Add `buf_release(buf: PageBuf) -> bool` to `BufferManager`** (P1-1) — a buffer pool without an unpin verb cannot be correctly implemented.

3. **Add `page_read(rel: Rel, blk: BlkNo) -> PageBuf` to `PageStore`** (P1-2) — read is at least as fundamental as write.

### Short-term (Phase 5 prep)

4. **Reconcile feature tests** — rename `spostgre_if` references in feature files to `simple_db_if`, or decide whether `spostgre_if` will be a separate namespace. Currently the feature tests target a directory that does not exist. (P2-1)

5. **Add `pmap_publish` generation parameter** — change signature to `pmap_publish(rel, blk, phys, wal_lsn, expected_gen) -> bool` per the feature test contract. (P2-3)

6. **Fix `examples/simple_db` submodule registration** — the gitdir maps to `spostgre`; determine the correct target repo and re-register. (P2-4)

### Medium-term (hardening)

7. **Write conformance tests** — for each trait, provide a minimal stub impl and exercise every method signature. This catches breaking changes before impl work begins.

8. **Add `nogc_sync_mut` and `gc_sync_mut` unit tests** (P3-1) — the two variants have no coverage at all.

9. **Fix `database/mod.spl` comment** — change "both tiers implement" to "trait surface that the full engine implements; embedded tier is structurally separate" until actual conformance is added. (P3-3)

10. **Consider `RelationOracle` trait** — if `spostgre_design.md §2.1` is still authoritative for the full-engine tier, this trait needs to be added to `simple_db_if`. (P2-2)

---

## Summary Table

| Area | Status |
|------|--------|
| Trait definitions (nogc_sync_mut) | Complete, well-structured |
| Cross-variant re-export chain | Correct and consistent |
| Embedded tier conformance | None — disconnected |
| Full engine conformance | None — submodule empty |
| Unit test coverage | Facade-only (struct fields), no trait exercises |
| Feature test alignment | Misrouted (spostgre_if vs simple_db_if) |
| Design doc alignment | 2 gaps: wal_group_commit (P0), pmap_publish gen param (P2) |
