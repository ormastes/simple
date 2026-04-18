# NVFS Submodule State

Tracks milestone progress and key file/test counts for each phase.

---

#### 9-N5b-btree-rebalance

- **FR:** FR-NVFS-N5b-001 — Status flipped to `Implemented`
- **Files changed:**
  - `src/core/pmap_btree.spl` — added `btree_borrow_from_left`, `btree_borrow_from_right`, `btree_merge_with_right`, `_delete_recursive`, `pmap_btree_is_empty`, invariant comment block; removed stub `_remove_leaf_key`. ~360 lines total (+210 lines net).
  - `test/unit/pmap_btree_rebalance_test.spl` — new, 8 rebalance tests.
- **Test pass counts:** pmap_btree_test.spl: 8 passed; pmap_btree_rebalance_test.spl: 8 passed.
- **Lint:** clean (no output).
- **Submodule SHA:** `d613620bb2bbf0ee85288e0239935c8bfd82dea9`
