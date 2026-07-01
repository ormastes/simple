-- DbStorage — Lean 4 formal model of the Simple DB storage engine invariants.
-- Wave 3b; plan: doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md
-- Source of truth:
--   src/os/services/nvfs/core/pmap_btree.spl   (B-tree)
--   src/lib/nogc_sync_mut/storage/shared/wal.spl (WAL / SharedWal)
--   src/lib/nogc_sync_mut/db/dbfs_engine/mvcc.spl (MVCC)
--   src/lib/nogc_sync_mut/db/dbfs_engine/txn.spl  (Txn protocol)
--   src/lib/nogc_sync_mut/db/dbfs_engine/pager.spl (Pager)
import DbStorage.BTree
import DbStorage.Wal
import DbStorage.Mvcc
import DbStorage.Theorems
