# Simple DB Embedded Tier — Hardening Audit

**Scope:** `src/lib/nogc_sync_mut/database/` + `src/lib/nogc_sync_mut/db_atomic.spl`
**Date:** 2026-05-23

---

## Current Capabilities

- **Atomic write-rename pattern** — `atomic_write` writes to `.tmp`, then renames; used by both `database/atomic.spl` and `db_atomic.spl`
- **File-based locking** — `FileLock` writes PID + timestamp to `.lock` file; stale lock detection by PID liveness and 2-hour age fallback
- **Multi-file atomic writes** — locks acquired in sorted path order to prevent deadlock; all writes committed atomically then all locks released
- **Write-Ahead Log (WAL)** — append-only pipe-delimited log; replayed on `SdnDatabase.load()` for crash recovery
- **Backup rotation** — `create_backup` maintains numbered `.bak.N` files up to configurable `backup_count`
- **Soft delete** — `mark_deleted` / `delete_row` sets `valid=false`; `valid_rows()` filters; `compact_table` hard-deletes on demand
- **Optimistic locking** — `update_row_if(key, row, expected_version)` version-check with `Err` on mismatch
- **QueryBuilder** — fluent interface: `filter_by`, `filter_in`, `only_valid`, `order_by`, `take`; CompareOp: Eq, Ne, Gt, Ge, Lt, Le, Contains, StartsWith, EndsWith, InSet; SIMD-accelerated bitmap path for >2 filters
- **Schema checker** (`checker.spl`) — `check_required_fields`, `check_empty_required`, `check_duplicate_ids`, `check_valid_column`, `check_foreign_key`, `check_file_refs`, `check_interner_range`, `check_enum_values`
- **Auto-fix functions** — `fix_remove_duplicates`, `fix_invalid_valid`, `fix_stale_running`, `trim_whitespace`
- **DbMetrics** — counters for read/write/compaction/WAL-replay; snapshot-able
- **BugDB, TestDB, FeatureDB** — domain databases with full CRUD; BugDB has statistics; FeatureDB has multi-mode status tracking
- **TodoDB** — read-only wrapper with documented bypass warning; write path not migrated
- **StringInterner** — bidirectional `str_to_id` / `id_to_str` dictionaries, monotonically incrementing ID counter; survives SDN round-trip
- **Compaction** — `compact_table` and `compact_database`; `should_compact(threshold)` for ratio-based trigger
- **SDN quote-aware parsing** — `split_sdn_row` handles quoted comma-containing values
- **Safety guard** — refuses to overwrite non-empty file with empty content

---

## Missing Features

- **P0 — WAL replay does not deserialize row data**: `WalEntry.data` is stored as raw text but replay only calls `t.add_row(SdnRow(fields: {}, _version: 0))` — a blank row, discarding all field data. WAL replay produces phantom empty rows, not real data recovery.
- **P0 — TodoDB write path bypasses atomic ops**: `todo_scan` writes `todo_db.sdn` directly via `file_write()`. The module self-documents this as a bypass but marks it only as a warning, not an error. Concurrent tool runs can corrupt the file.
- **P1 — No fsync before rename**: Neither `atomic.spl` nor `db_atomic.spl` calls `fsync`/`fdatasync` on the temp file before rename. On Linux with `ext4` (default), `rename` is durable but the written data may be in the OS page cache. A power loss after rename but before writeback loses the new content while the old file is gone — silent data loss.
- **P1 — Lock file creation is TOCTOU-racy**: `try_create_lock` does `file_exists` → (gap) → `file_write`. Two processes can both see no lock file and both write their PID. The later writer wins silently; no O_EXCL/O_CREAT atomic create is used. This defeats the entire locking mechanism under race conditions.
- **P1 — No QueryBuilder support for IS NULL / field-absent filtering**: Fields absent from a row are treated identically to empty string in comparisons. There is no way to distinguish "field not present" from "field present but empty", which affects completeness queries on optional columns.
- **P2 — FeatureDB `update_feature` appends instead of replacing**: `update_feature` calls `features_table.add_row(feature_to_row(feature))` without first deleting the old row. If the underlying `add_row` does not upsert by key, duplicate rows will accumulate, bypassing the duplicate check.
- **P2 — No WAL truncation / checkpoint rotation**: WAL file grows unboundedly. Checkpoint writes a sentinel entry but does not truncate the file. On large/long-running deployments the WAL can grow to hundreds of MB, making replay slow.
- **P2 — Backup does not clean up on rollback**: If `atomic_write` fails after creating the backup, the backup accumulates. Multiple failure bursts can fill disk with stale backups, especially with `backup_count=0` (keep-all default in some call sites).
- **P3 — StringInterner has no unintern / remove**: IDs grow monotonically; deleted strings remain in the interner and in the SDN `strings` table after compaction. This is a slow memory and file-size leak for long-lived databases with frequent churn.
- **P3 — No numeric-aware Gt/Lt comparison**: All CompareOp comparisons use lexicographic text comparison. `filter_by("count", CompareOp.Gt, "9")` will yield wrong results for multi-digit numbers ("10" < "9" lexicographically).
- **P3 — TestDB not migrated**: The comment in `test.spl` says "Test runner currently uses custom implementation in `src/app/test_runner_new/test_db_*.spl` (TO BE MIGRATED)". The unified library TestDB is unused in production.

---

## Hardening Gaps

- **[P0] WAL replay silently drops all field data** — see Missing Features P0 above. Crash recovery produces a valid-looking database with blank rows.
- **[P0] TOCTOU lock race** — two concurrent writers can both acquire the "lock" simultaneously, leading to interleaved writes and potential file corruption.
- **[P1] No fsync / fdatasync** — rename without fsync is not crash-safe on all filesystems (XFS with `nobarrier`, some NFS/FUSE, all network mounts). The write-rename pattern is only durable on local ext4 with default mount options.
- **[P1] Temp file not cleaned up on write failure** — if `file_write(temp_path, content)` succeeds but rename fails, the `.tmp` file is left on disk. Repeated failures accumulate orphaned temp files. The multi-write variant in `atomic.spl` has partial rollback logic, but the single-file path does not.
- **[P1] SDN parse silently ignores unparseable sections** — `SdnDatabase.load` skips sections where `parse_sdn_table` returns nil with a comment "Ignore any section that does not parse as a table." A truncated or partially-written section is silently dropped — the database loads successfully but with missing tables.
- **[P2] Stale lock heuristic is weak** — PID reuse on Linux (PIDs wrap at 4M) can cause a live process to be identified as the dead lock holder; the 2-hour fallback is too coarse. Production lock files from stuck jobs will block all writers for 2 hours.
- **[P2] `atomic_append` used for WAL without fsync** — WAL entries are appended with `atomic_append`, which acquires the file lock but (per the fsync gap above) does not guarantee durability before returning. The comment "atomic_append which syncs per call" in `wal.spl` is inaccurate if `rt_file_write_text` does not call fsync.
- **[P2] SDN value with newlines or double-quotes breaks round-trip** — `quote_if_needed` only quotes when commas are present. A field value containing a literal newline will corrupt the row format on export. A field containing `"` characters is not escaped, breaking the quote-aware parser on re-read.
- **[P2] `validate()` errors array returned but callers rarely act on it** — `SdnDatabase.validate()` returns `[text]` errors but most call sites in the domain DBs call `save()` unconditionally without checking `validate()` first.
- **[P3] StringInterner IDs loaded with `id > 0` guard, skipping ID 0** — `from_sdn` skips entries where `id_str.to_int()` returns 0 or parse fails, and `next_id` starts at 0. If ID 0 is ever interned and saved, it will be silently dropped on reload — off-by-one in interner persistence.

---

## Recommendations (Prioritized)

1. **[P0] Fix WAL replay to deserialize row fields** — Store row data as SDN-encoded text in `WalEntry.data`; parse it back into `SdnRow.fields` on replay. Without this, WAL is decorative.
2. **[P0] Fix lock creation race with O_EXCL** — Replace `file_exists` + `file_write` with an atomic create-exclusive (`rt_file_create_excl` extern or `open(O_CREAT|O_EXCL)`). Fail immediately if the file already exists; retry only on failure.
3. **[P1] Add fsync before rename** — After writing the temp file, call `fsync(fd)` (or `file_sync(path)` if the runtime provides it) before renaming. Alternatively, document the durability assumption explicitly and let callers opt into `strict` mode.
4. **[P1] Clean up temp file on rename failure** — In the single-file `atomic_write` path, `file_delete(temp_path)` on failure. Mirror the multi-file rollback logic.
5. **[P1] Treat unparseable SDN sections as fatal or log them** — Return an error (or at minimum a warning list) from `SdnDatabase.load` when sections are skipped, so callers can detect truncated databases.
6. **[P2] Fix `update_feature` to delete-then-insert** — Check if a row with the same ID exists before calling `add_row`; if so, call `mark_deleted` first (or use `update_row_if` for optimistic replace).
7. **[P2] Add WAL truncation on checkpoint** — After writing a Checkpoint entry and saving the database, truncate (or rotate) the WAL file to prevent unbounded growth.
8. **[P2] Escape newlines and double-quotes in SDN export** — In `quote_if_needed`, also quote (and escape) values containing `\n`, `\r`, or `"`.
9. **[P2] Migrate TodoDB write path** — Move `todo_scan`'s `file_write` calls to use `atomic_write` through the shared library. This is the only database with a known bypass.
10. **[P3] Add numeric-aware comparisons to QueryBuilder** — When both sides of Gt/Lt/Ge/Le parse as integers or floats, use numeric comparison; fall back to lexicographic otherwise.
11. **[P3] Add StringInterner unintern / compaction** — On `compact_database`, rebuild the interner from scratch using only strings referenced by valid rows; renumber IDs and rewrite the `strings` table.
12. **[P3] Fix interner ID-0 off-by-one** — Change `from_sdn` to use `id >= 0` (or check parse success independently from value) and initialize `next_id` to `max_seen_id + 1`.
