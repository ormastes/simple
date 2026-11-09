# Bug DB per-bug shards (2026-11-09)

## Problem
`doc/08_tracking/bug/bug_db.sdn` is one ~9k-line SDN file (tables `strings`,
`bug_descriptions`, `bugs_active`, `bugs`, `bug_investigation_logs`,
`bug_fix_strategies`, `bug_difficulty`, `bug_fix_claims`, `bug_scope`) sealed by
one `bug_db.<algo>_<hex>.csm` sidecar. ~30 parallel fix PRs each edit 1-3 rows,
so every merge stales every other PR's seal: constant merge+reseal churn,
rewinds, duplicate rows and a serialized landing bottleneck.

## Design (minimal schema change)
* **Legacy file is frozen.** `bug_db.sdn` and its `.csm` are read-only from now on;
  no writer rewrites them.
* **One shard per bug:** `doc/08_tracking/bug/db/<bug_id>.sdn` holds every row of
  that bug across all bug tables (same table names and columns as the legacy
  file; only non-empty tables appear). Each shard is sealed by its own `.csm`
  sidecar exactly like the legacy file (`config/check/sdn_seal_policy.sdn` lists
  `doc/08_tracking/bug/db/*.sdn`, xxh3). A shard with no rows (strings table
  only) is a tombstone: the bug is deleted.
* **Merge rule:** shard mode is on iff the `db/` directory exists. The loader
  reads the legacy file, then every shard in C-sorted filename order; a shard
  REPLACES every legacy row of its bug id (`id` / `bug_id` column). Sorting
  makes the merged view, and every report generated from it, deterministic.
* **Fail-closed validation:** an unreadable/stale-sealed shard, a shard row whose
  id is not the file stem (a duplicate or misplaced bug across shards), an
  unknown table, or a column mismatch rejects the whole database with the reason
  (`load_bug_database_checked`), the same way a stale legacy seal always did.
* **Writer:** `BugDatabase.save()` snapshots each bug's canonical shard payload at
  load and, on save, writes only the shards whose payload changed (new bug,
  status change, log line). Untouched bugs write nothing, so two PRs editing
  different bugs touch disjoint files and merge with no conflict.

## Code
* Loader/writer: `src/lib/nogc_sync_mut/database/bug.spl` (`load_bug_database`,
  `load_bug_database_checked`, `bug_shard_dir`, `_bug_merge_shards`,
  `_bug_shard_dbs`, `BugDatabase.save`, `pending_shard_ids`). Every pure-Simple
  consumer (`bug-add`, `bug-resolve`, `check-dbs`, `fix-dbs`, workaround store
  snapshot, MCP bugdb query) goes through `load_bug_database`, so they are
  shard-aware without further change.
* Shell twin: `scripts/check/bug-db-shard.shs` (`merged`, `extract`, `write`,
  `changed`, `check`, `--selftest`). `bug-claim.shs` and
  `sync-tracking-db-status.shs` edit a merged working copy and publish one
  shard per changed bug; `check-bug-status-consistency.shs`,
  `check-tracking-doc-registration.shs` and `check-tracking-db-unique-ids.shs`
  read the merged view. `check-tracking-db-unique-ids.shs` (push tier) also
  fails on any shard whose row ids differ from its stem and on a bug id present
  twice in the merged view. The existing seal gate (`check-sdn-crc32-sealed.shs`)
  verifies shard sidecars because they are policy-listed.
* Spec: `test/01_unit/lib/database/bug_db_shards_spec.spl` (parity with/without
  shard dir, only-touched-shard written + legacy byte-identical, two branches
  via disjoint files, duplicate id across shards rejected).

## Counting bugs

Count open bugs ONLY via `sh scripts/check/bug-db-shard.shs merged`; it unions both
tables (`bugs_active` and the legacy `bugs`, shards applied). The tally form is
`sh scripts/check/bug-db-shard.shs count`, which prints `<table> <severity> <status> <n>`
plus `TOTAL` rows across both tables. Counting `bugs_active` alone undercounted
open P2 on 2026-11-09 (31 vs 164). New still-real rows belong in `bugs_active`;
the legacy `bugs` table is being drained to closed history.

## Not changed (named gaps)
* `src/app/bug_gen/main.spl`, `src/app/tracking/main.spl`, `src/app/stats/*`,
  `src/compiler/90.tools/stats/*` and the Rust seed `driver/src/bug_db.rs` read
  the legacy file as text; they see pre-freeze rows only until pointed at the
  merged view (`bug-db-shard.shs merged` or `load_bug_database`).
* No bulk migration: existing rows stay in the frozen legacy file; a bug moves
  into a shard the first time it is edited.
