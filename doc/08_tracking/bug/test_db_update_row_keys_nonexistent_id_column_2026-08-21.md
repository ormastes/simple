# Test runs never finalize: SdnTable.update_row keys on a column no table has

- **Filed:** 2026-08-21
- **Status:** FIXED (fix in this change; reproduce spec green)
- **Severity:** HIGH — the test tracker published a vacuous green

## Symptom

`doc/08_tracking/test/test_result.md` (written 2026-08-18) reported
`Total 770 / Passed 0 / Failed 0 / Skipped 0` with every one of the 770 `tests`
rows carrying status `unknown`, and the last 10 rows of `test_runs` all stuck at
`status=running, test_count=0`:

```
run_1786933014662376, 1786933014663379, , 12345, dl, running, 0, 0, 0, 0, 0, true
```

A reader cannot distinguish that from a healthy suite that happens to have no
failures. It is a fail-open report.

## Root cause (two independent defects)

### 1. `update_row` matched on an `"id"` column that does not exist

`src/lib/nogc_sync_mut/database/core.spl` implemented `update_row`,
`update_row_if`, `get_row`, `mark_deleted` and `add_row`'s index insert against a
hardcoded primary key named `"id"`:

```
if current_row.get("id") == Some(key):
```

Of the nine tables in `test_db.sdn`, **only `strings` has an `id` column**.
`test_runs` keys on `run_id`; `tests`, `counters`, `timing` on `test_id`. So the
scan never matched, `update_row` returned `false`, and — because a row obtained
from a `for row in table.rows` loop is a copy under the bootstrap/native
receiver semantics documented in that same file — the mutated row was never
written back. Every in-place update was silently dropped, and every caller
ignores the `false` return:

- `test_extended/runs.spl` / `database.spl` `complete_run` → run stays `running`.
- the same files' `cleanup_stale_runs` → a crashed run is never marked `crashed`
  either, so an aborted run also stays `running` forever.
- `tracking.spl` / `database.spl` `update_counter`, `update_timing` → increments
  to an existing counter/timing row lost (only first-insert `add_row` survived,
  which is why counters look partly populated).

The run record IS opened and IS committed at the right place
(`test_runner_helpers.spl:236-250` calls `start_run` → `update_test_result` →
`complete_run` → `cleanup_stale_runs` → `save`), and `save()` does flush. The
loss is one layer below, in the row store.

### 2. `update_test_result` never wrote a verdict onto the `tests` row

`get_or_create_test` inserts `status_str = intern("unknown")`, and
`update_test_result` updated counters, timing and timing_runs but **never the
test row's `status_str`**. `test_count_by_status()` reads exactly that column,
hence `total=770, passed=0, failed=0` — correct arithmetic over data nobody ever
wrote.

## Fix

- `core.spl`: new `SdnTable.primary_key_column()` — `"id"` when the table really
  has one, else the table's first column. `add_row` / `update_row` /
  `update_row_if` / `get_row` / `mark_deleted` key on it.
- `test_extended/database.spl` + `test_extended/tracking.spl`: new
  `update_test_status(test_id, status)`, called from `update_test_result`.
  (Both files carry parallel copies of these methods; the `database.spl` copy is
  the one that wins at load time, so both were updated to stay consistent.)
- `test_runner/doc_generator.spl`: when the DB knows N>0 tests but holds a
  verdict for none of them, the generated report now says
  `ERROR — nothing was verified …` instead of publishing `0/0/0` as if healthy.

## Reproduce spec

`test/01_unit/lib/database/test_run_finalization_spec.spl` — 3 examples.
Pre-fix (verified by reverting `primary_key_column` to the old `"id"` behaviour):
`Results: 3 total, 0 passed, 3 failed`, exit 1. Post-fix: `Results: 3 total, 3 passed, 0 failed`.

## Not the cause

The compiler binary is present and runs (`bin/release/x86_64-unknown-linux-gnu/simple`,
the Rust seed). Runs did start and did reach `save()` — the WAL holding only a
checkpoint is consistent with rows being written but never *changed*.

## Follow-up (not fixed here, deliberately)

- Every `update_row` call site discards the `bool` return. A dropped update is
  still silent; callers should fail closed.
- `test_extended/database.spl` duplicates the method bodies in `runs.spl`,
  `tracking.spl` and `core_helpers.spl`. Two copies of a bug is how this one
  survived. They should be de-duplicated.

## Follow-up round 2 (2026-08-21)

### Discarded `update_row` bool — FIXED
`SdnTable.update_row_checked(key, row) -> Result<(), text>` is now the primary
API; a miss returns `Err("lost write: table '<t>' has no row with <pk>=<key>")`.
`update_row` is kept for genuine upsert call sites but delegates to it and
prints `[db] lost write: ...` on a miss, so a dropped write can no longer be
silent even where the bool is ignored. Converted call sites:
`database/server/txn.spl` (two sites — a lost write now returns
`commit_conflict`, i.e. genuinely fail-closed) and all five test-DB sites in
`test_extended/database.spl`. Reproduce spec:
`test/01_unit/lib/database/sdn_lost_write_spec.spl` (1 example, green;
pre-fix the method did not exist and the bool was discarded).

### Duplicated bodies — ATTEMPTED, REVERTED, still open
Deleting the duplicate bodies from `database.spl` and keeping only the
`impl TestDatabaseExtended:` blocks in `core_helpers.spl` / `runs.spl` /
`tracking.spl` / `queries.spl` compiles but FAILS at run time:
`semantic: method 'start_run' not found on type 'TestDatabaseExtended'`.
The extension modules are only loaded when something imports them, and the
import edge that would do it (`database.spl` -> `runs.spl`) is a cycle, since
those modules import `database.spl` for the class. So the duplication is held
in place by module loading, not by preference. Collapsing it needs a loader or
packaging change that is outside this fix; reverted rather than shipped broken.
Both copies were kept in sync in this change.

### Grammar defect hit while writing the spec — separate bug
`doc/08_tracking/bug/spec_val_match_parse_expected_let_found_dot_2026-08-21.md`.

### The `outcome=OK` / `failed=1` false green — SAME FAMILY, fixed separately
Confirmed to share this defect's shape (a failure computed correctly and then
discarded on the way out), but a different mechanism and code path. Recorded at
`doc/08_tracking/bug/test_runner_exits_zero_on_failed_spec_2026-08-21.md`.
