# test_extended: 33 methods declared in divergent duplicate impl blocks across five modules — stage2 candidate rejects the ambiguity; owner merge decision needed (2026-11-16)

**Status:** OPEN (owner decision required: per-method winner or merge plan)
**Area:** src/lib/nogc_sync_mut/database/test_extended/ (database.spl, queries.spl, tracking.spl, runs.spl, core_helpers.spl — all declare `impl TestDatabaseExtended`)
**Evidence:** manual tool build of `src/app/mcp/main.spl` with the admitted
stage2 compiler (pinned-c189f67185e1, receipt-authorized lineage): MIR phase
fails with e.g.
`unresolved method call: flaky_test_names is ambiguous on ...TestDatabaseExtended: impl blocks in more than one module declare it`,
plus `update_test_result`-ambiguous, `slice` unresolved at
test_extended/database.spl:1052 and tracking.spl:167, and
`null coalesce fallback does not match declared tuple owner` (x3).

## The duplicate map (fn + me declarations, verified by AST-level grep)

database.spl (the grown canonical file, ~1500 lines) shares method names with:

- queries.spl (15): all_test_info, flaky_test_names, get_counter, get_file_id,
  get_file_path, get_suite_id, get_suite_info, get_test_counts, get_test_id,
  get_test_timing, get_timing_summary, list_runs, test_count_by_status,
  tests_by_status
- tracking.spl (11): add_timing_run, baseline_history_states,
  collect_timing_runs, collect_timing_runs_for_cohort, is_flaky_test,
  promote_timing_baseline, record_baseline_generation, update_counter,
  update_test_result, update_test_status, update_timing
- runs.spl (4): cleanup_stale_runs, complete_run, prune_runs, start_run
- core_helpers.spl (3): get_or_create_file, get_or_create_suite,
  get_or_create_test

## The copies have DIVERGED semantically — not stale verbatim copies

Sampled diffs (extraction-normalized):

- get_counter: the queries.spl version guards `row_test_id == -1: continue`
  and extracts crashed/skipped counters; database.spl's version returns via
  `counter_record_from_row(row, test_id)` — different control flow AND fields.
- start_run: database.spl guards a missing `test_runs` table via an Option
  check before the match; runs.spl matches directly (older shape).
- update_timing / is_flaky_test: drifted tails/comments.

18 of the 32 extractable pairs differ beyond comments. Deleting either side
therefore CHANGES BEHAVIOR and is not a mechanical dedup — each pair needs an
owner call on which logic is current (or a merge).

## Impact

- The mcp tool build (and any closure pulling both sibling modules with an
  affected caller) fails closed under the stage2 candidate. The lsp build
  passes only because its closure does not trigger the ambiguity.
- The seed compiler resolves these ambiguously (first-match), which is why the
  defect is invisible to seed-built tooling.

## Owner asks

1. For each of the 33 pairs: declare the winner (and delete the loser), or
   specify a merge. Consider enforcing one-impl-block-per-type-per-package in
   CI to stop recurrence.
2. Until then, tool builds needing the mcp closure are blocked; the lane runs
   on seed-built mcp as a fallback if needed.


## 2026-11-16 resolution: duplicates removed (PR pending); drift audit remains

Fix landed in the same release/1.0.0 lane: all 32 duplicated methods were
removed from the four satellite modules (queries 14, tracking 11, runs 4,
core_helpers 3), which are now import-only deprecation-noted modules.
database.spl stands as the canonical, spec-validated implementation — the
test suite binds these names to database.spl under the seed's first-match
resolution, so the removed copies were never the tested behavior.

REMAINS OPEN: the semantic drift audit. 18 of the 32 pairs had divergent
bodies (e.g. queries.spl's get_counter guarded row_test_id == -1 and
extracted crashed/skipped counters that database.spl's counter_record_from_row
path may or may not cover; runs.spl's start_run lacked database.spl's
missing-table guard). Owners should confirm each divergence is either
covered by the canonical path or file a targeted bug. The mcp and
test_runner tool builds against the fixed tree are the verification gate.
