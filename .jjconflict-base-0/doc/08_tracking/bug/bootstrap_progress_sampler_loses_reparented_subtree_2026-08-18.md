# bootstrap-progress-watch tree RSS silently loses re-parented / unreadable
# subtrees (2026-08-18) -- FIXED

A stage-3 compile measured at 67.4 GB by `ps` logged
`tree_rss_kb=34753460` (34.7 GB) at the same instant -- a reported TOTAL smaller
than a single live process. Anyone sizing the stage-3 memory defect from
`bootstrap-progress.log` got half the truth.

## Not the cause

Field extraction is exact. Verified against a live 18 GB process:
`/proc/<pid>/stat` field 24 via `a[22]` after stripping through the last `") "`
gives 18444392 KB against `VmRSS: 18446948 kB`. Indices, page scaling and the
`set --` plumbing are all correct.

## Cause

`process_tree_metrics` defines the tree by PARENT CHAIN only: `included[root]=1`
then fixpoint over `included[parent[pid]]`. Two ways a live process leaves that
set with no signal:
- it is re-parented (its intermediate parent exits and it is inherited by init
  or a subreaper) -- routine for `native-build --threads 2` workers;
- any ancestor's `/proc/<pid>/stat` read fails, which drops that ancestor AND
  every descendant, because inclusion propagates only through loaded parents.

## Fix

Sum a SECOND, independent basis and report it alongside: the process GROUP does
not move when a parent dies. New fields on every `event=sample` line:
`tree_rss_pgroup_kb`, `tree_pgroup_processes`, `tree_scan_misses` (pids whose
stat read failed). `tree_rss_kb` keeps its parent-chain meaning so existing
readers are unaffected; `pgroup >> chain` now means "the chain lost a subtree",
and a nonzero `tree_scan_misses` is no longer invisible.

## Test

`test/01_unit/scripts/bootstrap_progress_watch_tree_test.shs` asserts the three
fields are numeric and that `tree_rss_pgroup_kb >= tree_rss_kb`.
NEGATIVE CONTROL RUN: with `scripts/bootstrap/bootstrap-progress-watch.shs`
reverted, the test fails `FAIL: tree_rss_pgroup_kb is not numeric:` (rc 1).
Patched, those assertions pass.

PRE-EXISTING, UNRELATED, NOT FIXED HERE: the same test already failed at
`FAIL: leaf tree RSS differs from root RSS` on unpatched origin/main -- a
`ps -o rss=` vs `/proc/<pid>/stat` skew in the leaf fixture. Byte-identical
failure before and after this change.
