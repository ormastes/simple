# runtime-api-regression push gate: false FAIL on release/1.0.0 PRs (2026-11-23)

Status: open (defect 2 fixed, verification-pending; defect 1 open). Gate: `push-runtime-api-regression` (`scripts/check/check-runtime-api-regression-push.shs`).

## Symptom
Pushing `work/mu1-20261122` (PR #10783, merged as `c3bb41538e4` into release/1.0.0)
FAILed with 11 `rt_core_dict_*` symbols "removed".

## Evidence (worktree C:/dev/wt/rtd1 at origin/release/1.0.0 `e1141effaa6`)
- `c3bb41538e4^1..c3bb41538e4` -> PASS, 3804 checked, 0 removed.
- `c3bb41538e4^2~1..c3bb41538e4^2` -> PASS, 0 removed.
- `merge-base(origin/main, PR head)=65e3a69e676..c3bb41538e4^2` -> FAIL, 9 removed
  (`rt_core_dict_sort_entry_less`, `rt_core_immortal_registry_*`, ...). This range
  spans the release line's own history, not the PR's delta.
- Every `rt_core_dict_*` that disappeared over release history was a `static`
  helper renamed on purpose:
  `589125e1a57` (order_cmp/order_oom/ordered_slots/put_seq -> `core_dict_*`),
  `b9721bcb2d5` (scope_read_checked_v/heap_v), `bbd62986925` (entries_bytes/free),
  `23e7ba475f9` (sort_entry_less removed by insertion-order dicts).
  Tip `runtime_native.c` still defines the full pre-`acc30fdfae3` set (+`rt_core_dict_find`).
  The Rust runtime defines no `rt_core_dict_*` at all.

## Defects
1. Range: when the local `refs/remotes/origin/release/1.0.0` is stale (seen here:
   `cannot lock ref ... expected a8bb3822...`) the push dispatcher falls back to
   main's merge-base, so the whole release-only history is attributed to the PR.
2. Classification: the guard counts `static` C functions as exported runtime API.
   Static helpers are file-internal, not `rt_*` ABI; renames of them should not count.

## Fix direction
Skip `static` definitions in the C symbol extraction; fail closed (ERROR, not FAIL
with a wrong base) when the PR-base ref cannot be verified as current.

## Defect 1 fix (lane gs2, 2026-11-23)
`main_merged_predecessor` (`scripts/check/check-push-must-pass.shs`) now uses local
tracking refs only to decide whether narrowing applies. Whenever it does, or the
outgoing range contains a merge, the base comes from the LIVE remote lines via
`rebased_push_published_base` (ls-remote + bounded object fetch of main,
release_phase3, release/<x.y>); a stale or missing `refs/remotes/origin/release/*`
can no longer make main's merge-base win. If the live lines cannot be confirmed the
function returns 2 and the dispatcher prints `ERROR — nothing was checked` (exit 2)
instead of running gates over a wrong range. Selftest (`--self-test`, release
fixture): topic off release/9.9 (differs from main) with the tracking ref deleted,
then rewound — base must equal the live release tip and the range must be exactly
the topic's 2 own commits; an unreachable push remote must yield rc 2.
Defect 1 status: fixed, verification-pending. Behaviour change: a fast-forward push whose
range contains a merge now makes a bounded live `ls-remote` (+ possible object fetch);
when that fails the push exits 2 and must be re-pushed after `git fetch` (intended
fail-closed). Note: `--self-test`'s pre-existing slow-remote and release_phase3
fixtures are timing-sensitive on a loaded Windows host (passed with
`MUST_CHECK_REMOTE_QUERY_TIMEOUT_S=60`, 34/34).

## Defect 2 fix (2026-11-23, branch work/gs1-20261123)
`defined_symbols_c` now drops literal C definitions whose declaration prefix
contains `static` (`static`, `static inline`, ...) before extracting names.
Test-first: new selftest fixture F renames 5 `static rt_core_dict_*` helpers
and must PASS (red before the fix, green after: 6/6 fixtures). The incident
fixture A still FAILs.
Real range `65e3a69e676..c3bb41538e4^2` with the fix:
`PASS — 3282 symbol(s) checked, 0 removed` (pre-fix: `FAIL — 3813 checked, 9 removed`; the 531-symbol drop is the excluded `static` helpers).
