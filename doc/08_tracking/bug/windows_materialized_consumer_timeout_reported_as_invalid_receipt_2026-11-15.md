# Windows materialized consumer timeout reported as "receipt is invalid"

- **Status:** verification-pending
- **Date:** 2026-11-15
- **Area:** bootstrap / Windows symlink materialization
- **Related:** `windows_materialized_symlink_alias_git_state_timeout_2026-09-09.md`,
  `resume_stage3_materialized_links_dir_junction_refusal_2026-11-14.md`

## Symptom

`bootstrap-windows.sh --full-bootstrap --stop-after-stage2` (worktree
`C:/dev/wt/caret-native`, commit `7ce10415611`) aborted `stage=starting exit=1`
with `error: Windows materialization receipt is invalid: ...windows-materialized-links.2837239.env`
right after a clean 2h materialization (created=62 failed=0, result=complete).
No `stage3-materialized-consumer: <reason>` line was printed.

## Root cause

The receipt was valid. Running the native consumer directly against it with
`BOOTSTRAP_STAGE3_GIT_MAX_MILLISECONDS=900000` returned 0 after **489s**.

`bootstrap_stage3_materialized_git_state` (`scripts/check/lib/bootstrap-stage3/authority.shs`):

1. The default budget was `300s x (1 + load1/ncpu)`. With integer division on an
   80-thread host the scale is always 1, so the budget was a fixed 300s. That
   is below the C# consumer's own default/ceiling of 1200s.
2. The outer `timeout` was budget + 30s = 330s. PowerShell startup and the
   `Add-Type` compile run before the C# clock starts, so the outer kill fired
   first. That is why no C# `bound.time` message appeared.
3. Any non-zero exit, timeout included, was reported as "receipt is invalid"
   with advice to `--undo` and re-materialize, which throws away a 2h valid
   materialization.

## Fix

- Default budget = 1200000 ms (the native ceiling). Outer kill = budget + 120s.
- A timeout (124/137 from `timeout(1)`) exits 3 with a "timed out, receipt not
  judged" message. `bootstrap_materialized_startup` reports that without
  `--undo` advice and still fails closed.
- Validation itself is unchanged.

Repro/prevention test: `scripts/bootstrap/tests/materialized-consumer-timeout-test.shs`.

## Workaround (before the fix lands)

Supply the existing receipt and the ceiling budget:

```sh
export SIMPLE_WINDOWS_MATERIALIZED_LINKS_RECEIPT=<receipt.env>
export BOOTSTRAP_STAGE3_GIT_MAX_MILLISECONDS=1200000   # values > 1200000 are rejected
```
