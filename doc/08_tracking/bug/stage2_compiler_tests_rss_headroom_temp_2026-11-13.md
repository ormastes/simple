# Stage 2 compiler tests: TEMPORARY small-host RSS headroom relaxation (2026-11-13)

Status: OPEN (temporary workaround in place). Remove the workaround when the
removal condition below is met.

## Why

On the Windows release/1.0.0 bootstrap host, other sessions held about 30 GB.
The Stage 2 compiler-test matrix therefore ran in small-host one-worker mode,
where the process-tree RSS cap is 3/4 of the memory available when the matrix
starts. Two runs got caps of 18 GB and 24 GB. The full-CLI compile inside the
matrix peaks at 24.3 GB during HIR, so both runs aborted with exit 88
(`rss-cap-exceeded`, enforced by `scripts/bootstrap/bootstrap-session-exec.c`).

A real fix for the full-CLI compiler's peak RSS is being done separately. The
owner asked to lower the test runner's headroom temporarily until that fix
lands.

## Formula

`bootstrap_tree_rss_whole_build_plan` in
`scripts/bootstrap/lib/tree-rss-policy.shs` (small-host branch). It is used only
by the Stage 2 compiler-test phase, through `bootstrap_tree_rss_whole_build_export`
(`bootstrap-from-scratch.sh` and `admit-built-stage2-compiler-tests.shs`).

- Old: `budget = min(MemTotal x 75%, 3/4 x MemAvailable)`, with
  `cap = budget` and one worker.
- New: `budget = max(old, min(MemTotal x 75%, MemAvailable - 4 GiB, one-worker
  requirement))`, where the one-worker requirement is the 4 GiB phase base plus
  16 GiB x 150% (29360128 KiB), i.e. the normal plan's one-worker cap. Still one
  worker. The relaxed budget only applies when it is larger than the old one, so
  the change never adds a refusal and never lowers a cap.
- Constant: `BOOTSTRAP_TREE_RSS_SMALL_HOST_TEMP_HEADROOM_KIB=4194304`.
- When the relaxed term sets the budget, the plan bound is
  `small-host-one-worker-temp`. This value is published as
  `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_BOUND` and recorded in the watchdog
  receipt (`--cap-bound`). The budget text in the plan summary starts with
  `TEMPORARY`. This follows `.claude/rules/bootstrap.md`: a memory relaxation
  has to be visible in receipts.

Example, 31 GiB (32505856 KiB) available on a 128 GB host: the old cap was
24379392 KiB (23.25 GiB) and the new cap is 28311552 KiB (27.0 GiB).

Unchanged:

- An explicit `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` still bypasses the
  plan.
- The normal (non-small-host) plan, the worker count, timeouts and other lanes'
  caps are unchanged.
- The relaxed cap stays below the 48 GiB default ceiling, so the elevated-ceiling
  admission (3/4 of available) is never requested.

`SIMPLE_BUILD_MEMORY_RESERVE_BYTES` is not changed. Its native-build start gate
(24 GiB on hosts of 48 GiB and above) refuses only when less than 24 GiB is
available. At that level even the relaxed cap (at most about 20 GiB) is below
the 24.3 GB peak, so the gate is not what is blocking these runs.

## Removal condition

The full-CLI peak RSS fix has landed, and the Stage 2 compiler-test full-CLI
build's peak RSS has been re-measured from a watchdog receipt. Then delete
`BOOTSTRAP_TREE_RSS_SMALL_HOST_TEMP_HEADROOM_KIB`, its block in
`bootstrap_tree_rss_whole_build_plan`, and the `small-host-temp-*` selftest
fixtures, and close this record.
