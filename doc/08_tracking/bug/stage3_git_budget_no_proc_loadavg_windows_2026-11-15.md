# Stage3 git-state budget stays 300 s on Windows (no /proc/loadavg)

Status: verification-pending

`bootstrap_stage3_materialized_git_state` (scripts/check/lib/bootstrap-stage3/authority.shs)
scaled its time budget by `/proc/loadavg`. Git Bash on Windows has no such file, so
the scale collapsed to 1 and the budget stayed 300 s; a full-checkout walk exceeds it and
preflight failed with `bound.time` / `preflight bind: bootstrap_stage3_git_state failed`.
Workaround was `BOOTSTRAP_STAGE3_GIT_MAX_MILLISECONDS=1200000`.

Fix: budget computation extracted to `bootstrap_stage3_git_budget_ms`; when load is
unavailable it uses the 4x cap (1200000 ms). Readable loadavg behavior unchanged.
The explicit env override still wins.

Test: `sh scripts/check/bootstrap-stage3-git-budget-self-test.shs`
(RED before: function missing; GREEN after: no-loadavg=1200000 idle=300000 busy=900000).
Not covered: a real Windows preflight run.
