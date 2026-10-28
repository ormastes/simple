# Feature Expert: Build/Test Abnormality Detection

Start with `doc/04_architecture/simple_build_test_abnormality_detection.md` and preserve the three independent outcomes: scope enforcement, declared budget, and historical anomaly. Shared portable decisions belong in `src/lib/common/perf/execution_metrics.spl`; platform handles and observations belong at the existing process/runtime owner boundary.

Do not restore 137/139 heuristics, call RLIMIT_AS tree RSS, auto-ratchet approved baselines, pool incompatible cohorts, discard tail samples, or supervise modules by restarting the whole compiler. Keep native-host gaps explicit in the system-test and agent-task plans.

Current implementation map:

- `resource_scope.spl` owns fixed classes, cgroup/systemd enforcement, current-build scope, and truthful lower-quality fallback.
- when the caller's own cgroup cannot delegate `memory` (any login/tmux/`systemd-run --scope` shell), `_run_with_unix_limits` caps memory through a per-child `systemd-run --user --scope` (MemoryMax + TasksMax, `OOMPolicy=continue`, a supervisor shell reporting `memory.events`/`memory.peak`/`pids.events`) and only falls back to RLIMIT_AS when no user manager answers the probe. RLIMIT_AS counts reserved VA: the seed reserves ~1.2-1.5 GB it never touches, which is how 212 sweep specs aborted with `memory allocation failed` at 2.5 GB RSS under the 3 GiB Unit cap. Such a scope escapes the caller's own scope, so an outer MemoryMax no longer bounds children; the per-child cap is the bound. `resource_scope_memory_enforcement()` names the mechanism in effect.
- `test_runner_metrics.spl` owns stable class/cohort derivation shared by core, fork, and composite execution.
- the Linux delegated provider classifies OOM/PID/external termination only from retained provider markers or kernel counters; generic `resources`, 137, 139, and 143 statuses are insufficient.
- `execution_metrics_sdn.spl`, the test database resource-run table, and build subject/run ledgers keep stable subjects separate from volatile observations.

Before resuming verification, require an admitted source-matched Stage-4 binary. Windows Job receipt and macOS process-group receipt qualification remain visible in their `doc/08_tracking/todo/simple_build_test_abnormality_*_receipt_2026-08-24.md` records; Linux evidence cannot promote them.


## Native resource projection regression (2026-10-28)

Retained phase2 code can read imported `ScopedChildRun.usage` and
`budget_status` at offset zero after a `Result` tuple extraction. Preserve
resource evidence through owner-module projection helpers; nil substitution
would conceal the defect. Native tests must include distinct nonzero metrics,
absent evidence, and the limited-result path. See
`doc/08_tracking/bug/phase2_runner_tuple_resource_projection_2026_10_28.md` and
`scripts/check/check-native-resource-projection.shs`.


Native SDN group counters on the retained phase2 compiler need explicit array
mutation: indexed assignment can leave zero counts. See
`doc/08_tracking/bug/phase2_runner_indexed_group_accumulation_2026_10_28.md`
and the native `check-native-sdn-groups.shs` regression gate.


Public SDN aliases (`--sdn`, `--format sdn`, `--format=sdn`) must enter the same
transport admission path. Do not bypass unsupported V4 process ownership by
printing a partial legacy console summary. See
`doc/08_tracking/bug/test_runner_sdn_equals_transport_bypass_2026_10_28.md`.
