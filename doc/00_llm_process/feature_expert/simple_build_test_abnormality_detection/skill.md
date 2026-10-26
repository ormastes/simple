# Feature Expert: Build/Test Abnormality Detection

Start with `doc/04_architecture/simple_build_test_abnormality_detection.md` and preserve the three independent outcomes: scope enforcement, declared budget, and historical anomaly. Shared portable decisions belong in `src/lib/common/perf/execution_metrics.spl`; platform handles and observations belong at the existing process/runtime owner boundary.

Do not restore 137/139 heuristics, call RLIMIT_AS tree RSS, auto-ratchet approved baselines, pool incompatible cohorts, discard tail samples, or supervise modules by restarting the whole compiler. Keep native-host gaps explicit in the system-test and agent-task plans.

Current implementation map:

- `resource_scope.spl` owns fixed classes, cgroup/systemd enforcement, current-build scope, and truthful lower-quality fallback.
- `test_runner_metrics.spl` owns stable class/cohort derivation shared by core, fork, and composite execution.
- the Linux delegated provider classifies OOM/PID/external termination only from retained provider markers or kernel counters; generic `resources`, 137, 139, and 143 statuses are insufficient.
- `execution_metrics_sdn.spl`, the test database resource-run table, and build subject/run ledgers keep stable subjects separate from volatile observations.

Before resuming verification, require an admitted source-matched Stage-4 binary. Windows Job receipt and macOS process-group receipt qualification remain visible in their `doc/08_tracking/todo/simple_build_test_abnormality_*_receipt_2026-08-24.md` records; Linux evidence cannot promote them.
