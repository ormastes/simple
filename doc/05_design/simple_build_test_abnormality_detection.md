# Detailed Design: Simple Build/Test Abnormality Detection

UI design is N/A: this feature exposes structured records, CLI diagnostics, and test/build policy; it adds no TUI or GUI interaction surface.

## Portable model

`src/lib/common/perf/execution_metrics.spl` defines the evidence, identity, budget, baseline, and anomaly value types. Pure helpers validate evidence, classify termination from explicit event flags, canonicalize identity fields, evaluate budgets, compute median/MAD thresholds, preserve approved baselines, and detect missing required spans.

`ExecutionResourceScope` is a facade, not a serialized handle. Its provider returns a final `ResourceUsage`; the record carries `ExactTree`, `ExactDirectChild`, `SampledTree`, `ProcessOnly`, or `Unavailable` quality.

## Termination precedence

Infrastructure failure > internal wall/no-progress watchdog > cgroup/job memory event > PID event > CPU event > explicit signal > normal exit > unverified external termination. An exit code is retained as evidence but does not manufacture the cause.

## Budget and anomaly decisions

Budget evaluation compares each configured maximum directly against the observation and never reads a baseline. Anomaly evaluation rejects incompatible/non-approved cohorts, validates required spans/counters, and then requires all three deltas: absolute floor, relative floor, and robust MAD multiplier. A failure needs a confirming candidate run. Zero MAD uses the absolute and relative floors and treats any positive excess beyond the configured noise floor deterministically.

Baseline promotion returns a new approved record and supersedes the prior record; recording a run never invokes promotion.

The test database persists each generation in `baseline_history`. A later promotion changes only the prior generation's lifecycle field to `superseded` and appends the new approved generation; its cohort, samples, median, generation, and promotion timestamp remain frozen.

## Persistence

`test_db.sdn` and `build_db.sdn` contain stable identities/policies. `test_db_runs.sdn` and `build_db_runs.sdn` append observations. Large traces and profiles use content-addressed references. Schema versions and tool digests are part of identity/invalidation.

## Integration sequence

1. Replace the false 137/139 classifier behind the existing process-limit facade with explicit evidence input while retaining a compatibility result adapter.
2. Add the observed-process runtime sibling API (`wait4`/rusage on Unix; Job accounting on Windows) and provider-owned process-tree scope.
3. Extend test result/run serialization.
4. Add compiler phase spans/counters and build-run persistence.
5. Add CLI/policy integration and explicit baseline promotion.

## Implemented foundation (2026-08-24)

- `src/lib/common/perf/execution_metrics.spl`: portable resource/termination evidence, declared budgets, phase/span/work models, cohort keys, frozen robust comparisons, explicit promotion, gradual-drift state, complexity exponent, and retention slope.
- `src/lib/common/perf/execution_metrics_sdn.spl`: separate stable subject and volatile run/resource/decision SDN serialization.
- `src/lib/nogc_sync_mut/io/resource_scope.spl`: fixed resource classes, whole-current-process scope, delegated cgroup-v2 enforcement/observation, an explicit systemd delegated-service provider, and lower-quality RLIMIT/process-group sampling fallback.
- `src/runtime/runtime_process_owned.c`: additive direct-child `wait4` plus sampled owned-process-group CPU/RSS/I/O/PID observations without changing v2 lifecycle results.
- `src/runtime/runtime_fork.c`: additive `wait4` getters let fork-mode tests retain exact direct-child CPU and peak-memory observations.
- `TestFileResult` has backward-compatible compile/execution/resource-class/cohort/budget/anomaly fields. Interpreter, SMF, native, safe, fork, baremetal, and QEMU host processes attach observations and persist available evidence in the unified database's volatile `resource_runs` table.
- Test DB timing updates now preserve baseline fields; explicit promotion is the only mutation path, and lifecycle columns migrate legacy rows.

Still required for final verification: Windows observed Job Object receipts, macOS native receipt evidence, a provider-proven PID-limit row, and a source-matched admitted self-hosted compiler. The repository has migrated the former dual-file test database into `test_db.sdn`; `resource_runs` is a volatile table in that compatible unified database rather than a second writer racing `test_db_runs.sdn`.

## Runtime boundary decisions

### Owned subprocess observation

- `runtime_need`: Simple cannot obtain `wait4`, signal status, process-group membership, or kernel counters without an OS boundary.
- `facade_checked`: existing `process_ops` and `process_limit_enforcer` facades were inspected first; their legacy tuples collapse evidence required by REQ-002/003.
- `chosen_path`: additive versioned owned-process observation receipts behind `resource_scope.spl`; legacy APIs remain compatible.
- `rejected_shortcuts`: exit-137/139 inference, `/proc` reads in app leaves, and calling the Rust seed as the production toolchain.

### Fork-mode direct-child metrics

- `runtime_need`: the fork bridge reaps the child internally, so only that bridge can retain its `wait4` rusage.
- `facade_checked`: routing fork mode through an exec-based facade would destroy its copy-on-write purpose and change semantics.
- `chosen_path`: additive read-only getters for the most recent owned fork receipt, surfaced as `ExactDirectChild` rather than tree evidence.
- `rejected_shortcuts`: relabeling parent RSS as child RSS, inferring OOM from SIGKILL, or claiming descendant coverage from direct-child rusage.

## Error handling

Unavailable metrics use sentinel-free optional/evidence fields and downgrade quality. Scope setup failure either falls back according to policy or returns `InfrastructureFailure`; it never silently claims exact enforcement. Malformed SDN records are rejected with schema/cohort diagnostics. All cleanup is idempotent and refuses unsafe process identifiers.

## Complexity

Event append and budget checks are O(1). Median/MAD comparison sorts bounded baseline samples, O(n log n). Complexity-probe regression fits log-transformed points over a small fixed series. Storage retains all raw observations while keeping large artifacts out of SDN.
