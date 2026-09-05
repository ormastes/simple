# Architecture: Simple Build/Test Abnormality Detection

## Decision

Adopt a four-layer pipeline with one-way dependencies:

1. Platform resource providers create and observe a process-tree scope.
2. `std.execution_metrics` owns portable value records and pure decisions.
3. Build/test adapters emit spans, counters, identities, and compatible SDN runs.
4. Policy compares declared budgets and explicitly approved historical baselines, then explains the independent verdicts.

Callers may depend on the next lower layer; platform providers never depend on test/build policy.

## Capsules

- `ResourceScopeProvider`: spawn/attach, enforce, observe, terminate, and close. Linux cgroup v2, Windows Job Object, and Unix fallback implementations are private provider details.
- `ExecutionEvidence`: `ResourceUsage`, evidence quality, termination evidence, spans, counters, and external artifact references. It contains no live handles.
- `ExecutionIdentity`: canonical semantic configuration, scenario/workload, aspect plan, and machine environment identities.
- `ExecutionPolicy`: explicit budgets, baseline state/promotion, robust anomaly comparison, gradual-drift state, and explanation.
- `BuildMetricsAdapter` and `TestMetricsAdapter`: translate owner-specific phases/results into shared records without duplicating policy. `test_runner_metrics.spl` is the single test-side owner for class and cohort derivation across core, fork, and composite executors.

## Invariants

- Drawn boundaries preserve the three independent outcomes: enforcement termination, budget decision, anomaly decision.
- Unlike memory quantities retain distinct field names and units.
- Exact-tree claims require provider evidence; fallbacks never upgrade themselves.
- Stable subject databases never absorb volatile samples.
- Approved baseline mutation is a separate explicit transaction.
- Missing required spans/counters invalidates or downgrades comparison; it cannot look like a speedup.
- Scope closure terminates descendants safely and rejects non-positive PIDs.

## Data Flow

```text
build/test owner -> ResourceScopeProvider -> ExecutionEvidence
       |                                      |
       +---- spans/counters/identity ---------+
                                              v
                                     append run SDN
                                              |
                         budget policy -------+------- approved baseline
                                              v
                                  independent decisions + explanation
```

## Rollout

Waves 0–3 are implemented for host-independent code and the Linux current-host provider: trustworthy receipts, stable/volatile persistence, spans/cohorts/counters, explicit baseline promotion, CLI comparison, and build/test scope integration. The Linux systemd rung is explicit because the current user cgroup lacks direct controller delegation. Wave 4 nested compiler-unit enforcement remains intentionally excluded until frozen-graph worker transport exists; Windows Job and macOS pidfd-free observed receipts remain native qualification rows rather than inferred parity.

## Rejected Alternatives

- Exit-code heuristics: ambiguous and already produce false classifications.
- RLIMIT_AS as “RSS”: wrong quantity and not aggregate tree accounting.
- One mutable rolling baseline: converts regressions into normal behavior.
- Per-caller platform code: duplicates sensitive kill/wait logic and breaks ownership.
- Per-module compiler process: reload cost defeats supervision.
