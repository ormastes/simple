# Simple Build/Test Abnormality Detection

## Goal

Add first-class abnormality detection to Simple builds and tests for compile/test time, memory, algorithmic work, and runaway processes.

Keep three mechanisms independent:

| Mechanism | Purpose | Result |
|---|---|---|
| Hard resource limit | Protect machine/CI | Kill/cancel process tree |
| Declared budget | Enforce expected maximum | Deterministic violation |
| Historical anomaly detector | Detect introduced regressions | Warning/failure |

A baseline must never replace a hard limit, and a hard limit alone cannot detect gradual regressions.

## 1. Current State and Gaps

Simple already has explicit compiler phases, build timing, per-spec child processes, test SDN timing history, memory-aware shard admission control, and supervised-build foundations.

Main gaps:

1. Peak memory of the complete process tree is not reliably measured.
2. Virtual-address-space limits are not equivalent to actual aggregate memory.
3. Exit 137/139 alone cannot prove timeout/OOM.
4. A regression must not automatically become its own new baseline.
5. Baseline identity needs mode, target, optimization, cache state, aspects, bootstrap stage, concurrency and machine class.
6. Admission control is not per-child enforcement.
7. Build supervision must avoid reloading the whole compiler for every module.

## 2. Research Summary

| System | Technique to adopt |
|---|---|
| rustc-perf | Separate check/debug/opt and full/incremental scenarios |
| Cargo timings | Compilation units, concurrency and dependencies |
| Bazel profiler | Structured spans and critical-path analysis |
| Clang | Hierarchical traces plus compiler/assembler/linker resource stats |
| GCC | Per-pass timing/allocation |
| TypeScript | Work counters: files, nodes, types, caches, memory |
| LLVM LNT | Machine + subject + metric identity |
| Go benchstat | Repeated paired before/after comparison |
| Criterion/Google Benchmark | Distribution-based change detection |
| Bazel test sizing | Resource classes separate from timeout |
| Linux cgroup v2 | Tree-wide accounting and hard limits |
| Windows Job Objects | Process-tree accounting/enforcement |

## 3. Shared Architecture

```text
build / test / benchmark / bootstrap / qemu
                    |
                    v
          ExecutionResourceScope
       limits + process-tree metrics
                    |
                    v
             Structured spans
      phase / unit / test / external tool
                    |
                    v
           Build/Test SDN records
                    |
                    v
       budget + anomaly detector
                    |
                    v
 CI result / explanation / diagnostics
```

```simple
enum ResourceEvidenceQuality:
    ExactTree
    ExactDirectChild
    SampledTree
    ProcessOnly
    Unavailable

enum TerminationCause:
    Exited
    WallTimeout
    NoProgressTimeout
    CpuLimit
    MemoryHigh
    MemoryMax
    ProcessLimit
    OutputLimit
    Signal
    ExternalTermination
    InfrastructureFailure

struct ResourceUsage:
    wall_ms: i64
    user_cpu_ms: i64
    system_cpu_ms: i64
    peak_tree_charge_bytes: i64
    peak_direct_child_rss_bytes: i64
    heap_live_end_bytes: i64
    heap_peak_bytes: i64
    io_read_bytes: i64
    io_write_bytes: i64
    pids_peak: i64
    evidence_quality: ResourceEvidenceQuality
    termination: TerminationCause
    signal: i64
    exit_code: i64
```

Do not label every platform memory metric as RSS. Cgroup charge, child RSS, allocator-live memory and Windows job commit are different.

## 4. Platform Measurement

### Linux

Use one cgroup v2 scope per build/test, optionally nested by worker.

Measure/enforce `memory.high`, `memory.max`, `memory.peak`, `memory.events`, `cpu.stat`, `pids.max`, `pids.peak`, and `pids.events`.

Fallback:

1. `wait4()` for direct-child CPU/peak RSS.
2. `/proc` process-tree sampling.
3. Existing RLIMIT/timeout backend, marked lower-quality evidence.

Never infer OOM solely from 137 or memory exhaustion solely from 139.

### Windows

Use a Job Object for the whole build/test tree. Collect peak job memory, CPU/accounting and process counts; enforce job-wide limits.

### macOS/other Unix

Use process groups, `wait4`/rusage, watchdogs and tree sampling. Always record evidence quality.

## 5. Build Phase Instrumentation

Use stable phase IDs:

```simple
enum BuildPhaseId:
    Startup
    ConfigResolution
    SourceClosure
    LoadSources
    Parse
    SourceReclaim
    HirLower
    TypeCheck
    EffectCheck
    Monomorphize
    MirLower
    BorrowCheck
    AsyncTransform
    MirOptimize
    AopWeave
    DebugTrace
    BackendCodegen
    Assemble
    Link
    SmfPackage
    ManifestWrite
    ArtifactValidation
```

Each span stores `run_id`, `span_id`, `parent_span_id`, `phase_id`, `unit_id`, timestamps, status, work counters and resource observations.

### Phase memory

```text
memory_at_start
memory_at_end
peak_memory_during_span
transient_peak_above_start = peak - start
retained_delta = end - start
heap_live_at_start
heap_live_at_end
heap_peak_during_span
```

| Pattern | Likely cause |
|---|---|
| High transient, low retained | temporary buffers |
| Low transient, high retained | long-lived state/cache |
| High process memory, low heap-live | arenas, mmap, child tools/page cache |
| Heap-live + process memory grow | retained structures |
| Memory grows while work stays flat | leak/duplication/allocator regression |

Whole-build memory can be hard-limited immediately. Exact per-phase hard limits require isolated workers or cooperative allocator budgets.

## 6. Work Counters

| Phase | Counters |
|---|---|
| Source/load | files, bytes, dependency edges, cache hits/misses, duplicates |
| Parse | bytes, tokens, AST nodes, errors, modules |
| HIR/type | modules, functions, types, symbols, query hits/misses, candidates |
| Monomorphize | requests, unique/reused instances, max per generic |
| MIR | functions, blocks, instructions, temporaries |
| Optimization | passes, input/output instructions, changed functions |
| AOP | aspects, candidate/matched join points, advice applications, generated nodes |
| Backend | emitted functions, IR/object bytes, external tools |
| Link/package | objects, input/output/serialization bytes |

This detects cases such as parser slowdown with unchanged token count, HIR explosion, monomorphization explosion, quadratic AOP matching, cache invalidation regressions, and suspiciously skipped compiler phases.

## 7. Build Scenario Cohorts

Maintain independent baselines for:

- `full_cold`
- `full_warm_fs`
- `full_warm_cache`
- `incremental_patched`
- `incremental_unchanged`
- `check`
- `debug`
- `opt`
- `bootstrap_stage2`
- `bootstrap_stage3_flat`
- `bootstrap_stage4_full`

Never compare fundamentally different scenarios.

## 8. Configuration and Aspect Identity

Hash the effective build:

```text
configuration_id = hash(
    compiler/runtime/schema digests,
    host/output target,
    backend + compile mode + optimization,
    debug/GC/memory/low-memory mode,
    bootstrap stage + skipped-pass mask,
    cache scenario,
    concurrency/shards,
    effective semantic/module configuration,
    ordered aspect weave plan,
    aspect implementation digests,
    workload digest
)
```

Keep `semantic_configuration_id` separate from `machine_environment_id`.

Machine identity includes CPU model, allocated cores, memory quota, OS/kernel, runner/container class and relevant frequency policy.

Normal aspect regression:

```text
base revision + aspect set A
candidate revision + aspect set A
```

Marginal aspect overhead:

```text
same revision/config + aspect OFF
same revision/config + aspect ON
```

Store join-point candidates/matches, advice calls, weave time/CPU, memory, generated HIR/MIR and artifact-size delta.

## 9. Test Design

Keep per-spec process isolation and extend results:

```simple
struct TestFileResult:
    ...
    setup_ms: i64
    compile_ms: i64
    execution_ms: i64
    resource_usage: ResourceUsage
    resource_class: text
    cohort_id: Digest
    budget_status: BudgetStatus
    anomaly_status: AnomalyStatus
```

Use standard quantities such as:

```text
--max-memory=128MiB
--memory-high=768MiB
--max-wall=5s
--max-cpu=3s
--no-progress=2s
```

Initial SDN resource classes can define `unit`, `integration`, `system`, `qemu`, `gpu`, and `bootstrap` limits. Historical data may suggest tighter limits but must never silently loosen explicit budgets.

## 10. Correct Failure Classification

| Evidence | Classification |
|---|---|
| cgroup memory max/OOM event | proven `MemoryBudgetExceeded` |
| cgroup PID event | proven `ProcessBudgetExceeded` |
| internal watchdog | proven `WallBudgetExceeded` |
| SIGSEGV without memory event | `Crashed(SIGSEGV)` |
| external SIGTERM without scope evidence | `UnverifiedExternalTermination` |
| measurement unavailable | verdict + `ResourceEvidenceUnavailable` |

## 11. SDN Storage

Keep current test DB compatibility:

```text
test_db.sdn          stable test identity
test_db_runs.sdn     volatile test observations/resources
build_db.sdn         stable build subjects/policies
build_db_runs.sdn    volatile build observations
```

Share:

```text
std.execution_metrics
    cohort
    run
    span
    resource_usage
    baseline
    budget
    anomaly
```

Baseline states:

```simple
enum BaselineState:
    Provisional
    Approved
    Suspect
    Superseded
```

Approved baselines do not automatically move when a regression occurs. Large traces, heap snapshots, perf data, flamegraphs and memory time series should be external compressed artifacts/CAS entries referenced by digest.

## 12. Anomaly Algorithm

Comparison order:

1. Exact semantic configuration/scenario.
2. Same machine class.
3. Prefer paired base/candidate runs on the same runner.
4. Reject/downgrade heavily contended evidence.
5. Verify required spans/work counters.
6. New cohorts enforce hard limits but use a provisional baseline.

Recommended PR execution:

```text
A1 = merge-base
B1 = candidate
B2 = candidate
A2 = merge-base
```

Regression rule:

```text
delta = candidate_median - approved_median

abnormal if all true:
    delta > absolute_floor
    delta / approved_median > relative_floor
    delta > robust_noise_multiplier * baseline_MAD
```

Initial policy:

- warning: >=10% and >=3 MAD
- failure: >=15% and >=4 MAD, confirmed by another paired run
- also require a subject-specific absolute floor

Never delete outliers. Track p95/p99, maximum, outlier frequency, hard-limit proximity, `memory.high` events and no-progress incidents.

Use EWMA/CUSUM or consecutive-shift rules to catch gradual mainline drift.

Large speedups should be flagged when required phases disappear or work counters unexpectedly collapse.

## 13. Inefficiency Detection

| Abnormality | Inspect | Likely defect |
|---|---|---|
| Parse time/source byte rises | tokens/nodes/duplicates | parser/repeated parse |
| Parse work rises with workers | per-worker modules | each shard processing full closure |
| HIR time rises, nodes flat | queries/candidates | lookup/data-structure regression |
| HIR nodes explode | generated transforms | lowering duplication |
| Monomorphizations explode | unique/reused instances | specialization/dedup bug |
| AOP becomes superlinear | candidates/matches/aspects | repeated pointcut scans |
| Incremental approaches full | cache hits/invalidation | over-broad invalidation |
| Process memory rises, heap-live flat | mmap/PSS/allocator | arena/mapping retention |
| Heap-live rises phase-to-phase | owner/type retention | leak/unbounded cache |
| Wall rises, CPU flat | I/O/locks/waits | contention/deadlock/tool wait |
| CPU rises, wall flat | total work/critical path | hidden parallel-work regression |
| Output size rises, source flat | MIR/debug/symbols | code/metadata duplication |

### Complexity probes

Generate workloads at `N, 2N, 4N, 8N` and estimate:

```text
time ~= C * N^p
memory ~= D * N^q
```

Flag paths that move from near-linear toward quadratic before they reach a timeout. Apply to parsing, type candidates, generic specialization, imports and AOP matching.

### Retention probes

Repeatedly execute a persistent compiler/session workload, perform supported cleanup/GC, record live heap and process memory, and fit the post-cleanup memory slope. This separates true retained objects from allocator/mapping growth.

## 14. CI Plan

### Every PR

Run affected lanes plus sentinels:

```text
full_cold
incremental_unchanged
incremental_patched
changed tests with hard limits
no-aspect compiler sentinel
default-aspect compiler sentinel
changed-aspect interaction group
```

Compiler/parser/HIR/MIR/AOP/cache/runtime changes trigger a broader corpus.

### Nightly

Run full compiler corpus, all incremental scenarios, check/debug/opt, bootstrap stages separately, no/default/all aspects, normal/low-memory, retention probes, complexity probes, major targets/backends and QEMU/system/GPU suites.

On a confirmed anomaly retain structured trace, memory time series, heap snapshots, top regressed units, changed work counters, cache invalidation report, aspect-plan diff, artifact-size comparison and optional profiler data.

## 15. Implementation Waves

### Wave 0 — trustworthy measurement

1. Runtime observed-process API using `wait4` or equivalent.
2. Linux cgroup v2 scope.
3. Windows Job Object scope.
4. New sibling process API to avoid breaking every existing tuple caller.
5. Exact signal/exit/CPU/direct-child RSS/tree memory events/evidence quality.
6. Remove false 137/139 classifications.
7. Grandchild/process-tree tests.

Likely areas:

```text
src/runtime/*
src/compiler_rust/runtime/*
src/lib/nogc_sync_mut/io/process_ops.spl
src/lib/nogc_sync_mut/io/process_limit_enforcer.spl
new: src/lib/nogc_sync_mut/io/resource_scope.spl
```

### Wave 1 — persist evidence

Extend test runner/test DB and add build DB. Add a whole-build resource scope immediately so compiler shards, linker and descendants are measured before per-unit supervision is complete.

### Wave 2 — spans, cohorts and counters

Add stable phase IDs, span IDs, configuration/aspect/workload identities, work counters, phase heap metrics and build critical-path calculation.

### Wave 3 — anomaly detector and CI gate

Add commands/concepts equivalent to:

```text
simple perf record
simple perf compare
simple perf explain
simple perf baseline promote
```

Normal build/test commands should record/gate according to policy without requiring a separate profiler.

### Wave 4 — per-unit supervised build

Complete supervised build only after a practical worker transport exists:

- fork after frontend/frozen graph preparation, or
- serialize a compact module capsule.

Then use nested resource scopes for parse/HIR/codegen units.

Do **not** supervise by rerunning a complete compiler invocation once per source module.

## 16. Parallel Agent Plan

| Agent | Work |
|---|---|
| A — Runtime | observed-process API, wait4/rusage, signals |
| B — Linux | cgroup v2 scope/accounting/enforcement |
| C — Windows/macOS | Job Objects and fallback backend |
| D — Test runner | per-spec resource evidence and limits |
| E — SDN | build/test run schema, cohorts, baselines |
| F — Compiler | structured phase spans + work counters |
| G — Statistics | MAD/paired comparison/EWMA/CUSUM |
| H — AOP/cache | aspect counters, cache/invalidation evidence |
| I — CI | PR/nightly policy, diagnostics and bisection |
| J — Verification | sspec/system tests for classification and regressions |

Dependencies:

```text
A -> B/C -> D
A -> F
E -> G
F + E -> G
D + G -> I
F + G -> I
all -> J
```

## 17. Required Acceptance Tests

- Direct child allocates known memory -> nonzero memory evidence.
- Grandchild allocation -> whole scope includes descendants.
- Real SIGSEGV -> crash, not memory violation.
- `memory.max` exceeded -> proven memory-budget violation.
- External SIGTERM -> unverified external termination.
- Interpreter/native -> separate cohorts.
- Different aspect plans -> separate cohorts.
- Candidate +25% delay -> detected without changing approved baseline.
- Required phase removed -> suspicious improvement/incomplete evidence.
- Rare huge memory spike -> retained as outlier/tail evidence.
- Incremental edit -> cache work and invalidation reason recorded.
- N/2N/4N/8N fixture becomes quadratic -> complexity regression detected.

## Final Recommendation

Implement in this order:

1. **Trustworthy process-tree measurement and termination classification.**
2. **Structured compiler phase spans.**
3. **Configuration/aspect/cache/machine cohort identity.**
4. **Build SDN parallel to test SDN.**
5. **Frozen approved baselines with explicit promotion.**
6. **Work-normalized metrics and complexity/retention probes.**
7. **Paired base/candidate CI measurements.**
8. **Per-unit supervised build after worker transport is efficient.**

This architecture detects both catastrophic failures—timeouts, OOMs and runaway children—and subtle regressions such as duplicate parsing, monomorphization explosion, excessive cache invalidation, AOP matching growth, retained compiler state, allocator growth, hidden parallel work and accidentally skipped compiler phases.

## 18. Repository Validation (2026-08-24)

The proposal was checked against the current Simple tree. The findings sharpen the implementation boundary:

- `src/lib/nogc_sync_mut/io/process_limit_enforcer.spl` currently classifies exit 137 as `timeout_hard` and exit 139 as `memory`; both are unsupported inferences and must be replaced by affirmative scope/watchdog/signal evidence.
- `src/lib/nogc_sync_mut/process_limits.spl` already owns named test resource profiles and converts memory to bytes, but the Unix enforcement path lowers memory to `ulimit -v`; that is virtual address space, not aggregate resident/charged memory.
- Four memory-model copies of process/test-runner facilities exist. Shared value types and pure decision logic belong under `src/lib/common/perf/`; mutable execution ownership remains behind the canonical process facade rather than being copied into every caller.
- Existing test timing history and MAD-oriented research can be reused, but it does not provide cohort-safe approved baselines, paired comparisons, frozen promotion, tree resource evidence, or missing-span/work-counter validation.
- Existing bug records `supervised_builder_unwired_and_no_peak_rss_2026-08-17.md` and `test_runner_peak_rss_needs_child_rusage_extern_2026-08-17.md` already identify missing direct-child `wait4` evidence. TODO 573 separately retains Unix process-tree cleanup/provider-parity work.
- Windows runtime code already contains Job Object cleanup according to the retained TODO triage; the new work should extend that owner with accounting/limit evidence rather than introduce an app-local Windows implementation.
- Test DB V3 already separates `test_db.sdn` stable identities from `test_db_runs.sdn` observations and retains percentiles/outliers. However, `RunnerTestDbCore.update_timing` currently auto-ratchets its baseline after a median shift above 10%; this must be migrated to explicit baseline promotion rather than reused as-is.
- `test_runner_resources.spl` and `resource_tracker.spl` sample one direct process and are not wired as trustworthy tree enforcement. They may supply migration/UI concepts but cannot back an exact scope verdict.
- Compiler `driver_log_helpers.spl` and `hir_phase_profile.spl` contain useful phase timing, heap boundaries, and HIR work counters. The adapter should type these existing events instead of building on the unused `BuildLogger` alone.
- Current Unix timeout paths already establish process groups and test descendant cleanup. The owned-process C lifecycle provides tokenized start/poll/cancel/collect and is the correct extension point for rusage/tree evidence.
- The current Linux host has cgroup v2 mounted but not directly writable. Exact-tree integration should use an admitted transient delegated scope (for example the existing `systemd-run --user --scope` facility) and otherwise report fallback quality; it must not silently run uncapped.

### Owner-boundary decision

`runtime_need`: obtain direct-child `wait4`/rusage and platform scope observations that pure Simple cannot synthesize.

`facade_checked`: `std.process_limits`, `app.io.process_limit_enforcer`, the shared process facade, test-runner timing history, and common statistics helpers.

`chosen_path`: add shared pure-Simple evidence/cohort/budget/anomaly value logic first, then add the smallest observed-process/resource-scope capability at the existing process/runtime owner boundary.

`rejected_shortcuts`: new app-local `rt_*` aliases, interpreting 137/139 as proof, treating `ulimit -v` as tree RSS, per-module full compiler reinvocation, auto-promoting candidate observations, and silently relaxing declared budgets from history.
