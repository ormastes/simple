# Simple Build/Test Abnormality Detection — Feature Requirements

Status: selected by the user’s supplied feature specification on 2026-08-24.

## Requirements

- REQ-001: Builds, tests, benchmarks, bootstrap, and QEMU execution expose one `ExecutionResourceScope` contract while keeping hard enforcement, declared-budget decisions, and historical-anomaly decisions independent.
- REQ-002: Each observation records explicit `ResourceEvidenceQuality`, `TerminationCause`, exit/signal data, wall and CPU time, direct-child peak memory, tree charge when available, heap observations, I/O, and peak process count.
- REQ-003: Classification uses affirmative evidence. Exit 137/139 alone never proves timeout or OOM; SIGSEGV without a memory event is a crash, and external termination without scope evidence is unverified.
- REQ-004: Linux uses cgroup v2 for exact tree scope when available, with `wait4`, process-tree sampling, and existing RLIMIT/watchdog facilities as explicitly lower-quality fallbacks. Windows uses Job Object accounting/enforcement; macOS/Unix uses process groups, rusage, watchdogs, and sampling.
- REQ-005: Test records preserve stable test identity while volatile run records add setup/compile/execution durations, resource usage, class, cohort, budget, and anomaly decisions.
- REQ-006: Build records persist stable subjects/policies separately from volatile hierarchical run spans, phase IDs, unit IDs, work counters, resource observations, and external artifact digests.
- REQ-007: Cohorts distinguish scenario, semantic configuration, workload/aspect plan, tool/schema digests, and machine environment; incompatible scenarios or machine classes are never silently pooled.
- REQ-008: Baselines have `Provisional`, `Approved`, `Suspect`, and `Superseded` states. Only explicit promotion changes the approved baseline.
- REQ-009: Regression decisions require subject-specific absolute and relative floors plus robust MAD noise; failure additionally requires confirmation. Tail/outlier observations are retained.
- REQ-010: Stable compiler spans and work counters cover source/load, parse, HIR/type, monomorphization, MIR/optimization, AOP, backend, link, and packaging; missing required phases or collapsed work can flag suspicious improvements.
- REQ-011: Resource classes and explicit standard-quantity limits are enforced deterministically; historical policy can recommend tighter values but cannot loosen an explicit budget.
- REQ-012: Complexity probes estimate time and memory exponents over N/2N/4N/8N, and retention probes record post-cleanup heap/process-memory slope.
- REQ-013: Whole-build/test scope measurement is delivered before nested per-unit enforcement; nested enforcement must use an efficient frozen-graph worker transport and never reload the complete compiler once per source module.
- REQ-014: `simple perf record`, `compare`, `explain`, and `baseline promote` concepts share the same persisted evidence used by normal build/test policy.

## Traceability

Acceptance is defined by `.spipe/simple-build-test-abnormality-detection/state.md` AC-1 through AC-13 and the matching system-test plan/spec.
