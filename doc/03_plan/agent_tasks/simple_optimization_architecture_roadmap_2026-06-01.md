# Simple Optimization Architecture Roadmap Agent Tasks

Date: 2026-06-01

This plan continues the active `$sp_dev` roadmap in
`doc/01_research/local/simple_optimization_architecture_roadmap_2026-06-01.md`.
It records the next disjoint parallel-agent slices after the verified
checkpoint `d826cf69e0f4`.

## Current Evidence Baseline

- Roadmap state exists at
  `.spipe/simple-optimization-architecture-roadmap-2026-06-01/state.md`.
- The roadmap has lanes A-F, handoff gates, and dated progress evidence.
- The latest recorded sync checkpoint pushed `d826cf69e0f4` to GitHub `main`.
- `doc/06_spec` stray executable spec count was recorded as `0` at the last
  checkpoint.

## Lane A/F: Integration and Smoke Gates

Owner scope:
- `doc/01_research/local/simple_optimization_architecture_roadmap_2026-06-01.md`
- `.spipe/simple-optimization-architecture-roadmap-2026-06-01/state.md`
- verification command evidence only

Tasks:
1. Run the cross-lane smoke list from
   `doc/03_plan/sys_test/simple_optimization_architecture_roadmap_2026-06-01.md`
   before each coherent checkpoint.
2. Record `git status --short`, `jj status`, and tracked-file count before
   sync.
3. Fetch/rebase with jj only after verification evidence is current.
4. Do not push without the approval gate required by the release/sync rules.

Exit evidence:
- all smoke commands either pass or have named release-blocking defects;
- `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`;
- sync status is recorded in the roadmap progress log.

## Lane E: Persistent SMF Profile Split

Owner scope:
- future schema docs under `doc/05_design/`
- future tests under `test/system/app/compiler/feature/`
- future implementation under `src/compiler_rust/common/src/smf/`,
  `src/compiler/95.interp/`, and `src/app/optimize/`

Do not start implementation until the schema and migration design are reviewed.

### E1 Schema

Deliverables:
- define `.sprof` header/version fields;
- define function profile records for call count, self/total time, branch
  ratios, loop ranges, deopt count, JIT tier history, and provider choices;
- define stable symbol keys using MIR hash plus `stable_name` where available.

Acceptance:
- schema distinguishes unknown, incompatible, and exact-profile records;
- no runtime profile record can bypass safe-deoptimization facts.

### E2 Writer

Deliverables:
- identify where interpreter/JIT profile snapshots are materialized;
- write profile data as an append-safe or atomic replace operation;
- record corruption handling and version mismatch behavior.

Acceptance:
- failed writes do not corrupt existing `.smf` artifacts;
- disabled profiling adds no hot-request filesystem writes.

### E3 Loader and Merge

Deliverables:
- load `.sprof` only when profile-guided optimization is enabled;
- merge multiple runs with saturating counters and timestamp/source metadata;
- expose merged facts to hotspot planning without repeated full-tree scans.

Acceptance:
- stale or incompatible records are ignored with diagnostics;
- hot path request handling does not shell out or reread profiles.

### E4 Migration

Deliverables:
- exact MIR-hash reuse;
- rename/body-identical reuse via `stable_name`;
- similar-body reuse only as advisory evidence;
- migration report consumed by `src/app/optimize/`.

Acceptance:
- incompatible signature changes reuse `0%` of the previous profile;
- every reused record names confidence and reason.

## Lane Handoffs

- Lane E hands schema and migration decisions to Lane F for system-test design.
- Lane F rejects placeholder tests, `pass_todo`, and vacuous assertions.
- Lane A serializes any branch or sync work after Lane E/F artifacts are
  verified.
