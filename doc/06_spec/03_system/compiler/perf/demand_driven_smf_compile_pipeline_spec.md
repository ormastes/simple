# Demand-Driven SMF Compile Pipeline

**Evidence class:** expected-red production system contract
**Executable source:** `test/03_system/compiler/perf/demand_driven_smf_compile_pipeline_spec.spl`

## Manual flow

1. Freeze the active source revision through SCV and admit its package index.
2. Exercise canonical sectioned SMF archives and all package/file command forms.
3. Prove warm requests use no recursive scan and no unrequested source body.
4. Request metadata, bodies, HIR, MIR, and native facts independently.
5. Inject unresolved proxies and require deterministic rejection before MIR.
6. Exercise shared scheduling, SCC ordering, cancellation, budgets, CAS authority, and daemon loss.
7. Compare development backends and asynchronous promotion without foreground interference.
8. Compare mapped and buffered file views, including unsupported mapping and every policy.
9. Admit each implementation phase independently.
10. Inject every cutover stop condition and require `cutover_allowed=false`.

## Requirement map

- `DDSM-REQ-001..004`: archive structure, package resolution, warm no-scan behavior, bounded import discovery.
- `DDSM-REQ-005..007`: lazy proxies, MIR closure, and minimum HIR demand.
- `DDSM-REQ-008..010`: shared scheduler, persisted action graph, and host-shared CAS authority.
- `DDSM-REQ-011..016`: development backend, precompiled roots, generic shapes, async I/O, parser admission, and background isolation.
- `DDSM-REQ-017..020`: compatibility and portable file-view policy.
- `DDSM-PLAN-P0..P9`: all ten implementation-phase admissions.
- `DDSM-STOP-001..005`: all five mandatory cutover blockers.

## Current status

The production wrapper and static umbrella mapping gate exist. Static structure may pass independently, but every scenario remains expected red until `scripts/check/check-demand-driven-smf-compile-pipeline.shs` admits a production-derived, snapshot/compiler/fixture/producer-bound receipt. Existing package-index tests are supporting evidence only and cannot satisfy this runtime umbrella contract.
