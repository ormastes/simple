<!-- codex-design -->
# Simple Ring and Async Base — Agent Task Plan

## Shared contract and review gate

Frozen public names are `SimpleRing<Op, Cpl>`, `RingToken`, `RingGeneration`,
`RingAdmission`, `RingCompletion`, `RingMappingGrade`, `AsyncTaskFrame`,
`TaskPollResult`, `TaskContext`, and `AsyncProfile`. Frozen manual steps are
`Configure the async execution profile`, `Reserve and commit bounded ring work`,
`Complete work and wake the exact task`, `Reject stale, duplicate, and
over-capacity activity`, and `Prove mission bounds and deterministic policy`.
Frozen helpers are `setup_simple_ring_profile_fixture` and
`check_simple_ring_invariants`. Temporary bodies fail with `assert(false)` or
`fail(...)`; no placeholder pass is mergeable.

Merge owner: `/root`.

Final reviewer: `/root` (highest-capability Codex). Only the final reviewer may
accept broad exclusions, execution/performance/formal claims, generated-manual
quality, or done marks.

## Completed audit sidecars

The `.spipe/simple-ring-async-base/state.md` cooperative-review record freezes
these completed audit lanes for handoff:

| Audit | Completion record and handoff |
|---|---|
| Compiler/async lowering | Audited as an extension-point lane; V1 must not claim implicit-await/HIR/MIR implementation. |
| Runtime/ring/provider | Audited typed ring, generation, ownership, cancellation/reset, software-provider lifecycle, and no second scheduler ABI. |
| Profiles/mission policy | Audited five profile names, bounded allocation/pool rules, fallback grades, fingerprints, and deterministic policy. |
| Tests/SPipe/manual | Audited frozen steps/helpers, U/I/C/S/P split, mirrored manual path, fail-fast placeholders, and 80% branch target. |
| Architecture/docs migration | Audited MDSOC/provider boundaries, explicit downstream exclusions, owner/reviewer process, and artifact traceability. |

These are design/audit records, not execution receipts. `/root` must attach
the actual test, coverage, perf, and manual-generation receipts before PASS.

## Disjoint implementation lanes

No lane may edit another lane's files concurrently. Shared public names and
error semantics are frozen above; changes require `/root` review before edits.

| Lane | Owner | Exclusive files/directories | Deliverable |
|---|---|---|---|
| Common ring/task contracts | contract owner | `src/lib/common/contracts/execution/simple_ring_async_v1.spl`, matching common unit spec | token/admission/completion/task ABI values and validation |
| Profiles/mission policy | profile owner | `src/lib/common/contracts/execution/async_profile_v1.spl`, matching common unit spec | five profiles, validation, mission bounds, fingerprints |
| Hosted ring state | ring owner | `src/lib/nogc_async_mut/async_ring/simple_ring.spl`, ring-focused unit spec | fixed O(1) index queues, reserve/commit/complete/cancel/reset, telemetry |
| Software provider/adapters | provider owner | `src/lib/nogc_async_mut/async_ring/software_provider.spl`, integration provider spec | bounded pure-Simple provider and explicit mapping/fallback |
| Concurrency evidence | concurrency owner | `test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl`, concurrency fixtures only | owner transfer, ABA/reset, cancellation races, fairness, independent progress |
| Performance evidence | performance owner | `test/05_perf/runtime/simple_ring_async_base_perf_spec.spl`, retained receipts only | O(1), allocation/blocking, latency, throughput, high-water/RSS evidence |
| System/SPipe/manual | SPipe owner | `test/03_system/runtime/simple_ring_async_base_spec.spl`, generated mirror only | five-step modern SSpec and `doc/06_spec/03_system/runtime/simple_ring_async_base_spec.md` |
| Documentation/traceability | docs owner | feature docs other than this task-plan and system-test plan | architecture/detail/design/guide updates and requirement links |
| Hosted mission admission | mission adapter owner | `src/lib/nogc_async_mut/async_ring/mission_adapter.spl`, matching unit spec | bounded resource admission with explicit false static/allocation proof flags |
| Trace-ring evidence | trace owner | `src/lib/nogc_async_mut_noalloc/async/async_trace_ring.spl`, matching unit spec | fixed-capacity owner-bound tracing and overflow telemetry |
| Mission ready evidence | mission ready owner | `src/lib/nogc_async_mut_noalloc/async/mission_ready_set.spl`, matching unit spec | scalar bounded exact-wakeup mechanism with explicit placement-proof limits |
| Bounded model evidence | model owner | `test/00_formal_verification/runtime/simple_ring_async_base_bounded_model_spec.spl`, `doc/09_report/evidence/simple_ring_async_base_concurrency_linearization_2026-08-26.md` | exhaustive finite traces and source linearization/resource map; no universal proof claim |

The two plan files are owned by `/root`; no sidecar may edit them concurrently.
Generated `doc/06_spec` output is owned by the system/SPipe lane and must never
contain executable `.spl` files.

## Integration and handoff sequence

1. `/root` confirms interfaces and rejects any competing Future/scheduler ABI.
2. Ring, task, provider, and profile lanes land disjoint implementation and
   unit/integration evidence.
3. Concurrency and performance lanes run against that immutable contract and
   retain receipts; no single race or benchmark is promoted to formal proof.
4. SPipe lane writes the frozen five-step system scenario, runs docgen, and
   reviews the mirrored manual for visible steps, folded helpers, scope,
   provenance, scorecard, and limitations.
5. `/root` runs the exact commands in
   `doc/03_plan/sys_test/simple_ring_async_base.md`, checks every REQ/NFR row,
   confirms 80%+ branch coverage, direct-env guards, `0` executable specs under
   `doc/06_spec`, and then records PASS/FAIL/BLOCKED honestly.

Follow-on native providers, compiler lowering, OS/device migrations, and release
work are explicitly outside these lanes and must not be marked complete here.

## Current evidence status

Focused bootstrap-seed diagnostics are green for contracts, profiles, ring,
provider integration, concurrency, hosted mission admission, trace storage, and
the five-step system scenario. They are diagnostic only. The performance spec
exists but has no admitted baseline receipt; the manual is authored rather than
docgen-proven; branch coverage, RSS/allocation evidence, formal concurrency
proof, true static mission placement, and final pure-Simple verification remain
open under `doc/08_tracking/bug/simple_ring_async_base_open_evidence_2026-08-26.md`.

Per the user-approved phase boundary, this is sufficient for Phase 2 source
delivery. Qualification execution is owned by the Phase 3 ledger at
`.spipe/simple-ring-async-base/todo.sdn`; no deferred row is considered PASS.
