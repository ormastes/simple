<!-- codex-research -->

# Simple Ring and Async Base — Nonfunctional Requirements

Status: Selected
Date: 2026-08-26
Source: `doc/01_research/runtime/simple_ring_first_async_first_architecture_2026-08-26.md`

## Delivery phases

Phase 2 requires the pure-Simple bounded design and executable diagnostic
fixtures for these NFRs. Quantified proof gates—80% branch coverage, admitted
native performance/RSS/allocation measurements, self-hosted verification,
generated-manual provenance, compiler/linker placement, and mission assurance
receipts—are Phase 3 qualification work in
`.spipe/simple-ring-async-base/todo.sdn`. Deferral does not convert a TODO into
evidence or weaken the final NFR target.

## NFR-SRA-001 — Bounded time

Reserve, commit, provider take, terminal completion, cancellation lookup, targeted wake selection, and ready-queue insertion shall be O(1). Batch operations shall be O(batch size), never O(total task count).

## NFR-SRA-002 — Bounded memory

Ring storage, task capacity, wake capacity, trace storage, and mission resources shall have explicit finite bounds. Server and mission steady-state paths shall allocate zero heap objects after admission/Ready.

## NFR-SRA-003 — Nonblocking execution

Ring, provider-completion, UI/I/O/firmware/mission executor, and task-poll paths shall perform zero blocking waits. Blocking compatibility work shall run only in an explicitly named compatibility pool and shall remain observable.

## NFR-SRA-004 — Determinism

Mission profiles shall have deterministic ownership, admission, overload, cancellation linearization, wake selection, and scheduling policy. No silent fallback, random work stealing, queue growth, or detached execution is permitted.

## NFR-SRA-005 — Correctness under reuse

Slot reuse, token wrap boundaries, cancellation/completion races, reset, and delayed provider completions shall preserve exactly-one terminal completion and stale-generation rejection.

## NFR-SRA-006 — Assurance evidence

Mission evidence shall include an effect report, suspension map, task topology and maximum concurrency, ring-depth proof, memory upper bound, blocking proof, priority/deadline map, cancellation map, provider/fallback report, and configuration/artifact fingerprints. Missing required evidence is blocked, not passed.

## NFR-SRA-007 — Test depth

Owned code shall reach at least 80% branch coverage. Tests shall include constructor validation, every state transition and error branch, capacity boundaries, generation reuse, duplicate terminals, cancellation/reset orderings, deterministic overload, multiple typed rings, exact wakeups, independent-task progress, and profile/fingerprint matrices.

## NFR-SRA-008 — Performance evidence

Representative benchmarks shall record before/after p50, p99, and p99.9 latency, throughput, occupancy/high-water/full events, batch size, kick count, task polls/suspensions/wake latency, and maximum RSS or bounded pool/arena high-water. Mechanical async conversion is not accepted as an improvement without comparable evidence.

## NFR-SRA-009 — Sync-leaf overhead

Proven synchronous leaves that do not suspend shall not allocate a Future, task frame, scheduler entry, or ring operation. Any compiler phase implementing implicit suspension must measure and gate sync-leaf regression separately.

## NFR-SRA-010 — Portability and mapping honesty

The common contract shall not encode Linux, POSIX, GPU, or NVMe-specific descriptors. Every provider shall state direct/translated/software/emulated mapping and fallback reason, and mission policy shall be able to require direct or bounded translated mappings.

## NFR-SRA-011 — Compatibility

Existing public async APIs shall remain usable through explicit adapters during migration. Compatibility shall not weaken backpressure, generation, cancellation, ownership, blocking, or fallback reporting.

## NFR-SRA-012 — Documentation and traceability

Every feature requirement shall map to executable unit/integration/system evidence and an operator-readable mirrored manual. Architecture, design, plan, public concurrency guide, coding skill, and feature/layer expert knowledge shall remain current with shipped capability and named blockers.
