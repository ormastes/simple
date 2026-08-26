<!-- codex-research -->

# Simple Ring and Async Base — Feature Requirements

Status: Selected
Date: 2026-08-26
Source: `doc/01_research/runtime/simple_ring_first_async_first_architecture_2026-08-26.md`
SPipe lane: `.spipe/simple-ring-async-base/state.md`

## Decision

Simple has one typed asynchronous data-plane contract and one stackless task ABI. Native operating-system and device queues remain providers below that contract; executors and memory policies vary by profile without changing task semantics.

## Delivery phases

- **Phase 2 — pure-Simple foundation:** REQ-SRA-001 through REQ-SRA-012 and
  REQ-SRA-015 through REQ-SRA-018 are delivered as source contracts,
  implementations, adapters, documentation, and focused diagnostic tests.
  `mission_alloc`/`mission_pool` policy and bounded hosted/scalar mechanisms are
  included, but qualification is not implied.
- **Phase 3 — test and qualification:** the static-placement proofs in
  REQ-SRA-013/014, admitted self-host execution, coverage, generated manuals,
  performance/resource receipts, compiler lowering, and native-provider gates
  are tracked in `.spipe/simple-ring-async-base/todo.sdn`.

Phase 2 completion is not a release or mission-qualification PASS. Phase 3 TODO
rows are visible debt and may only become PASS with their named evidence.

## Requirements

### REQ-SRA-001 — Typed bounded ring

The base shall expose `SimpleRing<Op, Cpl>` with separate typed submission and completion values. Capacity is fixed at construction, admission is explicit, and a full ring returns a typed outcome without blocking, growing, overwriting, or silently submitting early.

### REQ-SRA-002 — Stable operation identity

Every admitted operation shall receive a `RingToken` containing a slot and `RingGeneration`. Reset increments the generation. Completion, cancellation, and lookup shall reject tokens from another ring, slot lifecycle, or generation.

### REQ-SRA-003 — Reserve and commit transaction

Admission shall separate reservation from commitment. An uncommitted reservation may be released without becoming provider-visible. Batch reserve/commit shall be all-or-explicitly-partial according to the requested policy and shall never hide partial admission.

### REQ-SRA-004 — Terminal completion contract

Each admitted single-shot operation shall produce exactly one terminal `RingCompletion`: success, failure, or cancelled. Duplicate and conflicting terminal attempts shall be rejected. Multi-shot behavior is outside V1 unless explicitly represented by a later operation type.

### REQ-SRA-005 — Cancellation and reset

Cancellation shall report whether work was cancelled before commit, requested from a provider, already terminal, or unknown/stale. Reset shall invalidate outstanding tokens, preserve a reset receipt, and prevent stale provider completions from waking or completing a reused slot.

### REQ-SRA-006 — Ownership and registered payloads

The ring shall record one mutable owner and explicit payload/buffer ownership transitions. Operations reference registered or caller-owned payloads; the ring contract shall not copy, allocate, or infer ownership on a hot path.

### REQ-SRA-007 — Exact wakeup

Each committed operation shall carry a task/waker key. A terminal completion shall identify the exact task to enqueue and shall not require scanning every Future or task.

### REQ-SRA-008 — Task ABI

The async base shall expose `AsyncTaskFrame`, `TaskContext`, and `TaskPollResult`, with polling equivalent to `poll(frame, context) -> Ready(result) | Pending(wait_token)`. Polling shall be nonblocking. Live-across-suspension state belongs in typed frames rather than generic byte arrays in the canonical path.

### REQ-SRA-009 — Structured task metadata

Task frames shall carry stable task, parent, cancellation, priority, deadline, wait-token, trace, and profile identities. Parent-owned lifetime and cancellation are the default. Detached work requires an explicit supervisor/service policy and is forbidden by mission profiles.

### REQ-SRA-010 — Provider mapping

Providers shall declare `RingMappingGrade` as `direct`, `translated`, `software`, or `emulated`, plus boundedness and fallback facts. A profile may reject a provider grade. Fallback is an explicit admission result and telemetry event, never silent.

### REQ-SRA-011 — Reference provider

V1 shall include a bounded pure-Simple software provider that exercises reserve, commit, provider take, completion, cancellation, reset, and exact wake behavior without introducing a second scheduler or Future ABI.

### REQ-SRA-012 — Profiles

`AsyncProfile` shall define the canonical presets `common`, `script`, `server`, `mission_alloc`, and `mission_pool`. Each preset selects async surface and policy, scheduler, memory, ring mapping, assurance, instrumentation, placement, capacities, blocking, allocation, detachment, fallback, work-stealing, and determinism rules.

### REQ-SRA-013 — Mission allocation profile

`mission_alloc` shall permit only pre-admitted sealed arenas/slabs with fixed capacity. It shall forbid unrestricted heap use after admission and allocation in ISR, completion hot paths, or durable publication paths. Capacity for tasks, operations, buffers, traces, and deadlines is reserved before mutation.

### REQ-SRA-014 — Mission pool profile

`mission_pool` shall use fixed/static pools for tasks, descriptors, buffers, timers, joins/cancellation, and traces; shall require compiler-known frame bounds; and shall forbid heap use after Ready, work stealing, detached tasks, unbounded polling, and multi-owner mutable queues.

### REQ-SRA-015 — Profile fingerprint

Every profile shall produce a stable fingerprint covering the task ABI, SimpleRing version, effect/memory/scheduler policies, provider requirements, resource bounds, instrumentation, placement, and configuration identity. Semantically relevant changes shall change the fingerprint.

### REQ-SRA-016 — Compatibility and migration

Existing Future, host runtime, OS notification, packet, render, and device queue surfaces may adapt to the new base incrementally. Adapters shall preserve explicit blocking/fallback facts and shall not define a competing canonical task or ring contract.

### REQ-SRA-017 — Observability

The base shall expose ring occupancy, high-water, full events, reservations, commits, cancellations, stale/duplicate rejects, batches, provider kicks, and completion latency, plus task poll, suspension, wake, resume, completion, and cancellation events using bounded trace storage selected by profile.

### REQ-SRA-018 — Effect and lowering extension points

The design shall reserve compiler-facing effects for `suspend`, `io`, `block`, allocation domains/pools, spawn, detach, unsafe, panic, nondeterminism, clock, and device access. The V1 library base shall not claim implicit-await or fixed MIR-frame compiler lowering until executable compiler evidence exists.

## Explicit later phases

Native io_uring, OS/device ABI providers, compiler implicit suspension, full executor replacement, SimpleOS/SOSIX migration, NVMe firmware migration, server/DB migration, and RenderRing migration consume this base but are not falsely declared complete by V1.
