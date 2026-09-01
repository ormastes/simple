<!-- codex-design -->
# Simple Ring and Async Base Architecture

## Status

Proposed V1 architecture. This document freezes ownership and migration
boundaries for the selected base contract; it does not claim that the runtime,
compiler lowering, or native providers are implemented. The executable
reference in this lane is a bounded pure-Simple provider.

## Context and decision

Simple currently has several Future, scheduler, host-I/O, notification, and
device-queue surfaces. That fragmentation makes backpressure, cancellation,
ownership, and wakeup semantics depend on the caller. The selected direction
is one typed asynchronous data-plane contract and one stackless task ABI:

```text
Simple source
  -> effect/frame metadata and (later) compiler lowering
  -> AsyncTaskFrame + poll(frame, context)
  -> profile-specific executor
  -> SimpleRing<Op, Cpl>
  -> software, OS, or device provider
```

The stable value contracts live in
`src/lib/common/contracts/execution`. A bounded hosted ring and software
reference provider live in the virtual capsule rooted at
`src/lib/nogc_async_mut/async_ring`. Mission/static adapters live in
`src/lib/nogc_async_mut_noalloc/async`. The compiler owns effect checking and
frame/lowering metadata only. OS and SOSIX code is a provider or policy
adapter; it does not define another task or ring ABI.

This is an MDSOC virtual capsule: the contract is shared upward, while each
profile weaves exactly one provider, executor policy, storage policy, and
instrumentation policy into a composition. A composition may vary placement
and implementation, but it must preserve the same task and ring semantics.

## Architectural invariants

1. `SimpleRing<Op, Cpl>` is the only V1 asynchronous data-plane contract.
   Storage, network, render, device, event, and compute rings are typed
   instantiations, not competing descriptor ABIs.
2. `poll(frame, context) -> Ready(result) | Pending(wait_token)` is the only
   V1 task polling contract. Existing Future/executor surfaces adapt to it;
   they do not become a second canonical task model.
3. Common contracts are value-semantic and platform-neutral. They contain no
   Linux, POSIX, GPU, NVMe, SOSIX, compiler, allocator, or scheduler-private
   descriptors.
4. Admission is explicit and bounded. A full ring returns a typed outcome;
   it never blocks, grows, overwrites, or silently submits early.
5. Every admitted single-shot operation has exactly one terminal completion.
   Duplicate, conflicting, stale, and cross-ring terminal attempts are
   rejected and observable.
6. A slot is identified by a ring identity, slot, and generation. Reset
   invalidates all old tokens before a slot can be reused.
7. One mutable owner is recorded for each ring/shard and each payload. Cross
   owner movement is an explicit transfer, not an inferred shared mutation.
8. A committed operation carries an exact task/waker key. Completion selects
   that task directly; no executor scans every Future or task.
9. Poll, ring operations, provider completion, and executor paths are
   nonblocking. Blocking compatibility work is named, isolated, and reported.
10. Fallback is an explicit admission result and telemetry event. A provider
    cannot silently degrade a mission or direct-required profile.
11. Synchronous leaves that are proven not to suspend remain direct. They do
    not create a frame, scheduler entry, Future, or ring operation.
12. V1 reserves compiler effect and frame extension points but does not claim
    implicit-await or fixed MIR frame lowering without compiler evidence.

## MDSOC capsule and ownership

### Virtual capsule

The capsule has five cooperating projections over one contract surface:

```text
common execution contracts
  |\
  | +-- hosted bounded ring + software provider
  | +-- mission allocation/static-pool adapters
  | +-- compiler effect/frame projection
  | +-- OS/SOSIX/device provider projections
  |
  +--> profile composition + executor policy + bounded instrumentation
```

The common projection is the only public next-layer surface. A provider may
implement the provider side of the contract, and an executor may consume
completion/wake values, but neither may reach into another provider's private
slots, frame layout, or queue metadata. Feature transforms for tracing,
assurance, and profile fingerprinting wrap these boundaries without changing
operation semantics.

### Layer map

| Layer/owner | Owns | May consume | Must not own |
|---|---|---|---|
| `src/lib/common/contracts/execution` | Stable value contracts, versions, enums, receipts, validation vocabulary | Dependency-light common value types | Runtime storage, OS descriptors, compiler lowering, scheduler code |
| `src/lib/nogc_async_mut/async_ring` | Hosted bounded slots, reserve/commit state, software provider, reference telemetry, bounded-preallocated mission admission | Common contracts and hosted storage primitives | Link-time-static/no-allocation claims, a Future ABI, a second scheduler, implicit compiler semantics |
| `src/lib/nogc_async_mut_noalloc/async` | Bounded trace-ring storage now; future true-static mission storage/executor adapters | Common contracts and no-allocation primitives | Importing the hosted ring, heap-growing fallback, work stealing, contract redefinition |
| `src/lib/nogc_async_mut/async` and `async_host` | Compatibility adapters for existing async APIs during migration | Canonical task/ring contracts | New terminal, wake, cancellation, or ownership semantics |
| `src/compiler/00.common`, `20.hir`, `50.mir` | Effect vocabulary, suspension eligibility, frame shape metadata, lowering extension points | Common contract metadata | Ring queues, provider calls, task scheduling, runtime ownership |
| `src/os/async` | OS-facing provider adapters and completion ingress | Common contracts, OS capability/policy surfaces | Platform-specific types in common; a new scheduler ABI |
| `src/os/sosix` | SOSIX capability/policy adapters and transport to providers | Common contracts and OS provider interfaces | Application-level Future semantics or private ring contracts |
| `src/os/drivers` and device owners | Hardware submission/completion and device mapping | Provider adapter contracts | Generic task lifetime, profile policy, or cross-device ownership inference |

The `src/lib/common/contracts/execution` directory currently contains
SimpleOS execution/capability/performance contract families. New ring/task
values belong beside those contracts and must be versioned and exported from
that common execution surface rather than hidden in a runtime module. The
paths rooted at `async_ring` now own the hosted ring/provider/mission-admission
implementation. The bounded trace owner lives under `nogc_async_mut_noalloc`;
the qualifying true-static mission executor/storage adapter remains an explicit
gap, not permission to mislabel the hosted wrapper or move contracts into a
convenience runtime file.

## Stable value contract

The V1 public vocabulary is frozen to these names:

```text
SimpleRing<Op, Cpl>
RingToken
RingGeneration
RingAdmission
RingCompletion
RingMappingGrade
AsyncTaskFrame
TaskPollResult
TaskContext
AsyncProfile
```

### Ring identity and storage

`SimpleRing<Op, Cpl>` has a fixed capacity established at construction. It
owns slot state and metadata, but it does not copy payloads or infer payload
ownership. An operation references either a registered payload/buffer or a
caller-owned value whose transfer is explicit in the operation contract.

`RingToken` contains ring identity, slot, and `RingGeneration`. The ring
identity rejects a token belonging to another ring; the slot rejects a token
from another slot lifecycle; and the generation rejects an old token after
reset or reuse. Generation arithmetic has a defined wrap policy and must
fail closed rather than make a wrapped token appear current.

### Admission transaction

Admission is a two-step transaction:

```text
reserve -> RingAdmission::Reserved(token, ownership receipt)
       -> commit -> provider-visible
       -> release -> never provider-visible
```

`commit` is the linearization point at which the provider may observe work.
The reserve path checks capacity and ownership without waiting. Batch reserve
and commit accept an explicit policy: all-or-fail, or explicitly-partial with
the admitted count and each rejected item returned. No API hides partial
admission. A failed reservation has no terminal-completion obligation.

### Completion and cancellation

Each committed single-shot operation transitions once from `Committed` to a
terminal `RingCompletion`: success, failure, or cancelled. A cancellation
request reports one of the following facts:

* released before commit;
* cancellation requested from the provider after commit;
* already terminal;
* unknown or stale token.

Cancellation does not manufacture a second completion. If the provider wins a
race, the completion remains the sole terminal result and the cancellation
receipt records that the operation was already terminal or provider-owned.

Reset drains or marks outstanding work according to the profile, emits a
reset receipt, increments the generation, and prevents delayed provider
completions from waking or completing reused slots. A provider completion
whose ring, slot, generation, or lifecycle does not match is a rejected stale
event, never a wakeup.

### Exact wake and task metadata

The committed metadata carries a task/waker key, task identity, parent
identity, cancellation identity, priority, deadline, trace identity, and
profile fingerprint. A terminal completion emits the exact key to the owning
ready ingress. It does not scan a task table, Future list, or all waiters.

`AsyncTaskFrame` stores typed state that is live across suspension. The
canonical contract does not use a generic byte-array frame. `TaskContext`
provides the profile, clock/deadline view, cancellation view, ring/provider
capabilities, and exact wake sink needed by `poll`. `TaskPollResult` is
`Ready(result)` or `Pending(wait_token)` and polling is nonblocking.

Parent-owned lifetime and cancellation are the default. Detached work requires
an explicit supervisor/service capability and is rejected by both mission
profiles. A frame may submit a ring operation, return `Pending(wait_token)`,
and be re-enqueued only by the exact completion/wake path.

## State and data flow

### Operation lifecycle

```text
construct(capacity, owner, profile)
  -> register payload/capability
  -> reserve (bounded)
  -> commit (provider-visible)
  -> provider take/kick
  -> terminal completion (exactly once)
  -> exact task wake
  -> task poll
  -> release/reuse

cancel may occur before commit, after commit, or after terminal.
reset invalidates all outstanding tokens and publishes a new generation.
```

The software reference provider exercises this full lifecycle without adding
an executor. It takes committed operations from the bounded ring, produces a
typed completion, and sends the exact wake key. It is a conformance provider,
not a hidden production scheduler.

### Ownership and transfer

The default queue model is single-owner/single-mutator. A server shard or
mission executor owns its local ring and ready ingress. A remote owner can
send a bounded transfer record through an explicitly declared ingress; the
receiver becomes the owner only after the transfer receipt. Payload
registration, provider pinning, completion publication, and release are
separate ownership transitions. No hot path performs an implicit copy,
allocation, or ownership guess.

The owner of a mutable frame is its parent executor. A provider may mutate
only provider-private state after commit and may publish a completion value;
it cannot mutate a task frame or wake an arbitrary task. This separation
prevents stale provider events and cross-owner queue mutation from becoming
an ABA or lifetime bug.

## Provider and executor boundaries

### Mapping grades

Every provider declares a `RingMappingGrade`:

| Grade | Meaning | Mission admission |
|---|---|---|
| `direct` | Common operation maps to native queue semantics without a software data-plane translation | Allowed when the profile requires direct |
| `translated` | A bounded adapter translates common values to a native descriptor/notification ABI | Allowed only when boundedness and translation evidence are present |
| `software` | Pure-Simple bounded provider implements the contract in memory | Allowed for common/script; mission policy chooses explicitly |
| `emulated` | Compatibility/emulation path approximates a provider or device | Rejected by mission profiles unless a future profile explicitly admits it |

The provider also reports boundedness, fallback reason, registration limits,
completion ordering, cancellation behavior, and reset behavior. Profile
admission rejects an incompatible grade before operations are admitted. A
fallback result contains requested grade, actual grade, reason, and telemetry
identity; it is never an unreported provider choice.

Executors are specialized implementations of the one task ABI:

* a UI/event executor keeps short semantic work synchronous and suspends
  file, network, DB, process, GPU, or long CPU work;
* a server executor owns shard-local ready and completion rings and uses a
  bounded remote-wake ingress;
* a compute executor may use work stealing only after ownership transfer and
  only in profiles that permit nondeterministic scheduling;
* a mission executor uses fixed-priority or another approved deterministic
  policy with explicit budgets, overload, cancellation, and deadline rules.

The executor consumes `TaskPollResult`; it never turns a `Pending` into a
blocking wait. A compatibility pool is the sole location for legacy blocking
operations and its occupancy, latency, and fallback facts are traced.

## Profile compositions

`AsyncProfile` is a value contract that selects surface and policy, scheduler,
memory mode, ring mapping, assurance, instrumentation, placement, capacities,
blocking, allocation, detachment, fallback, work stealing, and determinism.
Each profile emits a stable fingerprint covering those fields, the task ABI
version, SimpleRing version, provider requirements, resource bounds, and
configuration identity. A semantically relevant change must change the
fingerprint.

| Profile | Executor/policy | Storage and allocation | Mapping/fallback | Determinism |
|---|---|---|---|---|
| `common` | Hybrid profile-compatible executor | Ordinary hosted memory; bounded ring still required | Native preferred; software/translated fallback is explicit | Normal |
| `script` | UI/event-oriented cooperative executor | GC permitted outside ring invariants | Software and hosted providers permitted | Normal event ordering |
| `server` | Shard-local executor plus explicit compute compatibility pool | Arena/slab and registered buffers; zero steady-state hot-path heap objects after admission | Direct preferred; bounded translated/software fallback reported | Shard ownership and admission deterministic |
| `mission_alloc` | Deterministic fixed-priority/cooperative executor | Sealed pre-admitted arenas/slabs; no unrestricted heap after admission | Direct or profile-approved bounded translated/software | Deterministic ownership, overload, wake, cancellation |
| `mission_pool` | Deterministic fixed-priority/cooperative executor | Static compiler-known task/frame, descriptor, buffer, timer, join/cancellation, and trace pools | Direct or profile-approved bounded translated | No work stealing, detached tasks, or unbounded polling |

`mission_alloc` reserves task, operation, buffer, trace, and deadline capacity
before mutation; it allocates in neither ISR, completion hot path, nor durable
publication path. `mission_pool` has no general heap after `Ready`, requires
compiler-known frame bounds, and uses one owner per mutable queue/shard. Both
profiles reject detached tasks, silent fallback, queue growth, blocking poll,
and unknown capacity.

Invalid combinations fail closed. Examples include a mission profile with an
emulated provider, dynamic growth, detached work, work stealing, unrestricted
heap, or unbounded poll budget; a direct-required profile with a software-only
provider; and a deterministic profile with a nondeterministic scheduler.

## Compiler boundary and effect extension points

The compiler is a producer of task shape and effect evidence, not a runtime
owner. Relevant existing ownership points are:

* `src/compiler/00.common/effects.spl` and effect support in
  `src/compiler/00.common` — effect vocabulary and diagnostics;
* `src/compiler/20.hir/hir_lowering/async.spl` and
  `async_errors.spl` — suspension eligibility and lowering diagnostics;
* `src/compiler/50.mir/mir_effects.spl` — MIR effect metadata and future frame
  lowering seam;
* `src/compiler/85.mdsoc` — composition/feature-transform machinery, when a
  compiler transform is eventually enabled.

The reserved effects are `suspend`, `io`, `block`, `alloc.heap`,
`alloc.arena(domain)`, `alloc.pool(pool)`, `spawn`, `detach`, `unsafe`,
`panic`, `nondeterministic`, `clock`, and `device(kind)`. The compiler must
reject or report a profile/effect mismatch before profile admission.

V1 may describe the generated shape as a typed frame containing only values
live across suspension, parent/cancellation metadata, wait token, result, and
stable IDs. It does not promise implicit await, fixed MIR offsets, or a new
grammar until executable compiler evidence exists. Existing explicit async
functions and Future values adapt at the runtime boundary. No compiler phase
may call a provider, allocate a ring slot, or schedule a task while lowering.

## OS, SOSIX, and device seams

OS and device queues are below `SimpleRing` as providers. Their descriptors,
interrupt records, event ports, and fences remain private to the provider
adapter. SOSIX is the capability/policy layer above those providers: it can
authorize a mapping, registered buffer, reset, or fallback, but it cannot
change task poll or completion semantics.

The intended embedded path is:

```text
interrupt/device
  -> bounded CQ record
  -> ready bit or TaskId ready ring
  -> exact task poll
  -> next submission or terminal result
```

ISR code does not allocate, scan tasks, or call a blocking wait. Native
io_uring, POSIX notifications, SimpleOS/SOSIX queues, Vulkan/NVMe queues, and
hardware rings are later provider conformance work. Their native ABI is
translated or direct-mapped only at the provider boundary. No platform lane
may fork the common contract or add an OS-specific Future type.

## Compatibility and migration seams

Migration is additive and preserves observable facts:

1. Freeze common ring/task values and validation/receipt versions.
2. Add the bounded hosted software provider under
   `src/lib/nogc_async_mut/async_ring`; prove reserve, commit, take,
   complete, cancel, reset, stale rejection, and exact wake.
3. Use `src/lib/nogc_async_mut/async_ring/mission_adapter.spl` for hosted
   bounded-preallocation admission and lifecycle receipts only. Add qualifying
   `mission_alloc`/`mission_pool` adapters under
   `src/lib/nogc_async_mut_noalloc/async` only when generated/static backing is
   available. The scalar `mission_ready_set.spl` already provides bounded exact
   wake without explicit collection allocation, but both it and the hosted
   receipt record compiler/static/allocation-free proof as false.
4. Adapt existing Future, host runtime, OS notification, packet, render, and
   device queues through `src/lib/nogc_async_mut/async` and `async_host`.
   The adapters expose blocking, ownership, fallback, and cancellation facts;
   they do not redefine them. `future_compat_adapter.spl` is the first narrow
   seam: it maps nonblocking legacy poll results and preserves an admitted
   wait token without creating a scheduler.
5. Add OS/SOSIX and native device providers behind the provider mapping
   interface, one provider at a time, with direct/translated/software/
   emulated evidence.
6. Only after runtime evidence is stable, enable compiler-generated frames or
   implicit suspension for selected profiles. Existing explicit async syntax
   remains a compatibility input during the migration.
7. Retire blocking production paths and legacy scheduler internals only after
   parity, latency, bounded-memory, stale-generation, and exact-wake evidence.

Monoio, io_uring, existing thread pools, and host Future implementations are
therefore adapters or providers. None is promoted to a second canonical
executor/task ABI. Full host-driver, SimpleOS, NVMe, server/DB, render, and
GPU migration is explicitly later work.

## Startup, hot path, and invalidation

At startup/profile construction, validate capacities, ownership mode,
provider mapping grade, effect policy, blocking policy, and required
instrumentation. Negotiate the provider once and publish the profile and
configuration fingerprint. Startup may build bounded indexes and registration
tables; it must not silently select an incompatible fallback.

The hot path is bounded:

```text
reserve/commit -> provider kick/take -> terminal completion
  -> exact ready insertion -> poll -> next reserve/commit
```

Reserve, commit, take, complete, cancellation lookup, reset-token check,
targeted wake selection, and ready insertion are O(1); batch operations are
O(batch size), never O(total task count). Server and mission steady-state
paths allocate no heap objects after admission/`Ready`. Completion latency,
occupancy/high-water, full events, provider kicks, batch size, and wake-to-poll
latency are measured rather than inferred.

There is no required global ring/task cache in V1. A provider capability
description may be memoized for one composition and is invalidated when the
provider identity, mapping grade, capacity, or profile fingerprint changes.
Reset invalidates all outstanding tokens through the generation and reset
receipt. Payload deregistration, owner transfer, and provider quiesce invalidate
their corresponding handles/epochs. Unknown or partial invalidation fails
closed; it does not reuse old completion data.

## Observability and assurance

Ring telemetry includes occupancy, high-water, full events, reservations,
commits, releases, batches, provider kicks, terminal completions, cancellation
outcomes, stale/duplicate rejects, resets, fallback reasons, and completion
latency. Task telemetry includes spawn, poll, suspension, wake, resume,
completion, cancellation, parent identity, wait token, and profile fingerprint.
Mission profiles use bounded trace storage selected at admission; trace
overflow is an explicit policy result.

Mission evidence must include an effect report, suspension map, task topology
and maximum concurrency, ring-depth proof, memory upper bound, blocking proof,
priority/deadline map, cancellation linearization map, provider/fallback
report, and configuration/artifact fingerprints. Missing evidence blocks
admission; it cannot become a passing default.

## Verification shape and traceability

The lane’s source of truth is `.spipe/simple-ring-async-base/state.md`, which
freezes the shared names, manual-facing steps, and 16 acceptance criteria.
Architecture and implementation evidence must exercise at least:

* constructor and capacity/full/empty branches;
* reserve-release-commit and explicit batch policies;
* generation reuse, reset, stale provider completion, duplicate terminal,
  and cancellation/completion orderings;
* multiple typed operation/completion pairs and software-provider progress;
* exact wakeup while an independent task continues;
* profile validation, provider grade admission, deterministic overload, and
  stable fingerprint changes;
* mission allocation/pool upper bounds, no blocking, no detached work, and
  no hot-path growth.

The frozen manual-facing steps are `Configure the async execution profile`,
`Reserve and commit bounded ring work`, `Complete work and wake the exact
task`, `Reject stale, duplicate, and over-capacity activity`, and `Prove
mission bounds and deterministic policy`. Setup and checking use
`setup_simple_ring_profile_fixture` and `check_simple_ring_invariants`.
Executable SSpec remains under `test/03_system/...`; its operator-readable
mirror belongs under `doc/06_spec/...`, and no executable spec belongs in the
manual tree.

## Explicit exclusions and non-goals

V1 does not complete native io_uring, OS/device ABI, compiler implicit
suspension, a replacement for every existing executor, SimpleOS/SOSIX
migration, NVMe firmware migration, server/DB migration, or RenderRing
migration. It also does not make a software/emulated provider equivalent to a
direct provider, prove a mission profile from a single interleaving test, or
turn a compatibility Future into the canonical task model.

## Consequences

### Positive

* Backpressure, generation safety, cancellation, ownership, terminal
  completion, and exact wakeup have one auditable meaning.
* Hosted and mission profiles can share tests and receipts while selecting
  different storage and scheduling policies.
* Native providers can be added incrementally without leaking platform types
  into common contracts or forking task semantics.
* Synchronous leaves retain a zero-overhead path, and hot-path bounds are
  measurable rather than aspirational.

### Negative

* Every provider and compatibility adapter must report mapping, fallback,
  cancellation, reset, and ownership behavior explicitly.
* The common contract requires versioned values and more receipts than a
  convenience Future API.
* Compiler-generated frames and implicit suspension remain a staged follow-on,
  so migration temporarily carries explicit adapters.

### Risks and mitigations

* **ABI drift:** keep all public names in common execution contracts and
  reject incompatible fingerprints.
* **Hidden blocking:** isolate compatibility pools and trace every block/fallback
  event; executor poll and completion paths remain nonblocking.
* **ABA/stale completion:** require ring/slot/generation matching and reset
  receipts before reuse.
* **Mission overclaim:** fail profile admission when bounds, effects, provider
  grade, or evidence are unknown.
* **Second scheduler/task model:** review every adapter against the one
  `poll`/`Pending` contract before it is admitted to a composition.

## References

* `doc/01_research/runtime/simple_ring_first_async_first_architecture_2026-08-26.md`
* `doc/02_requirements/feature/simple_ring_async_base.md`
* `doc/02_requirements/nfr/simple_ring_async_base.md`
* `.spipe/simple-ring-async-base/state.md`
* `src/lib/common/contracts/execution/`
* `src/lib/nogc_async_mut/async/`
* `src/lib/nogc_async_mut/async_host/`
* `src/lib/nogc_async_mut_noalloc/async/`
* `src/compiler/00.common/effects.spl`
* `src/compiler/20.hir/hir_lowering/async.spl`
* `src/compiler/50.mir/mir_effects.spl`
* `src/os/async/`
* `src/os/sosix/`
