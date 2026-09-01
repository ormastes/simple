<!-- codex-design -->

# Simple Ring and Async Base — Detail Design

Status: V1 design handoff (pure Simple base; platform migrations deferred)
Date: 2026-08-26
Requirements: `doc/02_requirements/feature/simple_ring_async_base.md`, `doc/02_requirements/nfr/simple_ring_async_base.md`
Research: `doc/01_research/runtime/simple_ring_first_async_first_architecture_2026-08-26.md`
SPipe state: `.spipe/simple-ring-async-base/state.md`

## 1. Design boundary and invariants

This lane introduces one public typed data-plane contract and one stackless task
contract. The canonical owner is pure Simple. Native queues (io_uring, SOSIX,
NVMe, packet, render, or device queues) are providers below the contract; they
do not define another operation token, completion shape, scheduler, or task ABI.

V1 guarantees:

1. `SimpleRing<Op, Cpl>` is fixed-capacity at construction and never grows,
   copies payloads, blocks, or overwrites an entry.
2. `RingToken` is `(ring_id, slot, RingGeneration)`; both reset epochs and slot
   reuse versions participate in validation. A stale token cannot complete,
   cancel, wake, or inspect a reused slot.
3. Reservation, commitment, provider visibility, terminal completion, and
   completion consumption are distinct transitions.
4. Every admitted single-shot operation has exactly one terminal result. A
   duplicate or conflicting terminal attempt is an error and telemetry event.
5. Completion carries the exact `TaskId`/waker key. No completion scans a task
   table or a collection of `Future` values.
6. Payload ownership is explicit. A ring stores a registered handle or caller
   lease, never an inferred host pointer and never an implicit copy.
7. `poll(frame, context)` is nonblocking. An executor may park outside `poll`
   after receiving `Pending`, but the ring/provider/task path cannot wait.
8. Profile validation fails closed. Mapping fallback, blocking compatibility,
   allocation, and overload decisions are explicit results and telemetry.

The compiler's implicit-await grammar/HIR/MIR lowering is an extension contract
only. It is not part of V1 and must not be represented by a second Future ABI.
V1 callers construct/poll tasks explicitly or use a named compatibility adapter.

## 2. MDSOC ownership and module shape

The shared contract is a common tree node; sibling layers consume only its
public records:

| Owner | Proposed module | Owns | Must not own |
|---|---|---|---|
| Common contract | `src/lib/common/contracts/execution/simple_ring_async_v1.spl` | Tokens, admissions, completions, task ABI values, mapping grades | OS descriptors, scheduler policy, Future implementation |
| Common policy | `src/lib/common/contracts/execution/async_profile_v1.spl` | `AsyncProfile`, validation, canonical fingerprint | runtime probing or platform conditionals |
| Hosted ring owner | `src/lib/nogc_async_mut/async_ring/simple_ring.spl` | `SimpleRing<Op, Cpl>`, fixed slot/index queues, transitions, telemetry | A second task/Future ABI or native descriptors |
| Reference provider | `src/lib/nogc_async_mut/async_ring/software_provider.spl` | bounded deterministic software completion | a second scheduler or Future model |
| Hosted mission admission | `src/lib/nogc_async_mut/async_ring/mission_adapter.spl` | one-owner Configuring/Ready/Quiesced lifecycle and explicit resource receipts | link-time-static or allocation-free qualification |
| Bounded trace owner | `src/lib/nogc_async_mut_noalloc/async/async_trace_ring.spl` | sealed fixed-capacity task/ring event capture and overload policy | an executor, task scan, or link-time-static proof |
| Mission ready owner | `src/lib/nogc_async_mut_noalloc/async/mission_ready_set.spl` | scalar-only 64-slot admission and exact O(1) ready claim with generation reset | compiler placement, task-frame storage, or backend allocation proof |
| Legacy Future adapter | `src/lib/nogc_async_mut/async_ring/future_compat_adapter.spl` | nonblocking `Poll` to canonical `TaskPollResult` mapping with caller-owned token | waiting, scheduling, or token synthesis |
| Profile executors (follow-on) | profile-specific async modules | ready queue, timers, ownership and scheduling | changing task/ring semantics |
| OS/SOSIX/device adapters | `src/os/async`, `src/os/sosix`, `src/os/drivers` | capability checks and native translation | redefining common tokens/completions |
| Compiler extension | `src/compiler/**` | future effect/lowering evidence | claiming V1 implicit-await support |

`src/lib/nogc_async_mut` remains the default stdlib tier. `common` contains no
Linux/POSIX/GPU/NVMe descriptor, syscall, environment read, or blocking call.
The adapter boundary is the only place where those concerns are introduced.

## 3. Public data structures

The following is the source-level contract. Field names and variants are frozen
for implementation and test planning; the design does not claim that these
types are already implemented.

```text
struct RingGeneration:
    value: u64

struct RingToken:
    ring_id: u64
    slot: u32
    generation: RingGeneration

enum RingSlotState:
    Empty
    Reserved
    Committed
    InFlight
    Terminal

enum PayloadLease:
    Registered(buffer_id: u64, owner: u64)
    CallerOwned(region_id: u64, owner: u64)

struct RingOperation<Op>:
    token: RingToken
    operation: Op
    payload: PayloadLease?
    task_id: u64
    wait_key: u64
    parent_id: u64?
    priority: i32
    deadline_ns: u64?
    dependency: u64?
    trace_id: u64
    flags: u32

struct RingReservation<Op>:
    token: RingToken
    owner_id: u64
    operation: Op?

enum RingAdmission<Op>:
    Admitted(reservation: RingReservation<Op>)
    BatchAdmitted(reservations: [RingReservation<Op>], requested: u32)
    Full(requested: u32, available: u32)
    Rejected(error: RingError)

enum RingTerminal<Cpl>:
    Success(value: Cpl)
    Failure(error: RingProviderError)
    Cancelled(reason: RingCancelReason)

struct RingCompletion<Cpl>:
    token: RingToken
    terminal: RingTerminal<Cpl>
    task_id: u64
    wait_key: u64
    provider_id: u64
    completed_at_ns: u64
    trace_id: u64

struct RingResetReceipt:
    ring_id: u64
    previous_epoch: u64
    new_epoch: u64
    invalidated: u32
    stale_completions: u32

struct RingCapacity:
    operation_slots: u32
    completion_slots: u32
    max_batch: u32
    registered_payloads: u32
    wake_entries: u32
    trace_entries: u32

struct SimpleRing<Op, Cpl>:
    ring_id: u64
    owner_id: u64
    generation_epoch: u64
    slots: [RingSlot<Op, Cpl>]
    free_indices: [u64]
    submission_indices: [u64]
    completion_indices: [u64]
    free_head/free_tail/free_count: u64
    submission_head/submission_tail/submission_count: u64
    completion_head/completion_tail/completion_count: u64
    reserved: u32
    committed: u32
    in_flight: u32
    terminal: u32
    capacity: RingCapacity
    telemetry: RingTelemetry
```

`RingSlot<Op, Cpl>` is a preallocated cell containing the slot generation,
state, operation metadata, optional terminal value, and a completion-publication
marker. The completion queue stores `RingCompletion<Cpl>` values (or fixed
indices to cells in a no-copy implementation). `operation_slots` and
`completion_slots` are both finite; V1 requires `completion_slots >=
operation_slots` so a terminal result always has a reserved publication cell.

The three fixed index queues make arbitrary reservation release, provider take,
and completion consumption O(1) without scanning holes or slicing arrays.
`ring_id` is allocated once by the owning domain and is never reused while an
old ring can still publish. `RingGeneration.value` advances on reset and each
slot reuse. Checked increment returns
`RingError.GenerationExhausted` rather than wrapping.

## 4. Ring error and outcome vocabulary

```text
enum RingError:
    InvalidCapacity
    CapacityOverflow
    WrongOwner
    InvalidReservation
    InvalidTransition
    UnknownToken
    StaleToken
    GenerationExhausted
    AlreadyCommitted
    NotCommitted
    NotInFlight
    TerminalAlreadyPublished
    CompletionQueueFull
    PayloadOwnership
    PayloadNotRegistered
    ResetInProgress
    BatchInsufficient
    ProviderRejected
    ProfileRejected
    WakeCapacityFull

enum RingCancelOutcome:
    CancelledBeforeCommit(token: RingToken)
    ProviderCancelRequested(token: RingToken)
    AlreadyTerminal(token: RingToken)
    UnknownOrStale(token: RingToken)
    CancelRejected(error: RingError)

enum RingCancelReason:
    CallerRequested
    ParentCancelled
    DeadlineExpired
    ProviderReset
    OverloadRejected

enum RingProviderError:
    NotSupported
    ResourceUnavailable
    InvalidPayload
    DeadlineMissed
    DeviceFault
    TranslationFailed
    ProviderReset
    ExplicitFallback(reason: text)
```

`RingAdmission.Full` is a normal nonblocking capacity result, not an error
requiring retry sleep. `RingCompletion` is terminal only; a provider that needs
progress notifications must use a later explicitly multi-shot operation type.

## 5. Ring algorithms and state machine

### 5.1 Construction and capacity

`SimpleRing.new(owner_id, ring_id, capacity)` validates nonzero capacities,
`max_batch <= operation_slots`, `completion_slots >= operation_slots`, and
checked index arithmetic. It allocates exactly `operation_slots` fixed cells,
initializes every slot to `Empty`, sets both queue cursors to zero, and creates
bounded telemetry storage. It performs no later allocation. Capacity is not
rounded silently; a requested zero, overflow, or unsupported static bound is
`RingError.InvalidCapacity`/`CapacityOverflow`.

The ring is single-owner for mutation. A provider may be a distinct consumer
only through the provider seam, which establishes the producer/consumer handoff
and memory ordering. Multi-producer use requires a separate bounded ingress
owned by one ring owner; it is not implied by `SimpleRing`.

### 5.2 Reserve, release, and commit

`reserve()` checks `free = operation_slots - reserved - committed - in_flight -
terminal` in O(1). If zero it increments `full_events` and returns
`RingAdmission.Full(1, 0)`. Otherwise it allocates the next `submission_tail`
slot, reads the current slot generation, marks it `Reserved`, increments
`reserved`, advances the tail, and returns a `RingReservation` containing the
token. No provider can observe this slot.

`release(reservation)` validates owner, ring id, slot, generation, and
`Reserved` state. It marks the cell `Empty`, decrements `reserved`, and records
the release. A reservation that is not the newest tail may leave a reclaimable
hole; the owner advances `submission_head` over only `Empty` cells before the
next admission. This is bounded and does not scan the task set. A provider is
never allowed to consume a released reservation.

`commit(reservation, operation, metadata)` validates the same token and payload
lease, writes the typed operation and metadata into the fixed cell, changes
`Reserved -> Committed`, decrements `reserved`, increments `committed`, and
publishes the provider-visible cursor only after all fields are written. It
does not copy or allocate. Hosted V1 `commit_batch(task_keys, operations,
AllOrNothing)` validates owner, non-empty equal input lengths, every task key,
and total free capacity before changing a slot. It then reserves and commits
the validated batch without constructing an internal batch list and returns a
count receipt. V1 deliberately has no partial-admission policy, so it can never
report a partial batch as a full success; a future partial policy requires a
separate explicit receipt contract.

### 5.3 Provider take and terminal completion

`provider_take(max)` consumes committed cells from `submission_head` in FIFO
order, changes `Committed -> InFlight`, decrements `committed`, increments
`in_flight`, and returns at most `max` operations. `max` is bounded by the
caller and `capacity.max_batch`; no provider poll loops over uncommitted slots.

`complete(token, terminal)` validates ring id, slot, epoch and slot version,
then requires `InFlight`. It performs the terminal linearization once:

1. Write the typed terminal value and completion metadata.
2. Change `InFlight -> Terminal`; decrement `in_flight`; increment `terminal`.
3. Append one `RingCompletion<Cpl>` to the fixed completion queue.
4. Publish the exact `task_id`/`wait_key` wake record.

If the completion queue is unexpectedly full, the provider contract reports
`RingError.CompletionQueueFull` and enters a provider-fault/reset path; it must
not discard the result or publish a second completion. Because completion
capacity is reserved one-for-one with operation capacity, this condition is a
configuration or provider violation, not ordinary backpressure.

`take_completion()` consumes one CQ cell in O(1), revalidates the token and
terminal marker, changes `Terminal -> Empty`, increments the slot version for
reuse, decrements `terminal`, returns the typed completion, and returns the
payload lease to its recorded owner. A second `take_completion` for that token
returns `UnknownToken`/`StaleToken`.

### 5.4 Cancellation and reset

`cancel(token)` linearizes against `commit` and `complete` in the ring owner:

| Current state | Result | Provider visible? |
|---|---|---|
| `Reserved` | `CancelledBeforeCommit` and release | No |
| `Committed` | `ProviderCancelRequested` (provider must finish terminally) | Yes |
| `InFlight` | `ProviderCancelRequested` | Yes |
| `Terminal` | `AlreadyTerminal` | Already terminal |
| `Empty` or wrong generation | `UnknownOrStale` | No |

Provider cancellation is a request, not forceful interruption. The provider
must call `complete(... Cancelled(...))` or `complete(... Failure(...))` exactly
once. Deadline expiry follows the same path as caller cancellation.

`reset()` is permitted only by the ring owner after quiesce or an explicit
provider-reset policy. It advances `generation_epoch` with checked arithmetic,
marks all `Reserved`, `Committed`, and `InFlight` cells invalid, records a
`RingResetReceipt`, clears submission/completion cursors, and wakes no task for
invalidated work. Delayed completions fail `StaleToken`; they cannot touch a
reused slot. A reset that cannot advance the epoch fails closed.

## 6. Task ABI and task state machine

```text
struct TaskIdentity:
    task_id: u64
    parent_id: u64?
    supervisor_id: u64?

struct TaskContext:
    identity: TaskIdentity
    cancellation: CancellationState
    priority: i32
    deadline_ns: u64?
    wait_token: WaitToken?
    trace_id: u64
    profile_fingerprint: text
    ring_owner_id: u64

struct AsyncTaskFrame<T>:
    identity: TaskIdentity
    state_id: u32
    context: TaskContext
    live_state: T
    result: Result<T, TaskError>?

enum TaskPollResult<T>:
    Ready(result: T)
    Pending(wait_token: WaitToken)

struct WaitToken:
    ring_id: u64
    token: RingToken
    task_id: u64
    wait_key: u64
```

The implementation may specialize `AsyncTaskFrame<T>` per generated state
machine. `live_state` means only values live across a suspension point; the
canonical path never uses an opaque generic byte array. `TaskPollResult` is
called as `poll(frame, context) -> Ready(result) | Pending(wait_token)` and
returns a `Result<T, TaskError>` in `Ready` when the task can fail. `TaskError`
includes provider, cancellation, deadline, profile, and internal transition
errors.

Task lifecycle:

```text
New -> ReadyToPoll -> Polling -> Pending(wait_token) -> ReadyToPoll
                         |             |
                         v             v
                     Completed     CancelRequested
                         |             |
                         +--------- Cancelled
```

`Polling` is owned by exactly one executor. A poll may reserve/commit a ring
operation and return `Pending`; the provider's terminal completion emits one
ready record for the task's `wait_key`. Duplicate wake records are coalesced by
a bounded `ready` bit/queue and counted, never multiplied without bound. A
parent cancellation propagates to children before join completion. Detached
work requires an explicit supervisor/service capability and is rejected by
`mission_alloc` and `mission_pool`.

Executors select a ready task by profile policy, invoke `poll`, and return to
the scheduler. They do not call `block_on`, sleep, scan all tasks, or poll all
futures. An idle executor can park using a provider-specific wait outside the
task/ring contract.

## 7. Provider interface and reference software provider

```text
enum RingMappingGrade:
    Direct
    Translated
    Software
    Emulated

struct RingProviderDescriptor:
    provider_id: u64
    name: text
    mapping: RingMappingGrade
    bounded: bool
    supports_cancel: bool
    supports_reset: bool
    max_depth: u32
    fallback_reason: text?
    capability_fingerprint: text

trait RingProvider<Op, Cpl>:
    fn descriptor() -> RingProviderDescriptor
    fn admit(profile: AsyncProfile) -> Result<ProviderBinding, RingError>
    fn take(ring: SimpleRing<Op, Cpl>, budget: u32) -> Result<u32, RingError>
    fn cancel(ring: SimpleRing<Op, Cpl>, token: RingToken) -> RingCancelOutcome
    fn progress(ring: SimpleRing<Op, Cpl>, budget: u32) -> Result<u32, RingError>
    fn reset(ring: SimpleRing<Op, Cpl>) -> Result<RingResetReceipt, RingError>
```

`admit` compares mapping grade, boundedness, depth, cancellation, and reset
facts against the profile. A rejected grade returns `ProfileRejected` with the
provider descriptor and emits an admission event. An accepted translated,
software, or emulated path returns an explicit `chosen_path`/fallback record;
it is never silently treated as direct.

### Software provider V1

`SoftwareRingProvider<Op,Cpl>` owns a fixed array of provider entries and a
deterministic `progress_budget`. It is `RingMappingGrade.Software`, bounded,
nonblocking, and suitable for common/script/server tests. It does not allocate,
spawn, or maintain a scheduler. The reference sequence is:

1. `take` moves committed operations into the fixed provider array.
2. `progress` processes up to `budget` entries in token order.
3. The configured test policy returns `Success`, `Failure`, or
   `Cancelled` through `ring.complete` exactly once.
4. `ring.complete` publishes one exact wake record; the test executor inserts
   only that task into its ready queue.
5. `take_completion` reclaims the slot and payload lease.

The provider also exposes explicit `cancel`, `reset`, stale completion, and
duplicate completion probes. A provider error stops progress and leaves a
diagnostic receipt; it never retries by blocking or silently switching to a
different provider.

## 8. Profiles, validation, and fingerprints

```text
struct AsyncProfile:
    name: ProfileName
    async_surface: AsyncSurface
    async_policy: AsyncPolicy
    scheduler: SchedulerPolicy
    memory: MemoryPolicy
    ring_mapping: RingMappingPolicy
    assurance: AssuranceLevel
    instrumentation: InstrumentationLevel
    placement: PlacementPolicy
    capacities: ProfileCapacities
    blocking: BlockingPolicy
    allocation: AllocationPolicy
    detachment: DetachmentPolicy
    fallback: FallbackPolicy
    work_stealing: WorkStealingPolicy
    determinism: DeterminismPolicy
    compiler_features: CompilerFeatureFacts
```

Canonical profile intent:

| Profile | Surface/policy | Scheduler | Memory and bounds | Mapping/assurance |
|---|---|---|---|---|
| `common` | implicit-extension intent; latency may suspend | hybrid | finite heap/GC capacities; blocking only named compatibility pool | direct preferred, bounded translated/software allowed; normal |
| `script` | implicit-extension intent; event APIs | UI/event | GC; finite ring/task/trace capacities | software/emulation allowed; normal |
| `server` | implicit-extension intent; latency required | shard-local, remote-wake ingress | pre-admitted arena/slab; zero steady-state hot-path heap | direct preferred, bounded translated allowed; hardened |
| `mission_alloc` | explicit V1 task calls; async required | deterministic fixed-priority/cooperative | sealed bounded arenas/slabs; no heap after admission | direct or policy-approved translated only; mission |
| `mission_pool` | explicit V1 task calls; async required | deterministic fixed-priority/cooperative | static compiler-sized task/descriptor/buffer/timer/join/trace pools | direct or policy-approved translated only; mission |

The word “implicit” in the first three rows is a source-surface target, not a
V1 compiler claim. Until compiler feature evidence exists, callers use explicit
task construction and the profile reports `implicit_await_unavailable`.

Validation is deterministic and ordered:

1. Verify all capacities are positive, finite, and internally consistent:
   `completion_slots >= operation_slots`, `ready_capacity >= task_capacity`,
   `max_batch <= operation_slots`, and trace/wake pools cover configured maxima.
2. Reject blocking in ring/provider/task paths. If compatibility blocking is
   enabled, require a named compatibility pool and telemetry sink.
3. For `mission_alloc`, require sealed arenas, admission-time reserves for
   tasks/operations/buffers/traces/deadlines, no ISR/CQ/durable-publication
   allocation, no detached work, no work stealing, and deterministic overload.
4. For `mission_pool`, additionally require compiler-known frame bounds, static
   pools for tasks/descriptors/buffers/timers/joins-cancellation/traces, no heap
   after `Ready`, and a single mutable owner per queue/shard.
5. Reject `DirectRequired` for a provider whose descriptor is not `Direct`, and
   reject translated/software/emulated providers when bounded translation is
   not explicitly allowed. Record the reason.
6. Reject unknown compiler features, unbounded polling, random scheduling, or
   detachment in a mission profile. No invalid combination is normalized.

`profile_fingerprint(profile, provider)` serializes a canonical ordered record
containing ABI version, SimpleRing version, every effect/policy value,
provider requirements and capability fingerprint, all resource bounds,
instrumentation, placement, compiler feature facts, and configuration identity.
It hashes the record without pointers, timestamps, or map iteration order.
Changing any semantically relevant field changes the fingerprint; changing
only a diagnostic label does not. The fingerprint is copied into every
`TaskContext`, completion receipt, benchmark, and mission evidence bundle.

## 9. Ownership, payloads, and SOSIX boundaries

Payload admission is a two-party transition: caller/registered owner -> ring ->
provider -> ring -> caller/registered owner. A provider may retain a registered
buffer only while its token is `Committed` or `InFlight`. Cancellation before
commit returns the lease immediately; cancellation after commit returns it only
through terminal completion. An owner mismatch or reuse before completion is
`RingError.PayloadOwnership`.

SOSIX capability and IOMMU/VM checks happen in the SOSIX provider adapter. The
common ring sees only a validated `PayloadLease`, `RingToken`, and provider
descriptor. A cross-owner transfer uses a bounded ingress and an explicit
ownership receipt; it does not turn `SimpleRing` into an MPMC queue. Interrupt
handlers publish bounded completion/event records and set a ready bit; they do
not allocate, call `poll`, or wake by scanning all tasks.

## 10. Telemetry and evidence

```text
struct RingTelemetry:
    occupancy: u64
    high_water: u64
    full_events: u64
    reservations: u64
    releases: u64
    commits: u64
    partial_batches: u64
    provider_takes: u64
    provider_kicks: u64
    completions: u64
    cancellations: u64
    stale_rejects: u64
    duplicate_rejects: u64
    wake_published: u64
    wake_coalesced: u64
    completion_latency_buckets: [u64]
    trace_dropped: u64

struct TaskTelemetry:
    polls: u64
    suspensions: u64
    wakes: u64
    resumes: u64
    completed: u64
    cancelled: u64
    poll_latency_buckets: [u64]
```

Counters saturate rather than allocate. Trace entries are fixed-size and
profile-selected; overflow increments `trace_dropped` and cannot block a hot
path. Events include profile fingerprint, ring/token identity, task/wake key,
provider path, and timestamp where the profile permits a clock. Offline
evidence derives p50/p99/p99.9 latency, occupancy/high-water/full events,
batch/kick counts, wake latency, and max RSS or arena/pool high-water.

## 11. Compatibility migration and refactoring map

Adapters are temporary compatibility seams. New APIs and implementation code
must target the common ring/task contracts; adapters may not add a scheduler.

| Existing surface | Adapter mapping | Required behavior |
|---|---|---|
| `src/lib/nogc_async_mut/async/future.spl`, `std.async.future.Future<T>` | `FutureAdapter<T>` presents a one-shot `AsyncTaskFrame` and maps `Poll.Ready/Pending` to `TaskPollResult` | Preserve `map/then/timeout`; no new canonical ring ABI; opaque `state: [u8]` is legacy only |
| `src/lib/nogc_async_mut/async/future.spl`, `Future<T>` | `future_compat_adapter.spl` maps its nonblocking `Poll` to the canonical `TaskPollResult` and preserves a caller-supplied admitted token | The adapter never waits or creates a scheduler; legacy await/runtime behavior remains outside this proof |
| `src/lib/nogc_async_mut/async_host/future.spl`, `HostFuture<T>` | A future `HostFutureAdapter<T>` reserves one operation or represents a direct ready leaf | `block_on` remains explicit compatibility work and emits blocking telemetry; it is forbidden from `poll` |
| `HostRuntime`/`HostScheduler` | `CompatibilityExecutorAdapter` owns a bounded ingress and invokes canonical task frames | Work stealing and threads remain profile-owned; no second task identity or completion contract |
| `src/os/async/os_future.spl` (`OsFuture<T>`) | `OsFutureAdapter<T>` turns `OsPoll.Ready/Pending` into canonical terminal/wait outcomes | `OsWaker.notification_id/task_id` becomes exact `WaitToken`; no global notification scan |
| `ReadyFuture<T>` | synchronous ready-leaf adapter | No ring slot, Future allocation, task frame, or scheduler entry |
| `src/os/drivers/nvme/nvme_async.spl` / `NvmeAsyncCompletion` | NVMe provider maps command id to `RingToken`; CQE status is typed `Cpl` | IRQ notification is provider wake; `wait_completion_notify` is compatibility-only and never called by `poll` |
| `src/os/drivers/nvme/nvme_queue.spl` | native SQ/CQ remains device-owned below `RingProvider` | Preserve phase bits and DMA ownership; expose direct/translated descriptor facts |
| `src/os/sosix/core/completion_queue.spl` and SOSIX bounded queues | SOSIX provider translates `SosixCompletion` to `RingCompletion<Cpl>` | Preserve bounded rejection and capability checks; map overflow to explicit provider fault |
| `src/lib/nogc_async_mut/io/packet_ring.spl` / `packet_io.spl` | packet provider uses typed operation/completion and `PacketBufferLease` | Preserve RX/TX ownership and explicit lease return; no common packet descriptor |
| render/device queue facades | typed provider adapters | Provider mapping and fallback are admission facts; native migrations are follow-on work |

Migration order is: land common contracts and reference provider; add adapters
and evidence; route one host/OS surface at a time; move providers behind
`RingProvider`; remove production blocking paths only after parity evidence.
Existing public async APIs remain usable during this order (NFR-SRA-011).

## 12. Explicit runtime/facade decision

The implementation decision record is intentionally explicit so a missing
native capability cannot be hidden by a shortcut:

```text
runtime_need:
  V1 base contracts, profiles, telemetry, task frames, and software provider
  require no new native runtime capability. Existing native queues are later
  providers, not prerequisites for the pure-Simple base.

facade_checked:
  src/compiler_rust/runtime/src/async_runtime.rs
  src/compiler_rust/runtime/src/executor.rs
  src/compiler_rust/runtime/src/async_driver_sffi.rs
  src/os/async/{os_future,os_poll,os_waker,ring_buffer}.spl
  src/os/drivers/nvme/{nvme_async,nvme_queue_notify}.spl
  src/os/sosix/core/completion_queue.spl
  src/lib/nogc_async_mut/{async,async_host,io}.spl
  These provide compatibility seams and native capability facts; none is
  accepted as the canonical ring/task ABI.

chosen_path:
  pure-Simple common contracts + fixed-capacity software provider + explicit
  profile validation/fingerprint + adapters owned by OS/device/runtime layers.

rejected_shortcuts:
  reuse Future or OsFuture as the ring contract;
  retain a generic [u8] task frame as the canonical representation;
  call block_on or NotificationWait from poll/provider completion;
  silently fall back from direct to software/emulated mapping;
  grow queues, traces, task tables, or completion storage on demand;
  scan every task/Future after a completion;
  add platform descriptors/syscalls to common modules;
  introduce a second scheduler or claim compiler implicit-await is V1.
```

## 13. Requirement and evidence mapping

The implementation and test plan shall trace requirements as follows:

| Requirements | Design evidence | Focused executable evidence |
|---|---|---|
| REQ-SRA-001..005 | capacity, token, transaction, terminal, cancel/reset sections | constructor/boundary, generation reuse, duplicate terminal, race-order unit cases |
| REQ-SRA-006..009 | payload and task ABI/state sections | ownership transfer, exact wake, parent cancellation, independent pending-task integration |
| REQ-SRA-010..012 | provider/profile tables and validation | mapping admission and profile matrix |
| REQ-SRA-013..015 | mission rules and canonical fingerprint | capacity proofs, invalid combinations, stable/change fingerprint cases |
| REQ-SRA-016..018 | migration, decision record, compiler boundary | Future/OsFuture/SOSIX adapter tests and explicit implicit-await-unavailable assertion |
| NFR-SRA-001..012 | O(1) algorithms, bounded telemetry, evidence section | branch coverage, performance receipt, blocking guard, generated manual and traceability |

System scenarios use the frozen SPipe steps exactly:

1. `Configure the async execution profile`
2. `Reserve and commit bounded ring work`
3. `Complete work and wake the exact task`
4. `Reject stale, duplicate, and over-capacity activity`
5. `Prove mission bounds and deterministic policy`

Shared helpers are `setup_simple_ring_profile_fixture` and
`check_simple_ring_invariants`. Any temporary provider/scenario implementation
must fail with `assert(false)` or `fail(...)`; no placeholder pass is evidence.

## 14. V1 exclusions and handoff gates

This design does not claim native io_uring, full executor replacement, SOSIX or
SimpleOS migration, NVMe firmware migration, server/DB migration, RenderRing,
or compiler implicit-await lowering. Those phases must first supply provider,
ownership, performance, and assurance evidence against this contract.

Implementation handoff is blocked until each public transition has real unit
coverage (including capacity, wrap, stale/duplicate, cancellation/reset,
profile, and fingerprint branches), integration coverage exercises multiple
typed rings and independent progress, and the software provider demonstrates
exactly-one completion plus exact wake without a task-count scan.
