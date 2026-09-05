<!-- codex-research -->

# Simple Ring-First and Async-First Architecture

## Executive Decision

Simple should converge on one invariant:

``` text
Simple source
→ effect inference + implicit suspension
→ compiler-generated stackless task
→ profile-specific executor
→ SimpleRing SQ/CQ
→ native OS/device queue whenever possible
```

1. `SimpleRing` is the universal asynchronous data-plane contract.
2. Latency-bearing APIs are async by default while source stays sequential-looking, similar to JavaScript Promise/await ergonomics.
3. Proven synchronous leaves remain direct and zero-overhead.
4. Mission-critical modes support async; they restrict blocking, allocation, queue growth, scheduling, cancellation, and nondeterminism.
5. Add `mission_alloc` and `mission_pool`.
6. Use one task ABI with specialized UI, server, compute, embedded, and mission executors.
7. Migrate NVMe firmware and embedded SimpleOS to the same ring/task model.

## Current State and Gaps

Simple already has async/await, Futures, completion-oriented host I/O, Linux io_uring support, async POSIX/kernel/process/UI modules, SOSIX async concepts, GPU/GUI/Web/2D offload work, and NVMe firmware with SQ/CQ plus bounded cooperative tasks.

The main problem is fragmentation. Multiple schedulers, Future implementations, blocking compatibility paths, polling runtimes, and driver facades should become:

``` text
one compiler task model
+ one SimpleRing contract
+ profile-specific executors/providers
```

Priority gaps are blocking Future waits, accidental serialization, blocking driver operations, hot-path allocation, generic suspension-frame arrays, embedded task scanning, and insufficient end-to-end nonblocking tests.

## Research Synthesis

| Source | Lesson | Simple direction |
|---|---|---|
| Linux io_uring | Shared SQ/CQ, batching, registered resources | Platform-independent SimpleRing; io_uring is a Linux provider |
| Arrakis | Protected control plane plus direct data path | SOSIX controls policy/setup; rings handle steady state |
| Demikernel | Uniform async API over heterogeneous datapaths | Direct, translated, software, bounded-emulated providers |
| SPDK / Seastar | Per-core ownership avoids shared locks | Shard-owned server/storage I/O |
| Rust async | State machines store live-across-await state | Typed compiler-generated task frames |
| Embassy | Static task storage and targeted wakeups | Fixed/generated task storage for embedded and mission_pool |
| Koka | Effect inference tracks suspension/side effects | Expand Simple effects beyond Sync/Async |
| Swift structured concurrency | Parent-owned tasks improve lifetime/cancellation | Structured concurrency by default |
| Ravenscar / SPARK | Bounded concurrency works for high assurance | Deterministic mission async |
| Vulkan / Vulkan SC | GPU work is queue/fence based | Common asynchronous RenderRing |
| DBMS io_uring studies | Mechanical conversion may not improve performance | Benchmark every migration |
| Coz | Causal profiling finds globally useful optimizations | Add host causal profiling |

Target: JavaScript-like ergonomics + inferred effects + compiler state machines + structured concurrency + static embedded task storage + shard ownership + ring-first I/O.

## SimpleRing V1

Use typed rings rather than one universal descriptor:

``` text
SimpleRing<StorageOp, StorageCompletion>
SimpleRing<NetworkOp, NetworkCompletion>
SimpleRing<RenderOp, RenderCompletion>
SimpleRing<DeviceOp, DeviceCompletion>
SimpleRing<EventOp, EventCompletion>
SimpleRing<ComputeOp, ComputeCompletion>
```

Common metadata: operation token, ring generation, resource/capability handle, task/waker key, priority, deadline, dependency/timeline value, flags, payload reference, and trace ID.

Required properties:

- SPSC/single-owner by default.
- Explicit backpressure; no silent growth or blocking.
- Exactly one terminal completion per admitted operation unless multi-shot.
- Slot + generation protection against stale completion/ABA.
- Registered buffers with explicit ownership.
- Nonblocking dependency/timeline waits.
- Explicit cancellation outcome.
- Reset generation invalidates stale work.
- Batched reserve/commit.
- Exact task wakeup; no global Future scan.
- Occupancy/high-water/batch/kick/latency telemetry.
- SOSIX capability and IOMMU/VM enforcement.

Mapping grades are `direct`, `translated`, `software`, and `emulated`. Mission profiles can require direct or bounded translated mappings.

## Async-First Language Semantics

Ordinary functions are effect-inferred:

``` simple
fn load_document(id):
    val row = db.document(id)
    val data = file.read(row.path)
    Document(row, data)
```

If an expression is `Future<T>` and `T` is expected, the compiler may insert suspension when the function permits it.

``` simple
val user: User = fetch_user(id)                 # implicit await
val future_user: Future<User> = fetch_user(id)  # preserve Future

sync fn validate_header(h) -> Result<Header>:
    ...
```

Keep `async fn` for APIs that must remain suspension-capable.

Implicit await occurs only when expression type is `Future<T>`, expected type is `T`, and suspension is permitted. It is not inserted when a Future is explicitly expected, inside explicit parallel constructs, in `sync fn`, or in explicit-await profiles.

The compiler should warn about accidental serialization of independent async calls.

### Task lowering

Generate typed frames containing only state live across suspension:

``` text
TaskFrame<load_document>
  state
  parent
  cancellation
  wait_token
  result
  id
  row
  data_buffer_handle
```

Core ABI:

``` text
poll(frame, context) -> Ready(result) | Pending(wait_token)
```

Executors never perform blocking waits from `poll`.

## Effect System

Expand effects to include:

``` text
suspend
io
block
alloc.heap
alloc.arena(domain)
alloc.pool(pool)
spawn
detach
unsafe
panic
nondeterministic
clock
device(kind)
```

Structured concurrency is default. Detached work requires a supervisor/service capability and is forbidden in mission profiles.

## Compiler Mode Variations

Keep build closure independent from runtime semantics.

| Axis | Values |
|---|---|
| build.closure | tiny, normal, full |
| language.surface | common, script |
| async.surface | implicit, explicit, off |
| async.policy | allowed, required_for_latency, forbidden |
| scheduler | ui, sharded, hybrid, compute_work_steal, fixed_priority, cooperative |
| memory | gc, heap, arena, pool, static |
| ring.mapping | direct_required, completion_required, emulation_allowed |
| assurance | normal, hardened, mission |
| instrumentation | none, error, debug, trace, coverage, profile, sanitize |
| placement | static, dynamic, auto |

Canonical presets:

- `common`: implicit async, hybrid scheduler, native ring preferred.
- `script`: implicit async, GC, UI/event executor.
- `server`: shard-local arena/slab, per-core I/O plus compute pool.
- `mission_alloc`: bounded domain arenas, deterministic scheduler.
- `mission_pool`: fixed pools/static storage, deterministic cooperative/fixed-priority scheduler.

Every artifact embeds a profile fingerprint covering ABI, SimpleRing version, effects, memory/scheduler policy, provider requirements, resource bounds, instrumentation, and configuration hash.

## Mission-Critical Async

Async is supported. Prohibit unbounded tasks, hidden blocking, unknown queue growth, unconstrained allocation, detached work, unsafe cancellation, silent fallback, and unbounded polling.

### mission_alloc

- No unrestricted system heap after admission.
- Sealed bounded domain arenas/slabs allowed.
- No allocation in ISR, CQ hot path, or durable publication path.
- No arena growth.
- Reserve task, operation, buffer, trace, and deadline capacity before mutation.

### mission_pool

- No general heap after Ready.
- Generated typed task pools/static task storage.
- Fixed pools for descriptors, buffers, timers, joins/cancellation, traces.
- Exact compiler-known frame sizes.
- Static topology checked at link time where possible.
- No work stealing.
- Single owner per mutable queue/shard.
- ISR only posts bounded completion/event records and wakes tasks.
- Idle CPU sleeps instead of scanning tasks.

Mission evidence includes effect report, suspension map, task topology/max concurrency, ring-depth proof, memory upper bound, blocking proof, priority/deadline map, cancellation map, provider/fallback report, and configuration/binary hashes.

## Executors

Use one task ABI with specialized executors:

- UI executor: short state/event logic sync; file/DB/network/process/GPU/long CPU work suspends.
- Server executor: one shard per core/service, local ready ring, remote-wake ingress, completion rings, timer wheel, no global mutex.
- Compute executor: independent CPU-bound work; work stealing allowed only after ownership transfer.
- Mission executor: fixed-priority or approved deterministic schedule, bounded budgets/capacities, explicit overload policy.

## Host Runtime Migration

1. Add common ring contracts.
2. Add async ring integration.
3. Add OS ring ABI.
4. Add platform ring providers.
5. Convert existing driver APIs into compatibility adapters.
6. Keep thread pool only as explicit blocking/compute compatibility pool.
7. Remove blocking Promise waits from Future execution.
8. Put Monoio behind the provider interface rather than a second task model.
9. Retire blocking production async-driver paths after parity.

## Embedded SimpleOS Migration

``` text
interrupt/device
→ bounded CQE
→ ready bit / TaskId ready ring
→ poll exact task
→ submit next operation or complete
```

Use generated/static task storage, ready bitmap/ring, fixed timer wheel, per-core rings, interrupt-driven wake, idle sleep, no task scans, no ISR allocation, and SOSIX/POSIX adapters over the same native ring.

Driver lifecycle:

``` text
create → bind → register → ready
→ submit/complete
→ quiesce → drain/cancel → reset → generation bump
```

## NVMe Firmware Migration

Do not rewrite protocol, FTL, WAL, checkpoint, recovery, GC, maintenance, or existing ownership logic.

Map host queues:

``` text
NVMe host SQ/CQ
→ SimpleRing<NvmeCmd, NvmeCpl>
```

Add internal HIL, FTL, per-channel NAND/FIL, DMA/ECC, and completion rings. Convert firmware tasks to mission_pool task-frame types.

Required changes include fixed storage, free-index rings for larger pools, generation in every token, stale completion rejection after reset, explicit CQ-full backpressure, one owner per queue/channel, cross-core message rings, task-state abort/timeout, and correct power-loss treatment.

Proof targets include queue bounds, no SQ overwrite, exactly-one terminal CQE, stale-generation rejection, unique pool ownership, cancellation/durability safety, foreground non-starvation, and maintenance progress.

## Web Server Lane

Use one server shard per core with accept, network, file, timer, DB-client, and compute rings.

- One shard owns each connection.
- Request tasks are children of connection tasks.
- Parser/router logic stays short/synchronous.
- Socket/file/DNS/DB/TLS/RPC/timer waits suspend.
- Heavy CPU work uses compute executor.
- Backpressure propagates through streams/connections/admission.
- Disconnect cancels child work.
- No executor-thread blocking.
- Zero-copy paths are benchmark-gated.
- HTTP/2 and HTTP/3 stream counts are bounded.

## DB Server Lane

``` text
network shard
→ transaction/query task
  → parser/planner: synchronous CPU
  → buffer miss: storage ring
  → WAL append/flush: durability ring
  → remote/shuffle: network ring
  → heavy operator: compute task
  → result: network ring
```

Shard mutable transaction/page ownership by core, use async buffer misses/scans, issue independent reads before awaiting, register page/WAL buffers, group commits, define cancellation around the durable commit point, and run maintenance as budgeted background tasks. Direct NVMe is optional and benchmark-gated.

## GUI, Web, 2D, GPU, and CPU Rendering Lane

``` text
GUI / Web / 2D / WM
→ immutable Scene/DrawIR
→ seal + admit
→ RenderRing
   → GPU provider
   → CPU provider
→ completion / present receipt
```

CPU rendering is asynchronous too so fallback cannot block the UI executor.

Suggested operations: CreateResource, UploadResource, SubmitDrawBatch, SubmitComputeBatch, Readback, Present, RetireResource, Cancel.

Map Simple operation tokens to GPU submission IDs and dependency values to timeline semaphore/fence values.

Mission rendering uses fixed frame/resource pools, no runtime shader compilation, no per-draw staging allocation, explicit GPU-required/fallback policy, last-valid-frame retention on admission failure, and single-lane publication.

## Immediate Correctness and Performance Fixes

P0:

- Replace blocking Future await with poll/Pending semantics.
- Ensure async scheduler never calls blocking await.
- Start all independent children before join/Future-all.
- Remove blocking driver operations/global mutex from production I/O path.
- Replace scheduler array slicing with O(1) indexed deque/ring.
- Prevent duplicate queue admission/execution.

P1:

- Prefer io_uring on supported Linux and record fallback reason.
- Remove per-operation hot-path allocation through registered resources/fixed slots.
- Make SQ-full explicit backpressure rather than implicit early submission.
- Replace synchronous sendfile-in-completion behavior.
- Generate fixed async frame offsets.
- Replace heap-heavy Future synchronization with profile-specific task frames.
- Replace embedded global scans with targeted wakeup.

P2:

- Add real delayed file/DB/network/GPU integration tests proving unrelated tasks continue.

## Profiling Architecture

Every task/operation carries TaskId, ParentTaskId, RingId, OperationToken, ProviderId, TraceId/SpanId, and profile fingerprint.

Trace events:

``` text
TaskSpawn
TaskReady
TaskRun
RingReserve
RingSubmit
ProviderStart
ProviderComplete
TaskWake
TaskResume
TaskComplete / TaskCancel
```

Use fixed per-core trace rings with no hot-path allocation.

Measure ring occupancy/high-water/full events/batches/kicks/latency; task frame size/polls/suspensions/wake latency; scheduler migrations/steals/idle/budget overruns; pool/arena high-water; web request latency/stalls; DB storage/WAL waits; UI input-to-present; GPU queue/device/readback latency; and NVMe HIL/FTL/FIL/NAND/CQ timing.

Profiling layers:

1. counters/histograms;
2. task/ring causal traces;
3. sampling and off-CPU profiling;
4. host causal profiling.

Performance gates should require zero steady-state hot-path allocation for server/mission critical paths, zero blocking calls on UI/I/O/firmware/mission executors, O(1) ring/task operations, no task-count scans after completion, negligible sync-leaf regression, native-provider parity targets, and before/after p50/p99/p99.9 evidence.

## Parallel Implementation Plan

### Phase 0 — Baseline and correctness

Benchmark current executor, drivers, web, DB, UI/render, and NVMe FW. Add blocking/allocation detectors and classify every async runtime path.

### Phase 1 — SimpleRing V1

Implement contracts, generation/token model, registered buffers, cancellation/reset, capability checks, software reference provider, and compatibility driver adapter.

### Phase 2 — Compiler async lowering

Implement expanded effects, implicit-await HIR, fixed MIR task frames, poll state machines, structured concurrency, cancellation cleanup, profile-specific frame placement, and interpreter/compiler/AOT parity.

### Phase 3 — Executors/providers

Implement UI, sharded server, compute, mission executors; io_uring provider; compatibility providers; timer/process/signal rings.

### Phase 4 — Embedded SimpleOS/SOSIX

Implement native ring mapping, per-core ready rings, IRQ-to-CQ path, ring-backed VFS/network/device/IPC/timer, POSIX blocking facade, and mission_pool runtime.

### Phase 5 — NVMe firmware

Add SimpleRing HIL adapter, internal rings, pool task frames, reset/cancellation generation, formal invariants, fault injection, host/RISC-V/QEMU/hardware evidence.

### Phase 6 — Web/DB servers

Migrate to per-core async runtimes, true async UDP/QUIC, async file/static paths, DB storage/WAL/network rings, structured request/transaction tasks, and overload/cancellation policies.

### Phase 7 — UI/browser/2D/render

Add immutable scene generations, RenderRing, CPU/GPU providers, timeline/fence mapping, async script integration, and explicit fallback policy.

### Phase 8 — Mission qualification and cleanup

Finalize mission_alloc/mission_pool, formal ring/pool proofs, evidence receipts, and delete/archive competing runtime paths.

## Final Architectural Rules

1. SimpleRing is the common asynchronous data-plane primitive.
2. SOSIX is the capability/policy/lifecycle control plane above it.
3. Preserve native queues as directly as security and portability allow.
4. Latency-bearing standard APIs are async by default.
5. Short local computation/state mutation remains synchronous.
6. Proven sync leaves pay no Future/scheduler/ring overhead.
7. Schedulers poll tasks; they never block awaiting them.
8. UI, connection, transaction, device, and renderer state have one owner.
9. Work stealing is limited to independent CPU computation.
10. No hidden blocking, allocation, queue growth, early flush, or provider fallback.
11. mission_alloc uses bounded admitted arenas.
12. mission_pool uses fixed pools/static task frames.
13. Both mission modes support bounded async, cancellation, deadlines, and device rings.
14. NVMe firmware migrates without rewriting proven FTL/recovery logic.
15. CPU and GPU rendering implement the same asynchronous RenderRing.
16. Every performance claim requires comparable before/after evidence.
