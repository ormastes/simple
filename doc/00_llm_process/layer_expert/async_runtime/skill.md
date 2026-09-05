# Async runtime layer expert

## Role

Own the MDSOC layer boundary for the SimpleRing/task/profile V1 async runtime
foundation. Common contracts are shared tree nodes; hosted storage, legacy
Future APIs, profile policy, compiler seams, and native providers remain
separate sibling projections.

## Layer ownership

| Layer | Owns | Must not own |
|---|---|---|
| `src/lib/common/contracts/execution` | Versioned ring/task/profile values, enums, validation, canonical fingerprints | Slots, schedulers, OS descriptors, compiler lowering, allocation policy implementation |
| `src/lib/nogc_async_mut/async_ring` | Fixed-capacity ring slots/index queues, lifecycle transitions, generation checks, telemetry | A second Future/task ABI, executor policy, native descriptors |
| `src/lib/nogc_async_mut/async` and `async_host` | Existing Future, promise, poll, executor, timer, and host compatibility behavior | Redefining V1 tokens/completions or silently claiming adapter parity |
| `src/lib/nogc_async_mut/concurrent` and `thread_pool.spl` | OS-thread, cooperative-green, multicore-green, and lower-level task facades | SimpleRing ownership or canonical V1 profile semantics |
| `src/lib/nogc_async_mut_noalloc/async` | Fixed-capacity trace storage and existing no-GC async primitives | Claiming hosted arrays are link-time-static storage or a migrated mission executor |
| `src/compiler/**` | Effect diagnostics and future frame/lowering extension points | Ring mutation, provider calls, task scheduling, implicit-await claims without gates |
| `src/os/async`, `src/os/sosix`, `src/os/drivers` | Native provider translation, capability checks, device completion ingress | New common contract or platform-specific Future ABI |

## Public-to-next-layer rule

Consumers import only the common records (`RingToken`, `RingCompletion`,
`AsyncTaskFrame`, `TaskContext`, `TaskPollResult`, and profile values). A hosted
ring or provider may expose an adapter facade, but sibling layers must not read
its private slots, queue cursors, frame layout, or scheduler state. Native
providers translate at the provider edge and never leak descriptors into the
common contract.

## Load-bearing invariants

- `SimpleRing<Op, Cpl>` is fixed-capacity and one-mutable-owner by default.
- Reserve/commit is the provider visibility boundary; release before commit is
  never provider-visible.
- Ring/slot/generation identity rejects stale, cross-ring, and reused tokens.
- Every admitted single-shot operation has exactly one terminal completion;
  completion carries the exact task key and does not scan Futures.
- `poll(frame, context)` is nonblocking and returns `Ready` or `Pending(token)`.
- Blocking, fallback, allocation, work stealing, detachment, and determinism
  are profile facts that must fail closed when incompatible.
- `AsyncProfile` is configuration/validation/fingerprint data. `implicit` is a
  policy field, not proof of compiler implicit-await support; mission presets do
  not create static storage.

## Existing API boundary

`Future`/`HostFuture` keep their own state, poll, waker, and chaining contracts.
`cooperative_green_spawn` is a current-OS-thread cooperative queue;
`multicore_green_spawn` and `task_spawn` are pool-backed task facades; and
`thread_spawn` is an OS-thread API. None is a V1 executor merely because it
can be wrapped by a future adapter. Compatibility work must report the legacy
surface, mapping/fallback grade, blocking behavior, ownership transfer, and
completion semantics.

## Tests and evidence

Use the focused specs:

- `test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl`
- `test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl`
- `test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl`

Additional focused specs cover the software provider, hosted mission admission,
fixed-capacity trace ring, concurrency interleavings, and the five-step system
scenario. They still do not prove native `io_uring`, compiler lowering,
executor migration, link-time-static mission storage, or admitted performance.

## Blockers and migration sequence

The current gap list is: native ready ingress and providers; link-time-static
mission storage/executor integration; compiler task-frame lowering; admitted
pure-Simple performance/RSS/allocation evidence; and formal bounded-concurrency
proofs.
Existing `src/runtime/platform/async_linux_uring.c` is not a V1 conformance
provider by path alone.

Migrate in this order: freeze common contracts; prove a bounded software
provider; add no-GC mission adapters; add explicit Future/green/thread
compatibility adapters; add one native provider at a time; then gate compiler
lowering and retire legacy executors only after parity, boundedness, stale-token,
exact-wake, and cancellation evidence.

## Update rule

Update this page whenever a layer owner, public facade, invariant, focused test,
or migration gate changes. Do not promote proposal text to current-state
evidence without an executable owner and test.
