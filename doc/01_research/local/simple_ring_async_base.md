<!-- codex-research -->

# Local Research — Simple Ring and Async Base

Date: 2026-08-26
Parent synthesis: `doc/01_research/runtime/simple_ring_first_async_first_architecture_2026-08-26.md`

## Finding

Simple has enough strong pieces to build one ring/task foundation, but they are split across incompatible ownership and polling models. The new base should reuse their proven invariants without promoting any existing runtime to the universal ABI.

## Compiler findings

- `src/compiler/10.frontend/desugar/desugar_async.spl` owns async desugaring, but explicit `await` currently lowers through `block_on`; generated state-machine helpers and the library Future API do not converge.
- `suspension_analysis.spl`, `state_enum.spl`, `poll_generator.spl`, `frame_analysis.spl`, `frame_verify.spl`, `spawn_analysis.spl`, and `reservation_analysis.spl` provide reusable suspension/frame/bound analysis.
- `src/compiler/20.hir/hir_lowering/async.spl` recognizes Future/Poll shapes but does not define a task-frame ABI.
- MIR represents await/yield/spawn/send/receive, while `src/compiler/90.tools/async_integration.spl` still has a stub state-machine bridge and the interpreter uses direct runtime await/yield calls.
- Effect propagation in `src/compiler/00.common/effects.spl` is explicitly not wired. Compiler implicit-await/effect lowering must therefore remain a follow-on lane, not a V1 library claim.

## Runtime fragmentation

- `src/lib/nogc_async_mut/async/` defines Future, Task, Executor, Runtime, Poll, cancellation, and combinators, but contains multiple Task/TaskContext models and hosted dynamic queues.
- `src/lib/nogc_async_mut/async_host/` defines another HostFuture/scheduler/waker model.
- `src/lib/nogc_async_mut/async_embedded.spl` and `src/lib/nogc_async_mut_noalloc/async/` provide fixed-capacity concepts, but current storage is constructed with heap arrays and task polling is incomplete.
- `src/os/async/` defines OsFuture/OsPoll/OsWaker/OsExecutor plus an MMIO SPSC ring. OsPoll lacks a wait token and OsWaker contains an unfinished wake path.
- `src/compiler_rust/runtime/src/async_runtime.rs` calls blocking future-await and uses dynamic queues; it is compatibility/bootstrap behavior, not the mission task ABI.

## Reusable queue and lifecycle invariants

- `src/os/sosix/core/operation.spl`, `completion.spl`, `completion_queue.spl`, and `wait_set.spl` already demonstrate generation validation, exactly-once terminal state, bounded completion publication, targeted readiness, and stale-watch rejection.
- `src/os/sosix/fs/async_transport_state.spl` and `completion_pump.spl` add slot+generation+token authentication, monotonic progress, endpoint validation, and stale/duplicate rejection.
- `src/os/kernel/ipc/process_queue.spl` is a strong bounded FIFO and generation-handle precedent.
- `src/lib/nogc_async_mut_noalloc/collections/ring_buffer.spl` shows fixed-at-construction ring storage, but uses sentinel errors and no generation.
- `src/lib/nogc_async_mut/io/packet_ring.spl` has bounded/batch vocabulary, but its current push/pop path does not preserve the supplied descriptor and cannot be the base.
- `src/os/drivers/nvme/nvme_queue.spl` supplies real hardware SQ/CQ and phase behavior but lacks generic reserve/commit, generation safety, and task wake semantics.

SOSIX remains the control plane above the common ring. Placing `SimpleRing` inside SOSIX would invert the selected boundary and prevent host/server/render consumers from sharing a platform-neutral data-plane contract.

## Profiles and mission reuse

- `src/compiler/00.common/assurance/policy_schema.spl` provides canonical policy serialization/hashing, but no async execution profile exists.
- `src/lib/nogc_sync_mut/mission_critical/domain_arena_v1.spl` is the strongest `mission_alloc` foundation: sealed arenas, typed exhaustion, high-water telemetry, and commit/rollback.
- `src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl` and fixed collections supply bounded building blocks, with an explicit language gap for true inline `[T; N]` storage.
- Compiler spawn/reservation/frame analyses can later validate an `AsyncProfile`; they should not own runtime ring state.

## Selected ownership

1. `src/lib/common/contracts/execution/`: versioned platform-neutral ring/task/profile value contracts.
2. `src/lib/nogc_async_mut/async_ring/`: bounded hosted ring and pure-Simple software reference provider.
3. `src/lib/nogc_async_mut_noalloc/async/`: follow-on mission/static storage and executor adapters consuming the same contracts.
4. `src/compiler/`: effects, suspension eligibility, typed frame generation, and lowering only.
5. `src/os/async`, SOSIX, drivers, render/server/DB/NVMe owners: provider/policy adapters retaining domain-private state.

## Existing evidence worth retaining

Reusable tests include SOSIX async transport/completion/wait-set/sync-wait specs, process-queue generation tests, noalloc scheduler/Ravenscar tests, async primitives/cancellation tests, owner-thread ready-queue tests, NVMe queue boundary tests, and log-ring capacity/overflow tests. Existing system async specs with `check(true)`, skips, declaration-only checks, or inline fake Futures are not production acceptance evidence for the new base.
