# Thread Enhancement Plan: Pool-Backed Spawn, Green Threads, and Scheduler-Aware Channels

<!-- codex-research -->

## Context

Simple's parallel benchmark (100 workers, LCG 100K iters, channel-based) shows:
- **Simple native: 12.9ms** — 100 OS threads + channel (mutex+condvar)
- **C pthreads: 10.1ms** — 100 OS threads
- **Go: 6.8ms** — goroutines (M:N) + channel (scheduler-integrated)

The gap is **thread spawn overhead**: 100 `pthread_create` calls (~100-200μs each = 10-20ms). Go runs 100 goroutines on ~16 OS threads via M:N scheduling. Same semantic, different runtime cost.

User constraints: memory-conscious (parallel agents crash tmux), pure Simple where possible, no over-engineering.

## Research Update

### Local Evidence

- Existing thread/channel surfaces are split across `src/lib/nogc_sync_mut/concurrent/thread.spl`, `src/lib/nogc_sync_mut/concurrent/channel.spl`, `src/lib/nogc_async_mut/concurrent/thread.spl`, and `src/app/io/thread.spl`; the plan must preserve `thread_spawn` semantics while adding a cheaper task-spawn facade.
- Runtime and interpreter work has prior concurrency evidence in `doc/01_research/runtime/execution/high_performance_concurrent_runtime.md`, including channel and thread extern wiring. Treat this as a compatibility constraint, not a clean-sheet runtime.
- Scheduler infrastructure already exists under `src/lib/nogc_async_mut/async_host/`, including `scheduler.spl`, `thread_safe_queue.spl`, `worker_thread.spl`, and task identity support. Reuse queue shapes and identity hooks before adding new scheduling concepts.
- Security research already requires future fiber runtimes to participate in unified task identity (`REQ-024` in `doc/02_requirements/infra/security_convention_first_architecture.md`). Green threads must register/restore task identity on park, unpark, and execution handoff.
- Existing parser/compiler tests include `spawn` and parallelism coverage; new tests should extend current thread/channel specs instead of creating isolated one-off demos.

### Domain Notes

- Go's own runtime describes the scheduler as distributing ready goroutines across worker threads, using G/M/P roles where an M needs a P to execute Go code, while an M may block in a syscall without a P. Source: https://go.dev/src/runtime/proc.go.
- Go explicitly avoids centralizing all scheduler state because per-P queues are a scalability requirement; Simple should follow the same direction only after Tier 0 proves the spawn overhead problem is real in current code. Source: https://go.dev/src/runtime/proc.go.
- Go preemption combines synchronous requests through stack guard state with asynchronous preemption only at safe points. Simple Tier 2 must therefore be compiler-backed and safe-point aware; a timer thread alone is not enough. Source: https://go.dev/src/runtime/preempt.go.
- `makecontext`/`swapcontext` are useful for a Tier 1 prototype, but POSIX.1-2008 removed them for portability reasons. Tier 1 should be explicitly Linux/macOS-hosted and should not become the long-term ABI. Source: https://man7.org/linux/man-pages/man3/makecontext.3.html.

## Requirement Deltas

- REQ-THR-001: Add a pool-backed task spawn API that reuses worker OS threads and leaves `thread_spawn` as the explicit OS-thread primitive.
- REQ-THR-002: Fix blocking and backpressure correctness before performance work; full channel buffers must block, return an error, or report backpressure, never silently drop.
- REQ-THR-003: Thread-pool idle waiting must use a blocking primitive, not millisecond sleep polling.
- REQ-THR-004: Green-thread identity must integrate with existing runtime task identity hooks before scheduler-aware channels are considered complete.
- REQ-THR-005: Tier 2 preemption requires compiler-emitted safe points or stack checks; do not simulate it only with external timer interrupts.
- REQ-THR-006: Simple exposes OS threads and green threads as distinct APIs: `thread_spawn` for OS threads and `green_spawn`/`green_run_*` for cooperative green threads.

## Non-Goals

- Do not replace `thread_spawn`; keep it as the direct OS-thread escape hatch.
- Do not make `ucontext` the permanent portable runtime ABI.
- Do not begin growable stacks until fixed-stack green threads have passed correctness, memory, and latency gates.

## Three Tiers

### Tier 0: Thread Pool (Quick Win — closes benchmark gap)

**Goal**: Reuse N OS threads for all tasks. Expected: 12.9ms → ~7-9ms.

**C Runtime** (`src/runtime/runtime_thread.c`):
1. Add `pthread_attr_setstacksize` — configurable stack (default 512KB vs current 2-8MB default)
2. Add `rt_pool_submit(closure_ptr) -> i64` — submit to pre-created worker pool
3. Fix: `runtime_native.c` channel `send()` silently drops when buffer full (line ~2581)
   - Status: native channel now grows beyond the old 1024-slot ring and is covered by `test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl` in native mode.

**Simple Stdlib**:
4. Fix `thread_pool.spl` — replace `thread_sleep(1)` poll loop with condvar-based blocking
5. New pool-backed task facade in `src/lib/nogc_sync_mut/concurrent/thread.spl` or equivalent:
   ```
   fn task_spawn(closure: () -> i64) -> TaskHandle   # pool-backed, not OS thread
   class TaskHandle: join() -> i64, is_done() -> bool
   ```
   - Default pool: auto-created on first `task_spawn()`, sized to `thread_available_parallelism()`
   - `thread_spawn` unchanged (always OS thread, backward compat)
   - `go` is reserved/parser-owned; lowering the language form to task spawn is a separate compiler lane.

**Codegen**: None needed.

### Tier 1: Stackful Green Threads + M:N Scheduler

**Goal**: 10K+ concurrent tasks, scheduler-aware channels. Go's GMP model.

**Current implemented seed** — `src/lib/nogc_async_mut/concurrent/green_thread.spl`:
1. Provides `GreenThreadHandle`, `green_spawn`, `green_run_one`, `green_run_all`, and `green_ready_count`.
2. Runs green-thread closures cooperatively to completion on the current OS thread.
3. Separates the green-thread API from OS-thread `thread_spawn`; stack switching, parking, scheduler-aware channels, and preemption remain Tier 1/Tier 2 follow-up work.

**C Runtime** — new `src/runtime/runtime_green.c`:
1. **Slab stack allocator**: One `mmap` per slab (8MB = 1024×8KB stacks), guard page per slab boundary. Live-G cap (default 100K) with backpressure.
2. **Context switch via ucontext** (Tier 1) — `makecontext`/`swapcontext`, ~1μs/switch. Prototype only; POSIX removed this API for portability reasons, so the long-term path is custom per-arch switching.
3. **Green thread descriptor**: `{ sp, stack_base, stack_size, state, entry_fn, closure_ptr, result, next }`
4. **Exported primitives**: `rt_green_spawn`, `rt_green_yield`, `rt_green_park`, `rt_green_unpark`

**Simple Stdlib** — new `src/lib/nogc_async_mut/green_scheduler.spl`:
5. **GMP scheduler in Simple** — reuse `WorkStealingQueue` data structures from `async_host/scheduler.spl` (not its stackless dispatch logic):
   - P (Processor): local LIFO queue (256 slots) + runnext
   - M (Worker): OS thread bound to P, runs worker loop
   - Global queue: `ThreadSafeQueue` (existing), checked every 61 ticks for fairness
   - Work-stealing: random P order, 4 attempts
6. **Scheduler-aware channel** (`green_channel.spl`): `recv()` calls `rt_green_park()`, `send()` calls `rt_green_unpark()`. Never touches condvar — all blocking is scheduler-mediated.
7. Upgrade `task_spawn()` and the compiler-owned `go` form → green thread spawn (same semantics, different backend)

**Codegen**: None — cooperative scheduling at explicit points (channel ops, yield).

**Memory**: 100 green threads × 8KB = 800KB vs 100 OS threads × 8MB = 800MB (**1000× improvement**).

### Tier 2: Compiler-Inserted Preemption + Growable Stacks

**Goal**: Full Go parity. Preemptible tight loops, 2KB initial stacks.

**C Runtime** (`runtime_green.c`):
1. Custom asm context switch (x86_64: ~15 insns, arm64: ~20) — ~50ns vs 1μs ucontext
2. Growable stacks: 2KB initial → copy+grow on overflow (requires stack maps from compiler)
3. Sysmonitor thread: 10ms preemption check, deadlock detection

**Compiler** (`src/compiler/70.backend/`):
4. Stack-check prologue in Cranelift 0.116 codegen: `if SP < stack_limit: call rt_green_morestack()`
5. Stack map generation (which slots are pointers) for stack copying
6. Preemption flag check at function prologues + loop back-edges

**Stdlib**:
7. Netpoller integration (epoll/kqueue) — park G on I/O, unpark on readiness
8. `select` on multiple channels (future)

## Go Runtime Reference (Key Design Decisions)

| Go Detail | Simple Equivalent |
|-----------|-------------------|
| G: 2KB initial stack, growable | Tier 1: 8KB fixed. Tier 2: 2KB growable |
| M: OS thread with g0 scheduling stack | M: OS thread, worker loop in Simple |
| P: 256-slot lock-free local runq + runnext | P: 256-slot queue, mutex initially, lock-free later |
| `gopark`/`goready`: suspend/resume G | `rt_green_park`/`rt_green_unpark` |
| Channel send → direct stack-to-stack copy | Tier 1: buffer copy. Tier 2: direct handoff |
| Syscall handoff: M detaches P | Tier 1: document "don't block OS". Tier 2: P-handoff |
| stackguard0 preemption in prologue | Tier 2: stack-check doubles as preemption check |
| Work-stealing: 4 attempts, random P | Same, implemented in Simple |

## Existing Infrastructure to Reuse

| What | Where | Reuse |
|------|-------|-------|
| Work-stealing queue shape | `async_host/scheduler.spl` | Data structures, not dispatch |
| Thread-safe MPMC queue | `thread_safe_queue.spl` | Global run queue |
| Atomic CAS intrinsics | `atomic.spl` | Lock-free queues (future) |
| Fiber task ID tracking | `fiber_identity.rs` | Green thread identity |
| Thread pool submit | `thread_pool.spl` | Tier 0 base |
| Closure ABI: fn_ptr(closure_ptr) | `runtime_thread.c:212-214` | Green thread entry |

## Spawn-Agent Work Plan

Spawn these as separate lanes only after recording the baseline benchmark output and current failing/passing thread specs. Each agent owns its lane files and must not edit another lane's files without an explicit handoff note.

### Agent A: Runtime Thread Pool and Channel Correctness

**Scope**: `src/runtime/runtime_thread.c`, native channel send/recv helpers, C runtime headers, runtime thread tests.

**Tasks**:
1. Confirm the current channel full-buffer behavior in runtime code and add a regression test before changing it.
2. Add configurable pthread stack size with conservative defaults and environment/runtime override.
3. Add `rt_pool_submit` and pool lifecycle primitives without changing `thread_spawn`.
4. Replace spin/sleep waits in pool workers with condition-variable or semaphore wakeups.

**Gate**: existing thread/channel tests pass; benchmark shows pool-backed 100-task spawn below the baseline OS-thread result.

### Agent B: Simple Stdlib Spawn Facade

**Scope**: `src/lib/nogc_sync_mut/concurrent/`, `src/lib/nogc_async_mut/concurrent/`, public module exports, examples.

**Tasks**:
1. Add `task_spawn(closure: () -> i64) -> TaskHandle` backed by the runtime pool.
2. Implement `TaskHandle.join()`, `TaskHandle.is_done()`, and error propagation consistent with existing Simple conventions.
3. Keep `thread_spawn` documented and tested as the explicit OS-thread API.
4. Add compatibility examples for CPU work, channel fan-in, and bounded task count.
5. Do not define `fn go`; `go` is a reserved language form and must be lowered by the compiler lane if exposed as public syntax.

**Gate**: no public API ambiguity between `go` and `thread_spawn`; docs and examples compile in interpreter and native modes where supported.

### Agent C: Green Scheduler Prototype

**Scope**: new `src/runtime/runtime_green.c`, `src/lib/nogc_async_mut/green_scheduler.spl`, scheduler identity bridge.

**Tasks**:
1. Build fixed-size stack slabs with live-G caps and backpressure.
2. Implement cooperative `rt_green_spawn`, `rt_green_yield`, `rt_green_park`, and `rt_green_unpark`.
3. Reuse `async_host` queue structures where possible and preserve task identity on every transition.
4. Add scheduler-aware channel prototype only after park/unpark correctness is verified.

**Gate**: 10K green tasks complete with bounded RSS, deterministic result collection, and no task identity leaks.

### Agent D: Compiler and Preemption Research Spike

**Scope**: `src/compiler/70.backend/`, stack metadata docs, architecture notes.

**Tasks**:
1. Identify where function prologue and loop back-edge checks can be emitted for current native backends.
2. Define the minimum stack/safe-point metadata needed for future growable stacks.
3. Produce a small design note before implementation; Tier 2 is blocked without this.

**Gate**: design identifies exact compiler insertion points and verification strategy; no production code required in the first spike.

### Agent E: Verification and Perf Harness

**Scope**: `test/`, `scripts/check/check-cross-language-perf.shs`, benchmark docs/evidence.

**Tasks**:
1. Capture baseline Simple/C/Go benchmark output before each tier.
2. Add no-placeholder SPipe specs for channel backpressure, pool-backed `go`, task identity, and green-task fan-in.
3. Track warm startup, representative task latency, throughput, and max RSS.
4. Keep `find doc/06_spec -name '*_spec.spl' | wc -l` at `0`.

**Gate**: each tier has correctness tests plus before/after performance evidence.

## Implementation Sequence

```
Phase 1 — Tier 0 (1-2 weeks)
  ├─ Capture baseline benchmark and current thread/channel test status
  ├─ Fix channel send drop bug
  ├─ Add stack size config to pthread_create
  ├─ Fix thread_pool.spl sleep polling → condvar
  ├─ Implement task_spawn() as pool submission
  └─ Benchmark: target <9ms

Phase 2 — Tier 1 (4-6 weeks)
  ├─ runtime_green.c: slab allocator + ucontext
  ├─ green_scheduler.spl: GMP scheduler in Simple
  ├─ green_channel.spl: park/unpark channel
  ├─ Upgrade go() → green thread
  └─ Benchmark: 10K tasks, channel throughput

Phase 3 — Tier 2 (8-12 weeks)
  ├─ Custom asm context switch (x86_64, arm64)
  ├─ Cranelift 0.116 stack-check prologue
  ├─ Growable stacks + stack maps
  ├─ Cooperative preemption at prologues
  └─ Benchmark: Go parity on diverse workloads
```

## Risks

1. **Tier 1: OS-blocking calls stall P** — green threads must only block on scheduler-aware primitives. Document clearly.
2. **Tier 2: Stack copy pointer fixup** — complex, Go spent years on this. Alternative: segmented stacks (no fixup, but "hot split" problem).
3. **Tier 2: Cranelift 0.116 stack_limit support** — may need manual IR emission if not exposed.
4. **Tier 1 portability** — `ucontext` is good enough for a hosted prototype but is not a portable long-term ABI.
5. **Memory: ucontext mmap per slab** — slab approach avoids VMA exhaustion (64 slabs vs 100K individual mmaps).
6. **Agent overlap** — runtime, stdlib, and tests touch shared concurrency semantics. Each spawned agent must record owned files and handoff notes before crossing lanes.

## Verification

- **Tier 0**: Run `sh scripts/check/check-cross-language-perf.shs` — Simple parallel should drop to <9ms
- **Native channel overflow**: `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl --mode=native --clean --force-rebuild --sequential --timeout 120`
- **Tier 1**: Spawn 10K green threads each sending to a channel, verify all results collected, measure total time
- **Tier 2**: Run tight LCG loop in green thread, verify it yields within 10ms (preemption works)
- All tiers: `bin/simple test` on thread/channel specs pass, LCG total = 107461963222 (matches C/Go)
- Release-blocking doc layout check: `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`

## Post-Plan: VCS

After exiting plan mode: `jj commit -m "..."`, fetch, rebase, push the benchmark changes from earlier.
