# Build runner fiber scheduler v1 — mmap writer, per-file pipeline fibers, async IO, memory admission

Status: design (2026-10-24). Tracker items 27–30. Companion to
`src_based_tldr_build_v1.md` (per-file jobs, single-flight, no locks) and
`packed_binary_ast_v1.md` (pointer-free mmap-in-place AST blob).

User rules inherited: no locks, fully async, temp+rename publication,
single-flight futures, per-file jobs, cache limits (#4378/#4381).

## 1. Survey (origin/release/1.0.0)

| Need | Exists | Reusable? |
|------|--------|-----------|
| mmap READ | `rt_mmap(path,size,off,readonly)` (`runtime_native.c`), `rt_file_mmap_read_*`, `rt_munmap/rt_msync`; zero-copy blob view `src/lib/nogc_async_mut/sosix/packed_blob_view.spl` (#4397) | yes |
| mmap WRITE | `rt_mmap(..., readonly=0)` maps RW but opens `OPEN_EXISTING` / `O_RDWR` without `O_CREAT`/size-set | **missing**: create + set length |
| Stackful fiber | only `fiber_identity.rs` (`rt_fiber_enter/exit/current_task_id`, "for future stackful fiber runtimes") | **missing** — no context switch primitive anywhere |
| Stackless coroutine | `nogc_async_mut/coroutine.spl` (manual enum state + step fn) | yes, pattern |
| Green threads | `concurrent/green_thread.spl`: one OS thread, FIFO of `fn() -> i64` closures, run-to-completion, no yield | queue shape only |
| Multicore pool | `concurrent/multicore_green.spl` → `rt_pool_*` (`runtime_pool.c`): **global mutex** (`g_pool_lock`, CRITICAL_SECTION) | violates "no global lock"; keep only as worker-thread launcher |
| Work stealing | `async_host/scheduler.spl` `WorkStealingQueue` + `HostScheduler` (Future/Poll/Waker) | Poll/Waker model reusable; queue is not per-socket/lock-free |
| Async file IO | `src/runtime/platform/async_driver.c` → IOCP (`async_windows.c`, ReadFile OVERLAPPED) and io_uring (`async_linux_uring.c` `io_uring_prep_read`); `rt_iocp_*` externs; `async_ring/` software provider | yes, completion source |
| CPU topology / affinity | none (`rt_cpu_count` only; no NUMA/socket query, no thread affinity) | **missing** |
| Memory limits | `80.driver/cache/metadata/cache_limits.spl`, `cache/gc/cache_eviction_plan_v1.spl` | yes, budget source |
| Build runner | `src/app/buildrunner/runner.spl`, `src/lib/common/task_runner/{scheduler,journal}.spl` — task ids/journal, no per-file future | host for the scheduler |

Conclusion: there is no stackful fiber. Everything that suspends today is a
stackless state machine (Future/Poll or coroutine step fn).

## 2. Fiber model decision

**v1 = stackless pipeline fiber**, not a stack-switching fiber.

A `FileFiber` is a state machine owning one source file end to end:

```
Start → AwaitSource → Parse → AwaitDeps(TLDR/packed AST) → Hir → Mir → Obj → Publish → Done
```

- Each `step()` runs one CPU stage to completion and returns `Poll`:
  `Ready`, `Yield` (more CPU work, requeue), or `Pending(io_token)`
  (parked until an IO completion or a single-flight future fires).
- Yield points are stage boundaries and every file/TLDR/AST read. Stages are
  not preempted mid-way; per-file stages are small enough for this.
- Reason: a stack switch (CreateFiber/SwitchToFiber, ucontext/asm) would be a
  new C/asm boundary, is unrunnable under the seed interpreter (interpreted
  frames live on the host stack), and costs a stack (≥64 KiB) per fiber at
  10k+ files. The state machine runs identically on seed, interpreter and
  native. A stackful backend can later plug in behind the same `step()`
  contract; `rt_fiber_enter_task_id` is already the identity hook for it.

## 3. Scheduler

- **Workers:** one OS thread per logical CPU, grouped by socket
  (2 × 40 on this host). Topology from a new `rt_cpu_topology()`
  (Windows `GetLogicalProcessorInformationEx`, Linux `/sys/devices/system/cpu`),
  affinity via `rt_thread_set_affinity` (C boundary with Simple twin per
  `pure_simple_hal.md`). Fallback: 1 socket, `rt_cpu_count()` workers.
  **Windows processor groups:** 80 logical CPUs > 64, so a process is confined
  to one group unless threads are assigned explicitly. Topology enumerates
  groups via `GetLogicalProcessorInformationEx(RelationAll)` and each worker is
  placed with `SetThreadGroupAffinity(group, mask)`. Linux uses
  `sched_setaffinity` plus NUMA node ids. Both sit behind a platform-neutral
  std layer aligned with the portability design (in progress separately).
- **Run queues:** per-worker Chase–Lev deque (owner push/pop bottom,
  thieves CAS top). Steal order: same-socket victims first; cross-socket only
  when the whole socket is idle. No global lock; the injector for new files is a
  per-socket MPSC ring fed by the runner.
- **Socket pinning:** a fiber's whole chain stays on the socket that started it
  (TLDR doc §"pins a job's whole chain"); stealing a fiber moves it only within
  the socket.
- **IO:** a worker submits the read (IOCP / io_uring / sync fallback via
  `async_driver.c`), records `io_token → fiber` in its own table, and runs the
  next fiber. Each worker polls its completion port non-blocking between steps
  and blocks on it only when its deque is empty and stealing fails. Completions
  push the fiber back onto the owning worker's deque.
- **Single-flight:** waiting on another module's TLDR/AST future parks the
  fiber in that future's waiter list (lock-free Treiber stack); the producer
  drains it on publish.

## 4. Memory admission (backpressure)

- Budget = cache-limits config (`cache_limits.spl`) build-memory cap, default
  a fraction of physical RAM.
- Each fiber carries an estimate `est = k_src·source_bytes + per-stage peak`
  (coefficients from the perf journal; conservative constants until measured).
- Admission: an atomic `reserved` counter; the runner admits a new file fiber
  only if `reserved + est ≤ budget` (CAS loop, no lock). Otherwise files stay
  in the not-yet-started list; running fibers always finish (no deadlock,
  since a parked fiber only waits on fibers already admitted or on IO).
- Stage-accurate release: after `Obj` publish the fiber releases its whole
  reservation; packed AST views are mmapped and count only their resident
  share.
- Saturation targets: CPU — keep every deque non-empty while budget allows;
  IO — cap in-flight reads per socket (queue depth, default 64).

## 5. mmap writer (item 27)

New `rt_mmap_create(path, size) -> MapHandle`: create `path.tmp.<pid>.<n>`,
set length (`SetFilePointerEx+SetEndOfFile` / `ftruncate`), map RW shared.
Simple API `MappedWriter`: `create(final_path, size)`, `bytes_at(off)` fill,
`finish()` = flush (`FlushViewOfFile`/`msync`) → unmap → close → atomic rename
to `final_path` (the existing temp+rename rule). `abort()` unmaps and deletes.
Object emission: when the backend reports the final size up front (packed AST,
SMF, our own object writer) write through `MappedWriter`; when it streams
(LLVM/external tool), it writes to the temp path and we rename — mapping that
is no gain.

## 6. Delivery (one PR each, to release/1.0.0)

1. mmap writer (`rt_mmap_create` C + Rust runtime, `MappedWriter`, spec).
2. Scheduler core: `FileFiber` step contract, per-worker deques, memory
   admission — first in pure Simple on one thread (spec-runnable on seed), then
   worker threads + topology/affinity.
3. Async file read integration (`async_driver` completion → requeue).
4. Per-file pipeline fiber. **Decided 2026-10-24:** this IS the per-file job
   scheduler; the TLDR plan's PR 4 is folded in. `FileFiber` consumes the TLDR
   lane's SourceReader / CacheReader / lazy TLDR table / link receipts.

Pre-req if needed: cross-thread CAS atomics (`rt_atomic_*`, C + Rust twins) as
their own small PR. Correctness rule: every PR ships specs, and memory
admission must never deadlock.

## 7. Open points

- Lock-free deque needs `rt_atomic_cas_i64`/fences visible to Simple; confirm
  `src/lib/nogc_async_mut/atomic.spl` covers CAS on shared memory under native.
- Per-stage memory coefficients are unmeasured.
- Stackful backend deferred; revisit only if stage-granular yield proves too
  coarse.
