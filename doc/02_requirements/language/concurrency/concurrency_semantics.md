# Simple Language — Concurrency Semantics Decision Document

**Date:** 2026-06-11
**Status:** PROPOSED (all decisions)
**Source:** Closes spec holes identified in `/tmp/async_audit/05_web_research.md` (38-item checklist; 20 UNCOVERED, 13 PARTIAL).
**Relation to existing requirements:** Cross-references REQ-MCG-001..010 in
`doc/02_requirements/feature/multicore_green.md`. This document adds REQ-CONC-001..025
for items that are new or need pinning. It does NOT duplicate covered items.

---

## Existing Model Summary

Simple's concurrency model (from design docs and `src/lib/nogc_async_mut/concurrent/mod.spl`):

- **Share-nothing green processes** — no shared mutable variables; sharing only via
  channels/messages or sealed sosix datasets.
- **Cooperative green queue** — `cooperative_green_spawn` runs tasks on the current
  carrier thread, yielding only at explicit `await`/`yield` suspension points
  (deterministic, single-carrier).
- **Bounded green_channel with explicit backpressure** — sender never blocks the
  carrier; returns `SendResult` (success/full/closed).
- **Multicore green runtime pool** — `multicore_green_spawn` uses an OS thread pool;
  `MulticoreGreenHandle.used_runtime_pool()` is the evidence gate (REQ-MCG-003).
- **Actors with message passing** — `actor_spawn`; isolated computation, mailbox MPSC/MPMC.
- **Erlang-style copy semantics for messages** — values copied on send in `nogc_async_mut`.

---

## Group 1: Scheduling / Fairness

### REQ-CONC-001 — Work-stealing fairness guarantee (S-3)

**Question:** Is there a starvation-freedom guarantee for the multicore green scheduler?

**Decision (PROPOSED):** The multicore green runtime pool **does not guarantee
starvation freedom today**. Work-stealing deques are the planned dispatch
mechanism, but no preemption or yield-insertion is specified. A CPU-bound task
that never suspends can monopolize its worker thread for an unbounded duration.
This gap is tracked under REQ-MCG-008. Callers relying on fairness must insert
explicit `green_yield()` calls in tight loops.

**Rationale:** Go 1.14 added asynchronous preemption to close exactly this gap;
before that goroutines could monopolize a P. Erlang uses cooperative reduction
budgets (2000 reductions) to enforce turn-taking without OS preemption.
Simple's current cooperative model matches pre-1.14 Go: safe and predictable,
but not starvation-free. Claiming starvation freedom would require
compiler-inserted yield points or OS signal preemption — neither is implemented.

**Test evidence:** A spec spawning N CPU-bound tasks on a pool of size M < N and
asserting all complete within `T` ms would fail today; when the scheduler
implements yield insertion, this becomes the acceptance gate.

---

### REQ-CONC-002 — Blocking I/O inside a green task (S-4)

**Question:** If a green task calls a blocking syscall (e.g., `file.read_sync`),
does it block the entire carrier thread?

**Decision (PROPOSED):** In `cooperative_green_spawn` mode: **yes, a blocking
syscall blocks the carrier thread** and starves all other tasks queued on that
carrier. In `multicore_green_spawn` mode: a blocking call blocks one runtime-pool
thread; other pool threads continue running other tasks. There is **no automatic
thread-expansion** (no equivalent to Go's `entersyscall`/`exitsyscall` M-thread
inflation). Users should use async I/O wrappers from `std.concurrent.io` inside
green tasks; using sync wrappers is permitted but documented as a latency hazard.

**Rationale:** Go releases the P slot on blocking syscalls and inflates M-thread
count. Erlang uses "dirty schedulers" for long FFI. Both approaches add scheduler
complexity. Simple adopts the simpler Kotlin model: cooperative suspension — if
you block, you block that thread. For `multicore_green` the pool absorbs the hit;
for `cooperative_green` the single carrier stalls. This is predictable and avoids
hidden thread proliferation.

**Test evidence:** Spawn a `cooperative_green` task that calls `thread_sleep(100ms)`
(a blocking call); assert a second task on the same carrier does NOT run during
those 100ms. Spawn the same pattern on `multicore_green` with pool size ≥ 2;
assert the second task completes before the first wakes.

---

### REQ-CONC-003 — Task priority / scheduling order (S-5)

**Question:** Does spawn order imply execution order? Is FIFO guaranteed?

**Decision (PROPOSED):** `cooperative_green_spawn` is **FIFO within a single
carrier** — tasks are enqueued and dequeued in spawn order, yielding only at
suspension points. `multicore_green_spawn` offers **no ordering guarantee** across
workers: work-stealing breaks FIFO across the pool. There are no task priorities
in either mode. Ordering-sensitive code must use explicit channel synchronization
rather than relying on spawn order.

**Rationale:** Go has no FIFO guarantee across goroutines. Erlang has no ordering
between processes. Kotlin coroutines within a single-threaded dispatcher are FIFO
by convention (not spec). For `cooperative_green`, FIFO is a natural consequence
of a single carrier + queue; for `multicore_green`, FIFO would require global
locking that defeats work-stealing.

**Test evidence:** Spawn 5 `cooperative_green` tasks that each record their start
index; assert start indices arrive in spawn order. Repeat on `multicore_green`;
assert only that all 5 complete, not in any particular order.

---

## Group 2: Cancellation

### REQ-CONC-004 — Non-cooperative task cannot be force-killed (C-2)

**Question:** What happens when `cancel()` is called on a task that never checks
a cancellation token or reaches a suspension point?

**Decision (PROPOSED):** There is **no force-kill of green tasks**. Cancellation
is purely cooperative. A task that ignores its `CancellationToken` and never
suspends will run to completion regardless of cancel requests. The only
process-level kill primitive is an OS-process `exit()`, which terminates the
entire process. Supervisor trees that need guaranteed termination must design
tasks to poll their token at regular suspension points.

**Rationale:** Erlang `exit(Pid, kill)` is the only forced kill; it bypasses trap_exit.
Kotlin `Job.cancel()` is cooperative; `runBlocking` + join is needed to await
actual termination. Rust's tokio has no force-abort for async tasks (only `abort()`
which drops the future at the next `.await`). Simple aligns with Kotlin and Rust:
cooperative cancellation, no force-kill. This prevents mid-operation corruption
and simplifies cleanup semantics.

**Test evidence:** Spawn a task containing an infinite loop with no `await` or
token check; call `cancel()` on its handle; assert the task is still running after
100ms; assert the calling task is not blocked.

---

### REQ-CONC-005 — Cancel-safety: partial work on cancellation (C-3)

**Question:** If a task is cancelled mid-operation (e.g., partial channel write
or partial I/O read), what is the observable state?

**Decision (PROPOSED):** Cancellation is delivered **only at suspension points**
(`await`/`yield`). A suspension point is atomic with respect to cancellation:
either the operation completes before suspension ends, or the suspension raises
a `CancellationError` before the operation begins. Partial channel writes do not
occur because `channel.send()` is either fully committed before the next
suspension or not started. Partial I/O reads may leave bytes consumed from the
underlying stream; callers must treat a cancelled read as data-loss at that
position. Channel operations are cancel-safe; stream I/O is not.

**Rationale:** Rust/tokio documents cancel-safety per method (e.g., `read_u32`
is not cancel-safe). Kotlin documents which `suspend fun` are cancel-safe.
Simple adopts the same principle: channel primitives are cancel-safe by
construction (atomic enqueue/dequeue); stream I/O is explicitly not.

**Test evidence:** Send to a bounded channel from a task that is concurrently
cancelled; verify the channel contains either 0 or 1 message, never a partial
value. Read from a stream in a cancellable task; verify the stream position is
either unchanged or advanced by a full read unit, never a partial byte count.

---

### REQ-CONC-006 — Cancellation unblocks channel recv (C-6)

**Question:** If a task is blocked on `channel.recv()` and its cancellation token
fires, does it unblock?

**Decision (PROPOSED):** Yes. `channel.recv()` is a suspension point. When the
task's token is cancelled while blocked on `recv()`, the task receives a
`CancellationError` (or equivalent typed error) and unblocks immediately. The
message that would have been received is NOT consumed — it remains in the channel
for another receiver. This prevents goroutine-leak patterns analogous to
Go's channel-recv goroutine leak.

**Rationale:** Kotlin's `receive()` throws `CancellationException` when the
coroutine is cancelled. Go has no built-in mechanism; idiomatic Go uses `select`
with `ctx.Done()`. Simple adopts the Kotlin approach: the runtime injects a
wakeup on the suspended recv waiter, raising `CancellationError`.

**Test evidence:** Spawn a task that calls `recv()` on an empty channel; cancel
the task; assert the task's join returns `Err(CancellationError)`; assert the
channel is still empty (no phantom message consumed).

---

## Group 3: Error Propagation

### REQ-CONC-007 — Unhandled error in an unsupervised task (E-1)

**Question:** What happens when a task panics or returns an error and its handle
is never joined?

**Decision (PROPOSED):** An unhandled error in a green task is **captured and
stored in the task handle**. It does not propagate to the spawning task, does not
crash the process, and is not silently swallowed. When the handle is eventually
joined (`handle.join()`), the error is surfaced as `Err(TaskError)`. If the handle
is **dropped without joining**, the error is silently discarded (fire-and-forget
semantics). There is no automatic panic propagation to parent (unlike Go's
`recover` convention or Erlang linked processes).

**Rationale:** Go panics crash the goroutine and by default the process (unless
recovered). Erlang processes die silently unless linked or monitored. Kotlin
`async {}` stores the exception; `await()` rethrows it. Simple adopts the Kotlin
`async` model: the handle is the error carrier. Callers who need Erlang-style
monitoring must use the supervisor API or explicitly join.

**Test evidence:** Spawn a task that panics; drop the handle without joining;
assert the process is still running. Spawn a task that panics; join the handle;
assert `Err(TaskError::Panic(...))` is returned.

---

### REQ-CONC-008 — Error value identity across task boundary (E-2)

**Question:** When an error crosses a task/actor boundary, is it the same value
or a copy?

**Decision (PROPOSED):** Error values follow the same copy semantics as all other
messages. In `nogc_async_mut` mode: **deep copy** on send (Erlang-style). In
`gc_async_mut` mode: **reference copy** (shared reference to the same heap
object, protected by GC). Error type identity (the concrete type tag) is preserved
in both modes. There is no error-wrapping or type erasure at the boundary.

**Rationale:** Erlang error reasons are terms, always copied. Rust moves errors
across `mpsc::channel`. Go error interface values are copied (the interface fat
pointer is copied; the underlying data may be shared). Simple's `nogc` copy
invariant applies uniformly; `gc` mode is reference-safe via GC.

**Test evidence:** In `nogc` mode, create a structured error value with a heap-
allocated field; send it across a channel; mutate the original after send; assert
the received error is unchanged. In `gc` mode, assert the received error is
reference-equal to the sent error.

---

### REQ-CONC-009 — Sibling cancellation ordering and first-error rule (E-4)

**Question:** In a `task_scope`, when one sibling task fails, what happens to
other siblings and which error is reported?

**Decision (PROPOSED):** A `task_scope` (structured concurrency scope) follows
Kotlin `coroutineScope` semantics: when any child task fails, **all sibling tasks
receive cancellation**. The scope waits for all siblings to finish cancellation
cleanup before propagating. The **first error wins**: if multiple siblings fail
concurrently, the first error to be recorded is the one surfaced to the caller;
subsequent errors are discarded. Cancellation errors from siblings cancelled as
a consequence of the first failure are not counted as new errors.

**Rationale:** Kotlin `coroutineScope` and `supervisorScope` define exactly this
split. Go's `errgroup` uses first-error with cooperative context cancellation.
Rust's `JoinSet` propagates all errors. Simple adopts Kotlin's `coroutineScope`
rule (not `supervisorScope`) as the default because it prevents partial-success
silent failures.

**Test evidence:** Spawn a scope with 3 children; make child-1 fail immediately,
child-2 sleep 50ms then check cancellation, child-3 sleep 200ms without checking;
assert scope returns `Err(child1_error)`; assert child-2 was cancelled; assert
child-3 ran to completion (or was cancelled depending on its cooperation).

---

## Group 4: Isolation / Sharing

### REQ-CONC-010 — Shared mutable state enforcement (I-2)

**Question:** Can two green tasks share a mutable variable directly?

**Decision (PROPOSED):** **No shared mutable variables across task boundaries.**
This is a language-level invariant for green tasks in Simple. Values passed to
`green_spawn` must be either immutable (sealed/readonly) or owned (moved, not
shared). Mutable state shared across tasks must use `Mutex<T>`, `RwLock<T>`, or
channels. The compiler emits a diagnostic (not yet implemented; tracked as a
future enforcement item) for attempted cross-task mutable sharing.

**Rationale:** Rust enforces this at compile time via ownership + `Send` trait.
Swift `actor` isolation enforces it at compile time. Erlang enforces it by
copying everything. Simple's current enforcement is runtime-enforced via the
`nogc_async_mut` copy model; compile-time enforcement is on the roadmap.

**Test evidence:** Write a spec that attempts to modify a variable from two tasks
without a mutex; assert a compile-time or runtime error is raised (spec is
annotated `@pending_enforcement` until compiler check lands).

---

### REQ-CONC-011 — Memory model: happens-before (I-3)

**Question:** What is the formal happens-before relationship between concurrent
operations in Simple?

**Decision (PROPOSED):** Simple adopts a **message-passing happens-before** model:

1. All operations in task A that precede `channel.send(msg)` happen-before all
   operations in task B that follow `channel.recv()` that returns `msg`.
2. `task_spawn(f)` happens-before the first operation of `f`.
3. All operations of task B happen-before `handle.join()` returns in task A.
4. Within a single green task: sequential consistency (program order).
5. No other cross-task ordering is guaranteed. In particular, two tasks that do
   not communicate via channels or join have **no guaranteed ordering**.

There is no shared memory between tasks in `nogc` mode, so the memory model
reduces to the message-passing rules. In `gc` mode, access to shared heap
objects through `Mutex`/`RwLock` follows lock-release/acquire ordering (standard
mutual exclusion happens-before).

**Rationale:** Go's memory model (2022 revision) uses the same message-passing
rule: "A send on a channel happens before the corresponding receive from that
channel completes." Rust's memory model is defined in terms of `Arc`/`Mutex`
acquire-release. Erlang's model is purely message-passing (no shared memory).
Simple's `nogc` mode is Erlang-equivalent; `gc` mode adds mutex ordering.

**Test evidence:** Spawn two tasks; task A sends value X on a channel; task B
receives and reads X; assert B never observes a stale value. Write a Litmus-style
test in `spec/language/concurrency/` that asserts the happens-before invariant
for send/recv and spawn/join.

---

### REQ-CONC-012 — Actor identity on restart (I-5)

**Question:** If an actor is restarted by a supervisor, does it get the same
`ActorId`? Can stale references cause issues?

**Decision (PROPOSED):** A restarted actor receives a **new, unique `ActorId`**.
The old `ActorId` becomes permanently invalid. Sending to an old `ActorId`
returns `SendResult::closed` (not a crash). There is no `ActorRef` rebinding —
callers who hold stale IDs must re-discover the new ID through the supervisor
or a registry. This prevents stale-ref message loss from being silent.

**Rationale:** Erlang gives a new PID on restart; old PIDs silently drop messages.
Simple chooses the same behavior for the drop but differs from Erlang by surfacing
`SendResult::closed` rather than silently dropping, making the staleness
detectable without monitors.

**Test evidence:** Spawn an actor; record its `ActorId`; crash and restart it;
send to the old ID; assert `SendResult::closed` is returned.

---

## Group 5: Channel / Mailbox Edge Cases

### REQ-CONC-013 — Send to a closed/terminated actor: full semantics (M-1)

**Question:** What exactly does `SendResult::closed` mean — orderly shutdown vs
crash? Is there a distinction?

**Decision (PROPOSED):** `SendResult::closed` means the receiving end of the
channel is **no longer accepting messages**, regardless of the reason (orderly
shutdown, crash, or GC). The sender cannot distinguish between orderly and crash
closure. To detect crash vs orderly shutdown, use the actor monitor/supervisor
API (which delivers a typed `ActorExitReason`). `SendResult::closed` is never a
crash on the sender side — it is a recoverable, typed result.

**Rationale:** Go panics on send-to-closed channel — this is widely considered a
design mistake. Erlang drops silently. Simple's existing `SendResult` enum is
correct; this decision pins the "no distinction at send site" rule and directs
callers to use monitors for crash detection.

**Test evidence:** Close a channel orderly; send to it; assert `SendResult::closed`.
Crash an actor; send to its channel; assert `SendResult::closed`. In both cases
assert the sender task continues normally.

---

### REQ-CONC-014 — Receive from a closed mailbox (M-2)

**Question:** Does `recv()` from a closed channel return a sentinel, raise an
error, or block forever?

**Decision (PROPOSED):** `channel.recv()` on a **drained and closed channel**
returns `Err(ChannelError::Closed)` immediately (never blocks). While the channel
has pending messages it returns `Ok(msg)` regardless of whether the sender has
closed. This matches Go's `v, ok := <-ch` where `ok=false` after drain, extended
to Simple's typed error result. A `recv()` on a channel that has senders but no
pending messages **suspends the task** until a message arrives or the channel is
closed (whichever comes first).

**Rationale:** Go: receive from closed returns zero value + `ok=false`. Never blocks.
Rust `mpsc::recv()`: returns `Err(RecvError)` when all senders dropped and queue empty.
Simple aligns with Rust: typed error, never blocks on drained-closed, does block
on empty-but-open.

**Test evidence:** Close a channel with 2 messages remaining; receive 3 times;
assert first two return `Ok(msg)`, third returns `Err(ChannelError::Closed)`.
Receive from an empty-but-open channel from one task while another task eventually
sends; assert the blocked recv unblocks and returns the message.

---

### REQ-CONC-015 — Selective receive semantics (M-5)

**Question:** Does Simple support Erlang-style selective receive (pattern-match on
mailbox, skipping non-matching messages)?

**Decision (PROPOSED):** **No selective receive in Simple's channels.** Channels
are FIFO queues; `recv()` always returns the head message. There is no
mailbox-scan or pattern-match-skip. Callers needing message dispatch by type must
use a typed union (variant) message type and match on the received value, or use
separate channels per message type. This avoids the O(N) mailbox-scan cost and
queue-head-of-line blocking that Erlang selective receive can cause.

**Rationale:** Erlang selective receive is O(N) on mailbox size and is a known
source of performance problems. Go channels have no selective receive; `select`
chooses between channel endpoints, not message values. Kotlin has no selective
receive. Simple adopts the Go/Kotlin model: FIFO channels + typed message dispatch
at the application layer.

**Test evidence:** Spec demonstrating typed union message dispatch over a single
channel; assert messages are processed in FIFO order. Spec asserting there is no
`recv_where(predicate)` or equivalent API in `std.concurrent`.

---

### REQ-CONC-016 — Nil/uninitialized channel operations (M-6)

**Question:** What happens when you send to or receive from an uninitialized
(nil/null) channel reference?

**Decision (PROPOSED):** An uninitialized channel reference is a **compile-time
or runtime type error**. Simple's type system does not permit `null` channel
values by default (option types are explicit). If a channel value is wrapped in
`Option<Channel<T>>`, calling `.send()` on the `None` case requires explicit
unwrapping; failing to unwrap raises a standard `Option::None` access error
(not a special channel error). There is no "blocks forever" behavior as in Go's
nil channel.

**Rationale:** Go's nil channel blocks forever on send and receive — intentional
but surprising. Rust's `Option<Sender<T>>` forces explicit `None` handling. Simple
adopts the Rust model: no implicit nil-block, explicit option handling.

**Test evidence:** Assert that `channel_new()` always returns an initialized
channel (non-optional). Assert that calling `.send()` on `None` raises an
`OptionUnwrapError` at the option layer, not a channel-specific error.

---

## Group 6: Lifecycle (Leak / Zombie)

### REQ-CONC-017 — Task leak prevention guarantee (L-1)

**Question:** Does Simple guarantee tasks cannot leak (run forever unobserved)?

**Decision (PROPOSED):** `task_scope` (structured concurrency) **guarantees no
task leaks within the scope**: the scope does not return until all child tasks
have completed or been cancelled. `green_spawn` without a scope (fire-and-forget)
**does not prevent leaks** — the task runs until completion regardless of whether
any handle is held. Detached tasks (`green_spawn` + handle-drop) are the only
source of potential leaks; callers must manage their own lifecycle. A future
`task_scope` enforcement mode (opt-in lint) will warn on unscoped spawns.

**Rationale:** Kotlin's structured concurrency (`coroutineScope`) is the gold
standard for leak prevention. Go has no built-in prevention. Rust's `tokio::spawn`
detaches by default. Simple offers both: scoped (safe, Kotlin-style) and unscoped
(Go-style, with known risks).

**Test evidence:** Create a `task_scope`; panic inside it; assert all child tasks
are cancelled before the scope propagates the panic. Spawn a detached task; assert
the process exits without waiting for it (fire-and-forget).

---

### REQ-CONC-018 — Zombie task memory (L-2)

**Question:** If a task completes but its handle is never joined, is the result
retained? Is there a memory leak?

**Decision (PROPOSED):** A completed task's result is **buffered in the handle**
until the handle is joined or dropped. Dropping the handle without joining
**discards the result** (no memory leak — the buffer is freed with the handle).
In `gc_async_mut` mode the GC collects the handle and result together. In
`nogc_async_mut` mode the caller is responsible for joining or explicitly dropping
the handle. A handle that is never dropped (orphaned in `nogc` mode) does leak
the result buffer.

**Rationale:** Rust `JoinHandle` drop = task detaches, result is lost (no leak
if dropped). Go has no handle by default. Kotlin `Deferred` retains result until
awaited or cancelled. Simple: handle-drop frees the result (like Rust after the
task completes) in `nogc` mode; GC handles it in `gc` mode.

**Test evidence:** Spawn a task that returns a large value; drop the handle
without joining; in `nogc` mode, assert the memory used by the task result is
freed (checked via allocator stats).

---

### REQ-CONC-019 — Detached tasks (fire-and-forget) (L-3)

**Question:** Are detached tasks (fire-and-forget) supported? What is the
lifecycle contract?

**Decision (PROPOSED):** Detached tasks are supported via `green_spawn_detached()`
(or equivalently `green_spawn()` + immediate handle drop). A detached task runs
to completion or until the process exits; there is no way to join or cancel it
after detachment. Detached tasks are appropriate for background work that must
not block the spawner and whose failure is acceptable to ignore. Error from a
detached task is silently discarded. Structured concurrency (`task_scope`) is
preferred for all non-background work.

**Rationale:** Go's default goroutine model is fire-and-forget. Rust `tokio::spawn`
detaches. Kotlin discourages it but allows `GlobalScope.launch`. Simple explicitly
supports it as a named operation with documented semantics rather than an
accidental consequence of handle-drop.

**Test evidence:** Spawn a detached task that writes to a shared channel after
a delay; drop all other references; assert the process does not exit early and
the channel receives the message.

---

### REQ-CONC-020 — Actor garbage collection trigger (L-4)

**Question:** When is an actor freed? What triggers collection?

**Decision (PROPOSED):** An actor is freed when **all of the following are true**:
(1) the actor's task has completed (either returned or errored), (2) no live
`ActorId`/`ActorRef` references exist that are actively held, and (3) the
mailbox is drained. In `nogc_async_mut` mode, the runtime performs reference-
counting on `ActorRef`; when the count drops to zero and the task is complete,
the actor struct and mailbox buffer are freed. In `gc_async_mut` mode, the GC
collects when the actor is unreachable.

**Rationale:** Erlang processes are freed when they exit; the mailbox is discarded.
Go goroutines are freed by the GC when unreachable. Simple's `nogc` mode requires
explicit reference counting because there is no GC; `gc` mode delegates to GC.

**Test evidence:** Spawn an actor; send it a shutdown message; join the handle;
assert actor memory is freed (via allocator stats). In `gc` mode, drop all refs
and trigger GC; assert the actor object is collected.

---

## Group 7: Backpressure

### REQ-CONC-021 — Backpressure propagation across pipeline stages (B-2)

**Question:** In a multi-stage async pipeline (producer → transform → consumer),
does backpressure from the consumer propagate back to the producer?

**Decision (PROPOSED):** Backpressure **propagates naturally through bounded
channels**. When the downstream channel is full, the upstream task receives
`SendResult::full` and is responsible for suspending itself (via an explicit retry
loop with `green_yield()`) or dropping the message. There is **no automatic
backpressure propagation** — the pipeline designer must handle `full` results.
The recommended pattern is a bounded channel at each stage boundary; producers
poll until `SendResult::success`. In `gc_async_mut` mode with unbounded channels,
backpressure does not propagate — this is an explicit design choice (Erlang model)
and must be understood by callers.

**Rationale:** Kotlin Flow has built-in backpressure via `SUSPEND` strategy.
Reactive Streams defines a `request(n)` pull protocol. Go channels block on full
(automatic backpressure). Simple's explicit `SendResult` model follows Kotlin's
`Channel(DROP_LATEST)` equivalent but requires the caller to implement the
retry/suspend loop. This keeps the runtime simple and puts policy at the
application layer.

**Test evidence:** Build a 3-stage pipeline with bounded channels of capacity 1;
produce 100 items at maximum speed; assert that memory usage stays bounded (no
unbounded queue growth); assert all 100 items are processed by the consumer.

---

### REQ-CONC-022 — Timeout: is a timed-out recv observable by the other side? (B-3)

**Question:** If `recv()` times out, has the corresponding `send()` already
consumed a slot? Is the message lost?

**Decision (PROPOSED):** A `recv()` timeout means the task unblocked because the
timeout elapsed **before any message arrived**. No message was consumed — the
channel state is unchanged. A message sent **after** the timeout (from another
task) is not lost; it remains in the channel for the next recv. A `send()` timeout
(if `send_timeout()` is offered) means the send was aborted before the message
entered the channel — no partial send. Timeouts are clean cancellations with no
observable side effects on the channel.

**Rationale:** Go's `select { case v := <-ch: ... case <-time.After(...): }`:
if the timer fires, no message is consumed. Erlang `receive after Timeout`: same
— no message consumed, message stays. Simple aligns with both: timeout is a
read that didn't happen, not a partial read.

**Test evidence:** Attempt `recv_timeout(1ms)` on an empty channel; assert it
returns `Err(ChannelError::Timeout)`; then send a message; assert the next
`recv()` returns the message (proving it was not consumed by the timeout).

---

## Group 8: Coroutine-Specific Semantics

### REQ-CONC-023 — Coroutine error propagation to resumer (CO-2)

**Question:** If an error (or panic) occurs inside a coroutine, is it delivered
to the resumer as a typed result?

**Decision (PROPOSED):** Errors inside a coroutine are **delivered to the resumer
as a typed `Err` result** from the `resume()` call. The coroutine is terminated
on unhandled error; subsequent `resume()` calls return `Err(CoroutineError::Dead)`.
The resumer is never crashed by a coroutine error. This mirrors Lua's `pcall`-
wrapped resume: `coroutine.resume()` returns `false, error` on coroutine error.

**Rationale:** Lua `coroutine.resume()` returns `(false, errorMsg)` on error —
the resumer receives the error and continues. Python generators raise
`StopIteration` on exhaustion, exceptions propagate to the caller. Simple adopts
the Lua model: resume is a typed result, errors are first-class return values.

**Test evidence:** Create a coroutine that panics on the second resume; assert
the first resume returns `Ok(yield_value)`, the second returns
`Err(CoroutineError::Panic(...))`, and a third resume returns
`Err(CoroutineError::Dead)`.

---

### REQ-CONC-024 — Yield value passing (asymmetric coroutine data flow) (CO-3)

**Question:** Can a coroutine yield a value to its resumer, and can the resumer
pass a value back on the next `resume()`?

**Decision (PROPOSED):** Yes, Simple coroutines (when defined) support
**bidirectional value passing**:
- `yield(value)` suspends the coroutine and delivers `value` to the resumer as
  the `Ok(value)` return of `resume()`.
- `resume(co, send_value)` passes `send_value` into the coroutine as the return
  value of the `yield()` call that suspended it.
- The initial `resume(co, initial_value)` passes `initial_value` as the first
  argument to the coroutine body.

This is the Lua/Python generator model. `async fn` tasks do not use this mechanism;
they use channels or return values for communication.

**Rationale:** Lua's `coroutine.yield(v)` / `coroutine.resume(co, v)` is the
canonical asymmetric coroutine protocol. Python's `generator.send(v)` mirrors it.
Rust generators (unstable) follow the same pattern. Simple adopts it for explicit
coroutine types (`Coroutine<In, Out, Return>`), separate from `async fn`.

**Test evidence:** Create a coroutine that yields its input doubled; resume with
`1`, assert yield returns `2`; resume with `3`, assert yield returns `6`; resume
with `stop_signal`, assert coroutine completes.

---

## Group 9: GC Interaction

### REQ-CONC-025 — Coroutine frame retention of large objects (G-1)

**Question:** Can a suspended coroutine frame keep a large object alive longer
than expected, causing memory bloat?

**Decision (PROPOSED):** Yes, this is a **known and documented behavior**. A
suspended coroutine or `async fn` future retains all live variables in its
suspension frame. If a large object (e.g., a buffer) is held in a local variable
across an `await` point, it remains allocated for the duration of the suspension.
Callers should explicitly drop large objects before `await` points when memory
pressure is a concern. In `gc_async_mut` mode the GC can collect the object if
the coroutine frame is the only live reference; in `nogc_async_mut` mode the
object is pinned until the frame completes or explicitly released.

**Rationale:** Python generators are known for this: `yield` inside a loop that
holds a large list keeps the list alive. Rust futures hold their entire captured
environment across `.await`. Go goroutine stacks can grow but are independently
collected. Simple acknowledges this as an ergonomic issue, not a correctness issue;
tooling (memory profiler) should surface long-lived suspension frames.

**Test evidence:** Create a coroutine that captures a 1MB buffer, suspends for
1s, then drops the buffer; assert in `nogc` mode that the 1MB is held during
suspension and freed after the coroutine resumes and drops explicitly.

---

## Appendix: Coverage Mapping

| Checklist ID | REQ-CONC | Status Change |
|---|---|---|
| S-3 | REQ-CONC-001 | UNCOVERED → PROPOSED |
| S-4 | REQ-CONC-002 | UNCOVERED → PROPOSED |
| S-5 | REQ-CONC-003 | UNCOVERED → PROPOSED |
| C-2 | REQ-CONC-004 | UNCOVERED → PROPOSED |
| C-3 | REQ-CONC-005 | UNCOVERED → PROPOSED |
| C-6 | REQ-CONC-006 | UNCOVERED → PROPOSED |
| E-1 | REQ-CONC-007 | UNCOVERED → PROPOSED |
| E-2 | REQ-CONC-008 | UNCOVERED → PROPOSED |
| E-4 | REQ-CONC-009 | UNCOVERED → PROPOSED |
| I-2 | REQ-CONC-010 | PARTIAL → PROPOSED |
| I-3 | REQ-CONC-011 | UNCOVERED → PROPOSED |
| I-5 | REQ-CONC-012 | UNCOVERED → PROPOSED |
| M-1 | REQ-CONC-013 | PARTIAL → PROPOSED |
| M-2 | REQ-CONC-014 | UNCOVERED → PROPOSED |
| M-5 | REQ-CONC-015 | UNCOVERED → PROPOSED |
| M-6 | REQ-CONC-016 | UNCOVERED → PROPOSED |
| L-1 | REQ-CONC-017 | PARTIAL → PROPOSED |
| L-2 | REQ-CONC-018 | PARTIAL → PROPOSED |
| L-3 | REQ-CONC-019 | UNCOVERED → PROPOSED |
| L-4 | REQ-CONC-020 | PARTIAL → PROPOSED |
| B-2 | REQ-CONC-021 | UNCOVERED → PROPOSED |
| B-3 | REQ-CONC-022 | UNCOVERED → PROPOSED |
| CO-2 | REQ-CONC-023 | UNCOVERED → PROPOSED |
| CO-3 | REQ-CONC-024 | UNCOVERED → PROPOSED |
| G-1 | REQ-CONC-025 | UNCOVERED → PROPOSED |

**Items not duplicated here (already COVERED or in REQ-MCG-001..010):**
I-1 (copy semantics — covered), I-4 (frame ownership — covered),
M-3 (mailbox overflow NoGC — covered), B-1 (bounded send result — covered),
G-2 (GC pause — covered), S-1 (preemption model — REQ-MCG-008 tracks fairness gap),
S-2 (parallelism control — REQ-MCG-008), C-1 (cancellation points — partial,
extended by REQ-CONC-005/006), C-4 (propagation direction — extended by REQ-CONC-009),
C-5 (resource cleanup — extended by REQ-CONC-005), E-3 (supervisor intensity —
tracked separately), CO-1 (stackless/stackful — design doc covers this),
M-4 (message ordering — FIFO per channel, extended by REQ-CONC-003).
