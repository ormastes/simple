# nogc_async_mut Architecture Guide

Architecture documentation for the `src/lib/nogc_async_mut/` library — Simple's async concurrency runtime. 57 files, 9,795 lines.

**Updated:** 2026-02-22

---

## Module Map

### Root-Level Modules (19 files, ~3,534 lines)

| File | Lines | Purpose |
|------|------:|---------|
| `async_unified.spl` | 157 | Runtime-agnostic interface — selects embedded vs host |
| `async_embedded.spl` | 479 | Embedded runtime (bare-metal, fixed-capacity) |
| `async_host.spl` | 58 | Host runtime entry point (OS-backed) |
| `concurrent.spl` | 265 | Concurrent primitives + FFI declarations |
| `async.spl` | 86 | Re-exports async core types |
| `actor_scheduler.spl` | 458 | Reductions-based fair scheduling for actors |
| `actor_heap.spl` | 185 | Per-actor heap with generational GC (Erlang-inspired) |
| `mailbox_actor.spl` | 255 | Mailbox-based actor implementation |
| `supervisor.spl` | 165 | OTP-style supervisor trees |
| `thread_pool.spl` | 325 | Thread pool with work distribution |
| `generator.spl` | 40 | Generator/coroutine support |
| `effects.spl` | 74 | Effect system annotations (`@async`, `@io`, etc.) |
| `mailbox.spl` | 76 | Bounded mailbox for actor messaging |
| `monitor.spl` | 74 | Process monitoring and linking |
| `gen_server.spl` | 82 | GenServer behavior (Erlang OTP) |
| `gen_statem.spl` | 76 | GenStatem behavior (state machine) |
| `gen_event.spl` | 84 | GenEvent behavior (event manager) |
| `thread_sffi.spl` | 285 | Thread FFI bindings |
| `async_sffi.spl` | 110 | Async FFI bindings |

### `async/` — Core Async Primitives (11 files)

| File | Purpose |
|------|---------|
| `__init__.spl` | Module marker |
| `future.spl` | Future<T> type — single-value async computation |
| `promise.spl` | Promise<T> — write-once future completion |
| `poll.spl` | Poll enum (Ready/Pending) |
| `task.spl` | Task state management |
| `executor.spl` | Task executor — runs futures to completion |
| `scheduler.spl` | Embedded scheduler — fixed run queue |
| `runtime.spl` | Embedded runtime — inline futures, MAX_FUTURES=32 |
| `io.spl` | Async I/O integration |
| `ffi.spl` | Async FFI declarations |
| `combinators.spl` | join, select, race, timeout combinators |

### `async_host/` — Host Runtime (12 files)

| File | Purpose |
|------|---------|
| `__init__.spl` | Module marker |
| `scheduler.spl` | Work-stealing scheduler (278 lines) |
| `runtime.spl` | HostRuntime — OS-backed execution |
| `future.spl` | HostFuture — heap-allocated, waker-based |
| `promise.spl` | HostPromise — multi-consumer completion |
| `waker.spl` | Waker callbacks for I/O readiness |
| `handle.spl` | HostTaskHandle — task lifecycle management |
| `joinset.spl` | HostJoinSet — structured task group |
| `unordered.spl` | HostFuturesUnordered — completion-order streaming |
| `worker_thread.spl` | Worker thread management |
| `thread_safe_queue.spl` | Lock-free concurrent queue |
| `combinators.spl` | Host-specific combinators |

### `actors/` — Rich Actor Model (2 files)

| File | Lines | Purpose |
|------|------:|---------|
| `__init__.spl` | — | Module marker |
| `actor.spl` | 588 | Full actor model with message dispatch |

### `concurrent/` — Thread-Safe Primitives (8 files)

| File | Purpose |
|------|---------|
| `__init__.spl` | Module marker |
| `mod.spl` | Module re-exports |
| `channel.spl` | MPMC channels — send/recv/try_recv/close |
| `mutex.spl` | Mutex — mutual exclusion lock |
| `rwlock.spl` | RWLock — reader-writer lock |
| `thread.spl` | Thread — OS thread wrapper |
| `actor.spl` | Simple actor (lightweight, concurrent/) |
| `collections.spl` | Thread-safe collections (MpscQueue, MpmcQueue, ConcurrentMap, AtomicFlag, Once, Barrier) |

### `io/` — Async I/O (5 files)

| File | Lines | Purpose |
|------|------:|---------|
| `event_loop.spl` | 258 | EventLoop — epoll/kqueue abstraction |
| `file.spl` | 445 | Async file I/O |
| `tcp.spl` | 341 | Async TCP sockets |
| `udp.spl` | 217 | Async UDP sockets |
| `buffer.spl` | 362 | I/O buffer management |

---

## Two-Tier Runtime Architecture

Simple provides two async runtimes targeting different deployment scenarios:

| Aspect | Embedded Runtime | Host Runtime |
|--------|-----------------|--------------|
| **Location** | `async/`, `async_embedded.spl` | `async_host/` |
| **Target** | Bare-metal, RTOS, WASM | Desktop, server, cloud |
| **Future storage** | Inline value, fixed slot array | Heap-allocated, dynamic |
| **Capacity** | MAX_FUTURES=32 | Unbounded |
| **Scheduler** | Round-robin, fixed run queue | Work-stealing, multi-threaded |
| **I/O** | Polling, no OS event loop | epoll/kqueue event loop |
| **Waker** | Index-based wakeup | Callback-based Waker struct |
| **Allocation** | Zero heap alloc (arena/stack) | Standard heap allocation |
| **Threading** | Single-threaded only | Multi-threaded support |

### Runtime Selection

`async_unified.spl` provides a single API that defaults to the host runtime:

```simple
use std.async_unified.*

val runtime = HostRuntime.new()
val handle = runtime.run_task(\: compute())
val result = runtime.block_on(handle.join())
```

Future: Compile-time `@config(runtime: "host" | "embedded")` will enable static selection.

---

## Actor Model

### Architecture Overview

Three actor implementations serve different complexity levels:

| Level | File | Use Case |
|-------|------|----------|
| Simple actor | `concurrent/actor.spl` | Lightweight message handler |
| Rich actor | `actors/actor.spl` | Full supervision, lifecycle, state |
| Mailbox actor | `mailbox_actor.spl` | Erlang-style mailbox + selective receive |

### Rich Actor (actors/actor.spl — 588 lines)

The primary actor implementation with:

**Core Types:**
- `ActorId` — unique identifier (auto-incrementing i64)
- `Message` — method name + args + optional reply_to
- `DispatchResult` — Ok/MethodNotFound/HandlerError status
- `HandlerTable` — name → handler function mapping

**Lifecycle:**
```
spawn → init → receive loop → terminate
         ↓                       ↑
    handle_call/cast         supervision
```

**Usage:**
```simple
use std.actors.actor.{ActorRef, spawn_actor, make_handlers}

var handlers = make_handlers()
handlers.register("increment", \args: do_increment(args))
handlers.register("get", \args: do_get(args))
val worker = spawn_actor(handlers)
worker.send("increment", [])
```

### Per-Actor Heap (actor_heap.spl — 185 lines)

Erlang-inspired per-actor memory isolation with generational GC:

**HeapConfig presets:**

| Preset | Initial Size | Max Size | GC | Generational |
|--------|-------------|----------|-----|-------------|
| `default` | 2 KB | 16 MB | Yes | Yes |
| `small` | 512 B | 4 KB | Yes | Yes |
| `large` | 64 KB | 64 MB | Yes | Yes |
| `no_gc(size)` | size | size | No | No |

**Key Types:**
- `HeapConfig` — initial_size, max_size, gc_enabled, generational, pretenure_threshold
- `HeapRegion` — used bytes + capacity tracking
- `HeapStats` — used/allocated bytes, object count, GC count, gen sizes
- `ActorHeap` — the heap itself with young/old generation regions

**Arena mode (`no_gc`):** Fixed-size arena, no GC overhead, freed entirely on actor termination. Maps to Zig-style arena allocators.

---

## Actor Scheduler (actor_scheduler.spl — 458 lines)

Reductions-based fair scheduling inspired by BEAM VM:

### Priority Levels

```simple
enum ActorPriority:
    Max      # System-critical (monitors, supervisors)
    High     # Latency-sensitive
    Normal   # Default for user actors
    Low      # Background work
```

### Actor States

```
Runnable → Running → Waiting → Runnable (wakeup)
    ↓         ↓         ↓
  Dead      Dead      Dead     (termination)
    ↑
Suspended (manual pause)
```

### Scheduler Configs

| Config | Reductions/Slice | Schedulers | Work Stealing |
|--------|----------------:|----------:|:-------------:|
| `default` | 2,000 | 4 | Yes |
| `single_threaded` | 2,000 | 1 | No |
| `low_latency` | 500 | 4 | Yes |

**Reductions:** Each function call/message receive costs 1 reduction. When an actor exhausts its timeslice, it yields and goes to the back of its priority queue. This prevents any single actor from monopolizing the scheduler.

---

## Concurrent Primitives

### Channel (concurrent/channel.spl — 167 lines)

MPMC (multi-producer, multi-consumer) channels:

```simple
use std.concurrent.channel.{channel_new}

val ch = channel_new()
ch.send(42)
val value = ch.recv()    # Blocking receive
val maybe = ch.try_recv() # Non-blocking (returns nil if empty)
ch.close()               # Idempotent
```

**Properties:**
- Unbounded queue (no capacity limit)
- FIFO ordering per sender
- Blocking recv waits until message available
- Closed channel rejects sends, drains remaining messages

### Mutex & RWLock

```simple
use std.concurrent.mutex.{Mutex}
use std.concurrent.rwlock.{RWLock}

var mtx = Mutex.new()
mtx.lock()
# critical section
mtx.unlock()

var rw = RWLock.new()
rw.read_lock()    # Multiple readers OK
rw.read_unlock()
rw.write_lock()   # Exclusive access
rw.write_unlock()
```

### Thread-Safe Collections (concurrent/collections.spl)

| Type | Description |
|------|-------------|
| `MpscQueue` | Multi-producer, single-consumer queue |
| `MpmcQueue` | Multi-producer, multi-consumer queue |
| `ConcurrentMap` | Thread-safe hash map |
| `AtomicFlag` | Atomic boolean flag |
| `Once` | One-time initialization barrier |
| `Barrier` | N-thread synchronization barrier |

---

## OTP Behaviors

Erlang/OTP-style behaviors for structured concurrent patterns:

### GenServer (gen_server.spl — 82 lines)

Request-reply server pattern:

```simple
# GenServer trait methods:
# - init(args) -> State
# - handle_call(msg, state) -> (reply, new_state)
# - handle_cast(msg, state) -> new_state
# - handle_info(msg, state) -> new_state
# - terminate(reason, state) -> ()
```

### GenStatem (gen_statem.spl)

Finite state machine with event-driven transitions:

```simple
# GenStatem trait methods:
# - callback_mode() -> mode  (state_functions | handle_event_function)
# - init(args) -> (initial_state, data)
# - handle_event(event_type, event, state, data) -> action
# - terminate(reason, state, data) -> ()
```

### GenEvent (gen_event.spl)

Event manager with pluggable handlers:

```simple
# GenEventManager API:
# - start() -> manager
# - add_handler(manager, handler)
# - remove_handler(manager, handler_id)
# - notify(manager, event)  # Fan-out to all handlers
# - call(manager, handler_id, request) -> reply
# - stop(manager)
```

### Supervisor (supervisor.spl — 165 lines)

Supervision trees for fault tolerance:

```simple
# Supervisor restart strategies:
# - one_for_one:  restart only the failed child
# - one_for_all:  restart all children on any failure
# - rest_for_one: restart failed child and all started after it
```

### Monitor (monitor.spl)

Process monitoring and linking:

```simple
# monitor(target_actor_id) -> MonitorRef
# link(actor_a, actor_b)    # Bidirectional link
# DownEvent — sent when monitored actor dies
# LinkExitEvent — sent when linked actor exits
```

---

## I/O Event Loop (io/event_loop.spl — 258 lines)

### Architecture

```
┌─────────────────────────────────────┐
│           EventLoop                 │
│  ┌─────────────┐  ┌─────────────┐  │
│  │ epoll_fd /   │  │  Waker      │  │
│  │ kqueue_fd    │  │  Registry   │  │
│  └─────────────┘  └─────────────┘  │
│         ↓                ↓          │
│  ┌──────────────────────────────┐   │
│  │     fd → (Interest, Waker)   │   │
│  │     registration map         │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
```

**Components:**
- `EventLoop` — core abstraction over epoll (Linux) / kqueue (BSD/macOS)
- `Waker` — callback to wake a pending future when I/O is ready
- `Interest` — Read / Write / ReadWrite event interest
- `IoEvent` — ready fd + interest that triggered

**Usage:**
```simple
val loop = EventLoop.new()
val waker = Waker.new(task_id, \id: scheduler.wake(id))
loop.register(socket_fd, Interest.Read, waker)
val events = loop.poll(timeout_ms)
for event in events:
    if event.ready == Interest.Read:
        handle_read(event.fd)
```

---

## Thread Pool (thread_pool.spl — 325 lines)

Fixed-size thread pool for CPU-bound work:

**Features:**
- Configurable worker count
- Task queue with work distribution
- Graceful shutdown (drain pending tasks)
- Worker thread lifecycle management

---

## Generator / Effect System

### Generator (generator.spl — 40 lines)

Lightweight coroutine support for lazy sequences:

```simple
# Generators yield values lazily
# Suspended between yields, resumed on next()
```

### Effects (effects.spl — 74 lines)

Annotation-based effect tracking:

```simple
# Effect annotations:
# @async — function is async (may suspend)
# @io    — function performs I/O
# @pure  — function has no side effects
# @sync  — function is synchronous (default)
```

These annotations are used for:
- Documentation of function behavior
- Future: Compile-time effect checking (Sendable enforcement)
- Future: Async function coloring (when full async support lands)

---

## Host Runtime: Work-Stealing Scheduler

The `async_host/scheduler.spl` (278 lines) implements a work-stealing scheduler:

### WorkStealingQueue

```simple
struct WorkStealingQueue:
    local: [usize]      # Local push/pop (LIFO for cache locality)
    steal_end: usize     # Steal index (FIFO for fairness)

    me push(task_id: usize)     # Push to local end
    me pop() -> Option<usize>   # Pop from local end (LIFO)
    me steal() -> Option<usize> # Steal from other end (FIFO)
```

### Scheduler Modes

```simple
enum SchedulerMode:
    SingleThreaded   # Single-threaded work-stealing
    MultiThreaded    # Multi-threaded with OS threads
```

### HostScheduler

```simple
class HostScheduler:
    # Features:
    # - Per-thread run queues with local LIFO
    # - Cross-thread stealing with FIFO
    # - Priority-based scheduling
    # - Task lifecycle tracking
```

---

## Module Dependencies

```
async_unified.spl
  ├── common/async_core (Poll, TaskState, Priority, CancellationToken)
  │   └── NOTE: async_core lives in src/lib/common/, not nogc_async_mut/
  └── async_host/ (HostRuntime, HostScheduler, HostFuture)
       └── async_host/thread_safe_queue
       └── async_host/waker
       └── async_host/future

actor_scheduler.spl
  ├── mailbox (Mailbox, MailboxConfig, SendResult)
  └── types (ActorId, Reductions, Capacity, Count)

actors/actor.spl (standalone — message dispatch only)

supervisor.spl (standalone — no imports)

io/event_loop.spl
  └── common/io/types (IoError, IoErrorKind, Interest, IoEvent)

concurrent/channel.spl (standalone — FFI atomics)
concurrent/mutex.spl (standalone — FFI locks)
concurrent/rwlock.spl (standalone — FFI locks)
concurrent/thread.spl (standalone — FFI threads)
```

---

## Key Design Decisions

### No Function Coloring

Following Zig's approach, `async_unified.spl` provides a single API where the same code works with both embedded and host runtimes. The async/sync distinction is handled at the runtime level, not in the function signature. This avoids the "colored functions" problem seen in Rust and JavaScript.

### Per-Actor Heap Isolation

Inspired by Erlang's BEAM VM, each actor can have its own heap via `actor_heap.spl`. This provides:
- **Isolation:** Actor crash doesn't corrupt other actors' memory
- **Fast GC:** Per-actor GC pauses are microseconds, not milliseconds
- **Deterministic cleanup:** Actor death frees entire heap instantly

### Reductions-Based Scheduling

Borrowed from Erlang: actors get a fixed "reductions budget" per timeslice. Each message receive or function call costs 1 reduction. When budget exhausted, the actor yields cooperatively. This provides:
- **Fairness:** No actor can monopolize CPU
- **Latency:** Bounded per-actor execution time
- **Preemption:** Cooperative but enforced

### Structured Concurrency

Supervisor + Monitor + CancellationToken provide structured concurrency:
- Tasks are organized in supervision trees
- Parent crash terminates children
- CancellationToken propagates cancellation
- JoinSet/FuturesUnordered for task group management

---

## Cross-References

- **Cross-language patterns:** `doc/research/async_patterns_cross_language.md`
- **GC↔NoGC migration:** `doc/design/async_migration_guide.md`
- **Module parity:** `doc/design/gc_nogc_module_parity.md`
- **OTP stdlib:** `src/lib/nogc_async_mut/gen_server.spl`, `gen_statem.spl`, `gen_event.spl`
