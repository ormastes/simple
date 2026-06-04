# Cross-Language Async Patterns Research

**Date:** 2026-02-22
**Purpose:** Inform Simple language async design decisions by surveying async/concurrency patterns across major languages.
**Scope:** Memory management interaction, cancellation, scheduling, and structured concurrency.

---

## Table of Contents

1. [Introduction](#introduction)
2. [Rust](#rust)
3. [Go](#go)
4. [Erlang](#erlang)
5. [Swift](#swift)
6. [Kotlin](#kotlin)
7. [Zig](#zig)
8. [C++](#c20-coroutines)
9. [Python](#python)
10. [Cross-Cutting Comparison Tables](#cross-cutting-comparison-tables)
11. [Recommendations for Simple](#recommendations-for-simple)

---

## Introduction

Simple's async story must integrate with three distinct memory regimes (`nogc_sync_mut`,
`nogc_async_mut`, `gc_async_mut`) and the existing actor/mailbox model inherited from the
Erlang-inspired OTP layer (`src/lib/nogc_async_mut/`). This document surveys how nine
production languages handle the intersection of async execution, memory management, and
concurrency safety, then distills concrete recommendations for Simple.

Key questions this research answers:

- How should coroutine frames be allocated (heap, arena, stack, GC)?
- What cancellation model preserves resource safety without `try/catch`?
- How do actors and structured concurrency coexist?
- What can Simple borrow from each language without inheriting their mistakes?

---

## Rust

### Core Model: Pin + Future + Ownership

Rust async is built on three pillars: the `Future` trait, the `Pin` type, and ownership
rules that extend across `.await` points.

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// The Future trait - all async code compiles down to this
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

// An async fn desugars to a state machine implementing Future
async fn fetch_data(url: &str) -> Result<String, Error> {
    let response = client.get(url).await?;    // suspend point 1
    let body = response.text().await?;         // suspend point 2
    Ok(body)
}
```

### State Machine Compilation

The compiler transforms each `async fn` into an enum whose variants correspond to
suspension points. Local variables that live across `.await` boundaries are stored
in the enum, making the future self-contained.

```rust
// Conceptual desugaring of async fn fetch_data
enum FetchDataFuture<'a> {
    Start { url: &'a str },
    WaitingForResponse { url: &'a str, get_fut: GetFuture },
    WaitingForBody { response: Response, text_fut: TextFuture },
    Done,
}
```

### Pin and Self-Referential Futures

`Pin<&mut T>` guarantees the future will not be moved after first poll. This is
necessary because the state machine may contain self-referential pointers (e.g., a
reference to a local variable stored in a prior variant). Without `Pin`, moving the
future would invalidate these internal pointers.

**Implications for Simple:** Simple does not have Rust's move semantics. If Simple
adopts coroutine state machines, it must either (a) always heap-allocate frames,
(b) use arenas that outlive the coroutine, or (c) forbid self-referential captures.

### Ownership Across Await Points

Rust's borrow checker enforces that references held across `.await` must be valid for
the entire duration. This means `&mut` references cannot be held across suspension
points unless the referent is owned by the future itself.

```rust
async fn problematic(data: &mut Vec<u8>) {
    // OK: data is borrowed for the entire future's lifetime
    data.push(1);
    some_io().await;
    data.push(2);  // Still valid because the future holds the &mut borrow
}
```

### Cancel Safety

Dropping a future in Rust cancels it. This is zero-cost but creates a class of bugs
called "cancel safety" violations. If a future has performed partial work (e.g., read
half a message from a socket) and is dropped, that partial state is lost.

```rust
// Cancel-unsafe: dropping after partial read loses bytes
async fn read_message(stream: &mut TcpStream) -> Message {
    let len = stream.read_u32().await;    // If cancelled here...
    let body = stream.read_exact(len).await;  // ...len bytes are lost
    parse(body)
}

// Cancel-safe: uses a helper that tracks partial state
async fn read_message_safe(stream: &mut TcpStream, buf: &mut ReadBuf) -> Message {
    buf.read_until_complete(stream).await;
    parse(buf.take())
}
```

Tokio documents cancel safety for every async method. `tokio::select!` is the primary
source of implicit cancellation.

### Tokio Runtime

Tokio uses a work-stealing scheduler with per-core run queues. Each worker thread has
a local queue (LIFO for cache locality) and a global queue (FIFO for fairness).
Futures are heap-allocated via `Box<dyn Future>` when spawned with `tokio::spawn`.

**Key design decisions:**

| Aspect | Tokio Choice | Rationale |
|--------|-------------|-----------|
| Frame allocation | Heap (Box) | Futures are `'static`, no arena needed |
| Scheduling | Work-stealing M:N | Balances throughput and latency |
| Cancellation | Drop = cancel | Zero-cost, but requires cancel-safety discipline |
| I/O model | epoll/kqueue/io_uring | Platform-specific, hidden behind trait |
| Timer | Hierarchical wheel | O(1) insert/cancel |

---

## Go

### Goroutines and the GMP Scheduler

Go uses goroutines, which are lightweight green threads multiplexed onto OS threads
by the Go runtime scheduler. The scheduler follows the GMP model:

- **G** (Goroutine): The unit of work. Starts with a 2KB stack that grows dynamically.
- **M** (Machine): An OS thread. Goroutines execute on Ms.
- **P** (Processor): A logical processor. Each P has a local run queue. The number of
  Ps defaults to `GOMAXPROCS` (number of CPU cores).

```go
// Goroutines are trivially cheap to create
func main() {
    ch := make(chan int, 100)

    for i := 0; i < 1000; i++ {
        go worker(i, ch)  // 2KB initial stack each
    }

    for i := 0; i < 1000; i++ {
        <-ch
    }
}

func worker(id int, done chan<- int) {
    // Do work...
    done <- id
}
```

### Stack Management

Goroutine stacks start small (2-8KB) and grow by copying. When a goroutine's stack
needs to grow, the runtime allocates a new, larger stack, copies the old stack contents,
and updates all pointers. This is called "stack copying" and replaced the older
"segmented stacks" approach (which caused "hot split" performance problems).

**Cost:** Stack growth requires a write barrier and pointer adjustment pass. Functions
that might trigger growth have a preamble check. The amortized cost is low, but the
worst case (deep recursion with many pointers) can be expensive.

### GC Interaction

Go's garbage collector is a concurrent, tri-color, mark-sweep collector. It interacts
with goroutines in several ways:

1. **Write barriers:** Every pointer write goes through a write barrier during GC.
   Goroutines running concurrent code pay this cost continuously.
2. **Stack scanning:** The GC must scan all goroutine stacks to find roots. With
   millions of goroutines, this can be a pause source. Go 1.19+ uses a cooperative
   preemption mechanism (async preemption via signals) to scan stacks.
3. **Allocation pressure:** Each goroutine's allocations contribute to GC pressure.
   The GOGC parameter controls the heap growth ratio before GC triggers.

```go
// GC-unfriendly: millions of goroutines each holding references
func leakyPattern() {
    for {
        go func() {
            data := make([]byte, 1024)  // Allocated on heap, tracked by GC
            time.Sleep(time.Hour)        // Goroutine and data live for an hour
            _ = data
        }()
    }
}
```

### Goroutine Leaks

Go has no built-in mechanism to cancel or kill a goroutine externally. A goroutine
blocked on a channel read, mutex, or I/O operation will live until the process exits
unless explicitly unblocked. This is a major source of resource leaks.

**Common patterns to prevent leaks:**

```go
// Context-based cancellation (standard pattern)
func worker(ctx context.Context) {
    for {
        select {
        case <-ctx.Done():
            return  // Clean exit
        case item := <-workChan:
            process(item)
        }
    }
}

// Leak detection in tests
func TestNoLeaks(t *testing.T) {
    defer goleak.VerifyNone(t)  // uber-go/goleak
    // ... test code ...
}
```

**Implications for Simple:** Go's goroutine leak problem is a direct consequence of
lacking structured concurrency. Simple should learn from this and require explicit
lifetime scoping for spawned tasks.

---

## Erlang

### Per-Process GC

Erlang's most distinctive feature for async design is per-process garbage collection.
Each Erlang process (lightweight, ~300 bytes initial) has its own heap and its own GC.
When process A's heap fills up, only process A is paused for collection. All other
processes continue running.

```erlang
%% Each process has isolated memory
spawn(fun() ->
    %% This process has its own heap
    Data = lists:seq(1, 1000000),
    %% GC of this data only affects THIS process
    process_data(Data)
end).
```

### Message Passing and Mailboxes

All inter-process communication is via asynchronous message passing. Messages are
copied from the sender's heap to the receiver's heap (with a large binary optimization
that uses reference-counted shared binaries on a global heap).

```erlang
%% Sending copies data to receiver's heap
Pid ! {request, self(), "hello"},

%% Receiving pattern-matches against mailbox
receive
    {request, From, Msg} ->
        From ! {response, process(Msg)};
    {shutdown} ->
        ok
after 5000 ->
    timeout
end.
```

**Mailbox semantics:**

- Messages arrive in order from a single sender (no ordering across senders).
- Selective receive scans the mailbox for a matching pattern.
- Unmatched messages remain in the mailbox (potential memory leak if never consumed).
- `after` clause provides timeout-based cancellation.

### Supervision Trees

Erlang's "let it crash" philosophy is implemented through supervision trees. A
supervisor is a process that monitors child processes and restarts them according to
a strategy when they fail.

```erlang
%% Supervisor specification
init([]) ->
    SupFlags = #{
        strategy => one_for_one,   % Restart only the crashed child
        intensity => 5,            % Max 5 restarts
        period => 60               % ...in 60 seconds
    },
    Children = [
        #{id => worker1,
          start => {my_worker, start_link, []},
          restart => permanent,    % Always restart
          shutdown => 5000,        % 5s graceful shutdown
          type => worker}
    ],
    {ok, {SupFlags, Children}}.
```

**Restart strategies:**

| Strategy | Behavior |
|----------|----------|
| `one_for_one` | Restart only the failed child |
| `one_for_all` | Restart all children if any fails |
| `rest_for_one` | Restart the failed child and all children started after it |
| `simple_one_for_one` | Dynamic children, all same spec |

### BEAM Scheduler

The BEAM VM uses preemptive scheduling based on reduction counting. Each process gets
a budget of ~4000 reductions (roughly one reduction per function call). When the budget
is exhausted, the process is preempted and the scheduler picks the next runnable process.

**Scheduler properties:**

- One scheduler thread per CPU core (by default).
- Each scheduler has a run queue with priorities (max, high, normal, low).
- I/O polling is integrated into the scheduler loop (no separate I/O threads).
- Dirty schedulers handle long-running NIF calls without blocking normal schedulers.

**Implications for Simple:** Erlang's per-process heap maps directly to the
`ActorHeap` concept in Simple's `gc_async_mut` library. The key insight is that
per-task GC eliminates global GC pauses, which is critical for latency-sensitive
concurrent applications.

---

## Swift

### Structured Concurrency

Swift 5.5+ introduced structured concurrency where the lifetime of child tasks is
bounded by the scope that created them. This prevents task leaks by construction.

```swift
// TaskGroup: all children must complete before scope exits
func fetchAllImages(urls: [URL]) async throws -> [Image] {
    try await withThrowingTaskGroup(of: Image.self) { group in
        for url in urls {
            group.addTask {
                try await downloadImage(from: url)
            }
        }

        var images: [Image] = []
        for try await image in group {
            images.append(image)
        }
        return images
    }
    // All tasks guaranteed complete here
}
```

### Actors

Swift actors provide data-race safety through actor isolation. Each actor has a
serial executor that processes messages one at a time. Cross-actor calls require
`await` because they may suspend.

```swift
actor BankAccount {
    private var balance: Double = 0

    func deposit(_ amount: Double) {
        balance += amount  // No data race: actor-isolated
    }

    func getBalance() -> Double {
        balance
    }
}

// Cross-actor call requires await
let account = BankAccount()
await account.deposit(100)        // Suspends until actor processes this
let b = await account.getBalance()
```

### Sendable Protocol

`Sendable` is a marker protocol that indicates a type can be safely transferred
across concurrency domains (actor boundaries, task boundaries). The compiler enforces
that only `Sendable` types cross these boundaries.

```swift
// Value types are implicitly Sendable
struct Point: Sendable {
    var x: Double
    var y: Double
}

// Reference types must explicitly opt in
final class Config: Sendable {
    let host: String   // Only immutable stored properties allowed
    let port: Int
}

// Non-Sendable types cannot cross actor boundaries
class MutableState {
    var count = 0  // Mutable -> not Sendable
}

actor Worker {
    func process(_ p: Point) { }         // OK: Point is Sendable
    // func process(_ s: MutableState) { }  // ERROR: not Sendable
}
```

### ARC Interaction

Swift uses Automatic Reference Counting, not tracing GC. ARC interacts with async
code in several ways:

1. **Task frame retention:** The async frame (coroutine state) is heap-allocated
   and reference-counted. Captured values increment their retain count.
2. **Actor-isolated references:** References to actor-isolated state cannot escape
   the actor. The compiler prevents returning references to internal state.
3. **Cycle risk in closures:** Async closures that capture `self` can create retain
   cycles, just like synchronous closures. `[weak self]` is the standard mitigation.
4. **No stop-the-world:** ARC has no GC pauses, but retain/release traffic on hot
   paths (e.g., passing objects between tasks) can be a bottleneck.

```swift
class NetworkManager {
    func fetchData() async {
        // Potential retain cycle if self is captured strongly
        let task = Task { [weak self] in
            guard let self else { return }
            await self.process()
        }
    }
}
```

**Implications for Simple:** Swift's `Sendable` protocol maps well to Simple's
effect annotations. A `@send` or `@async` annotation on types could enforce the
same safety at the module boundary level.

---

## Kotlin

### Coroutines and CPS Transformation

Kotlin coroutines compile to a continuation-passing style (CPS) state machine. Each
`suspend` function receives an implicit `Continuation<T>` parameter. The compiler
transforms the function body into a state machine with labeled states at each
suspension point.

```kotlin
// Source code
suspend fun fetchUser(id: Int): User {
    val profile = api.getProfile(id)     // suspend point 1
    val avatar = api.getAvatar(id)       // suspend point 2
    return User(profile, avatar)
}

// Conceptual CPS transformation
fun fetchUser(id: Int, cont: Continuation<User>) {
    val sm = cont as? FetchUserSM ?: FetchUserSM(cont)
    when (sm.label) {
        0 -> {
            sm.label = 1
            api.getProfile(id, sm)  // Pass state machine as continuation
        }
        1 -> {
            sm.profile = sm.result as Profile
            sm.label = 2
            api.getAvatar(id, sm)
        }
        2 -> {
            sm.avatar = sm.result as Avatar
            sm.cont.resume(User(sm.profile, sm.avatar))
        }
    }
}
```

### Structured Concurrency

Kotlin's `coroutineScope` enforces that all launched coroutines complete before the
scope returns. Failure in any child cancels all siblings (structured cancellation).

```kotlin
suspend fun loadDashboard(): Dashboard = coroutineScope {
    val user = async { fetchUser() }           // Child 1
    val posts = async { fetchPosts() }         // Child 2
    val notifications = async { fetchNotifs() } // Child 3

    // All three must complete. If any throws, others are cancelled.
    Dashboard(user.await(), posts.await(), notifications.await())
}
// Scope exit guarantees: no leaked coroutines
```

### Channels and Flow

Kotlin provides channels (hot) and Flow (cold) for streaming data between coroutines.

```kotlin
// Channel: hot, buffer-based, multiple producers/consumers
val channel = Channel<Int>(capacity = 64)

launch { // Producer
    for (i in 1..100) channel.send(i)
    channel.close()
}

launch { // Consumer
    for (item in channel) process(item)
}

// Flow: cold, lazy, single collector
fun numbers(): Flow<Int> = flow {
    for (i in 1..100) {
        delay(100)
        emit(i)  // Suspend until collector is ready
    }
}

numbers()
    .filter { it % 2 == 0 }
    .map { it * it }
    .collect { println(it) }
```

### Dispatcher Model

Kotlin separates the coroutine execution policy from the coroutine itself via
dispatchers:

| Dispatcher | Thread Pool | Use Case |
|-----------|-------------|----------|
| `Dispatchers.Default` | Shared pool, size = CPU cores | CPU-bound work |
| `Dispatchers.IO` | Elastic pool, up to 64 threads | Blocking I/O |
| `Dispatchers.Main` | Single main thread | UI updates |
| `Dispatchers.Unconfined` | No dispatch, runs in caller's thread | Testing |

**Implications for Simple:** Kotlin's structured concurrency model is the most
directly applicable to Simple. The `coroutineScope`/`supervisorScope` distinction
maps to Simple's `Supervisor` with different restart policies.

---

## Zig

### Io Interface: No Function Coloring

Zig 0.14+ replaces its earlier `async`/`await` with the `Io` interface pattern.
Instead of colored functions (async vs sync), all I/O operations take an `io`
parameter. The caller decides whether execution is async or blocking.

```zig
// No function coloring: same function works sync or async
fn fetchData(io: *Io, url: []const u8) ![]u8 {
    const socket = try io.open_tcp(url);
    defer socket.close();

    try socket.write("GET / HTTP/1.1\r\n\r\n");
    return try socket.read_all();
}

// Caller decides execution mode
pub fn main() !void {
    // Blocking mode
    var io = Io.blocking();
    const data = try fetchData(&io, "example.com");

    // Or async mode with event loop
    var loop = EventLoop.init();
    var io_async = loop.io();
    const handle = try loop.spawn(fetchData, .{ &io_async, "example.com" });
    const data2 = try handle.join();
}
```

### Explicit Allocators

Every Zig function that allocates memory takes an explicit `allocator` parameter. This
extends to async frames: the coroutine frame's memory comes from whatever allocator
the caller provides.

```zig
const std = @import("std");

fn processItems(allocator: std.mem.Allocator, items: []const Item) !void {
    var results = std.ArrayList(Result).init(allocator);
    defer results.deinit();

    for (items) |item| {
        const result = try transform(allocator, item);
        try results.append(result);
    }
}
```

### Arena Fallback

Zig's `ArenaAllocator` wraps any backing allocator and provides bulk deallocation.
This is particularly useful for request-scoped or task-scoped work where individual
frees are unnecessary.

```zig
fn handleRequest(backing: std.mem.Allocator, request: Request) !Response {
    // Arena for all request-scoped allocations
    var arena = std.heap.ArenaAllocator.init(backing);
    defer arena.deinit();  // Frees everything at once

    const alloc = arena.allocator();

    // All allocations below use the arena
    const parsed = try parseBody(alloc, request.body);
    const validated = try validate(alloc, parsed);
    const response = try buildResponse(alloc, validated);

    return response;
}
```

**Key insight:** Arena-per-task is the allocation equivalent of Erlang's per-process
heap. When the task completes, the entire arena is freed in O(1). No GC, no reference
counting, no individual frees.

**Implications for Simple:** Zig's arena-per-task pattern maps directly to Simple's
`ActorHeap` with the `no_gc` preset. The explicit allocator pattern is too verbose for
Simple's syntax goals, but the arena lifetime can be implicit (tied to task scope).

---

## C++20 Coroutines

### Promise-Based Coroutine Framework

C++20 coroutines are the most flexible (and most complex) coroutine system in any
mainstream language. They are built on three customization points: the promise type,
the awaiter, and the coroutine handle.

```cpp
#include <coroutine>

// A minimal task type
template<typename T>
struct Task {
    struct promise_type {
        T value;
        Task get_return_object() {
            return Task{std::coroutine_handle<promise_type>::from_promise(*this)};
        }
        std::suspend_always initial_suspend() { return {}; }  // Lazy start
        std::suspend_always final_suspend() noexcept { return {}; }
        void return_value(T v) { value = v; }
        void unhandled_exception() { std::terminate(); }
    };

    std::coroutine_handle<promise_type> handle;

    T result() {
        handle.resume();
        return handle.promise().value;
    }

    ~Task() { if (handle) handle.destroy(); }
};

Task<int> compute() {
    co_return 42;  // Compiler generates state machine
}
```

### HALO: Heap Allocation eLision Optimization

The C++ standard permits compilers to elide the heap allocation of coroutine frames
when the compiler can prove the frame's lifetime is bounded by the caller. This is
called HALO (Heap Allocation eLision Optimization).

```cpp
// HALO-eligible: coroutine frame lifetime bounded by caller
Task<int> inner() {
    co_return 42;
}

Task<int> outer() {
    auto result = co_await inner();  // Compiler may allocate inner's frame on outer's frame
    co_return result + 1;
}
```

**Requirements for HALO:**

1. The coroutine frame size must be known at the call site.
2. The frame must not escape the calling coroutine's lifetime.
3. The compiler must be able to inline the coroutine creation.

In practice, HALO is unreliable. Most C++ coroutine frameworks assume heap allocation
and provide custom allocators as a fallback.

### Custom Promise Allocators

When HALO does not apply, C++20 coroutines allow custom allocation through the
promise type's `operator new`:

```cpp
template<typename T>
struct PooledTask {
    struct promise_type {
        // Custom allocator for coroutine frames
        static void* operator new(std::size_t size) {
            return frame_pool.allocate(size);
        }
        static void operator delete(void* ptr) {
            frame_pool.deallocate(ptr);
        }
        // ... rest of promise_type
    };
};
```

**Implications for Simple:** C++20 coroutines demonstrate that coroutine frame
allocation is a separable concern. Simple can default to arena allocation (like Zig)
while allowing override for special cases (like pooled allocation for high-frequency
coroutines).

---

## Python

### asyncio Event Loop

Python's `asyncio` module provides cooperative multitasking through an event loop.
Coroutines are defined with `async def` and suspended with `await`.

```python
import asyncio

async def fetch_data(url: str) -> str:
    reader, writer = await asyncio.open_connection(url, 80)
    writer.write(b"GET / HTTP/1.1\r\n\r\n")
    await writer.drain()
    data = await reader.read(4096)
    writer.close()
    await writer.wait_closed()
    return data.decode()

async def main():
    # Structured concurrency via TaskGroup (Python 3.11+)
    async with asyncio.TaskGroup() as tg:
        task1 = tg.create_task(fetch_data("example.com"))
        task2 = tg.create_task(fetch_data("python.org"))
    # Both tasks guaranteed done here
    print(task1.result(), task2.result())

asyncio.run(main())
```

### Event Loop Architecture

Python's event loop is single-threaded (by default) and uses `select`/`epoll`/`kqueue`
for I/O multiplexing. The loop cycles through:

1. Run all ready callbacks.
2. Poll for I/O events (with timeout based on next scheduled callback).
3. Run callbacks triggered by I/O.
4. Repeat.

```python
# The event loop is explicit and pluggable
loop = asyncio.new_event_loop()
loop.run_until_complete(main())

# Or use uvloop for higher performance (libuv-based)
import uvloop
asyncio.set_event_loop_policy(uvloop.EventLoopPolicy())
```

### GC Interaction with Coroutine Frames

Python uses reference counting with a cycle-detecting tracing GC. Coroutine frames
interact with GC in several problematic ways:

1. **Frame retention:** A suspended coroutine keeps its entire frame alive, including
   all local variables. Large objects referenced by locals are not collected until the
   coroutine completes or is explicitly closed.

2. **Cycle detection:** Coroutines that reference each other (e.g., producer-consumer
   pairs holding references) create cycles that require the cycle detector.

3. **`__del__` and coroutines:** If a coroutine is garbage-collected without being
   awaited, Python raises a `RuntimeWarning`. The coroutine's `close()` method is
   called by the GC, which runs `GeneratorExit` through the coroutine.

4. **Exception chains:** Exception objects in Python reference their traceback, which
   references the frame, which references all locals. Async tracebacks can create
   chains that keep large object graphs alive.

```python
async def memory_hazard():
    large_data = bytearray(100_000_000)  # 100MB
    await asyncio.sleep(3600)             # Held for 1 hour
    # large_data not collected until coroutine completes

async def cycle_hazard():
    async def producer(consumer_ref):
        # producer holds ref to consumer, consumer holds ref to producer
        await consumer_ref.send(data)

    # Cycle: producer <-> consumer
```

### TaskGroup (Python 3.11+)

Python 3.11 added `asyncio.TaskGroup`, inspired by Trio's nurseries and Kotlin's
`coroutineScope`. It provides structured concurrency guarantees:

```python
async def main():
    async with asyncio.TaskGroup() as tg:
        tg.create_task(task_a())
        tg.create_task(task_b())
    # If either task raises, both are cancelled
    # Scope exit guarantees all tasks complete
```

**Implications for Simple:** Python demonstrates the cost of retrofitting async onto a
GC language. The interaction between coroutine frames and GC creates subtle memory
retention bugs. Simple should design the async-GC interaction from the start.

---

## Cross-Cutting Comparison Tables

### Memory Model x Async

How each language allocates and manages coroutine/task state:

| Language | Frame Allocation | Deallocation | GC Interaction | Self-Referential |
|----------|-----------------|--------------|----------------|------------------|
| **Rust** | Heap (Box) via spawn; stack-possible for non-spawned | Drop (deterministic) | None (no GC) | Pin required |
| **Go** | Stack (growable, 2KB initial) | GC sweeps goroutine stacks | Stacks are GC roots; scanned at safepoints | N/A (no raw pointers) |
| **Erlang** | Per-process heap | Per-process GC | Isolated; no cross-process GC pause | N/A (immutable data) |
| **Swift** | Heap (ARC) | ARC release at scope exit | None (ARC, not tracing GC) | Weak refs for cycles |
| **Kotlin** | Heap (JVM objects) | JVM GC | Coroutine objects are normal GC roots | N/A (JVM manages) |
| **Zig** | Caller-provided allocator | Explicit free or arena bulk free | None (no GC) | Not applicable |
| **C++** | Heap (operator new) or HALO elision | Coroutine handle destroy | None (no GC in core) | Promise-managed |
| **Python** | Heap (GC-tracked frame) | Refcount + cycle GC | Frame retains all locals; cycle risk | N/A (GC handles) |
| **Simple** | **Proposed: Arena per task** | **Arena bulk free at task exit** | **Per-task GC (gc_async_mut) or no GC (nogc_async_mut)** | **Forbidden** |

### Cancellation Comparison Matrix

| Language | Cancellation Mechanism | Cooperative? | Resource Cleanup | Partial Work Handling |
|----------|----------------------|-------------|------------------|----------------------|
| **Rust** | Drop the Future | Cooperative (drop at await) | Drop trait runs | Cancel-safety is manual |
| **Go** | `context.Context` | Cooperative (must check `ctx.Done()`) | `defer` statements | Manual; no enforcement |
| **Erlang** | `exit(Pid, Reason)` | Preemptive (process killed) | Supervisor restarts | Message queue drained |
| **Swift** | `Task.cancel()` / `withTaskCancellationHandler` | Cooperative (check `Task.isCancelled`) | `defer`/`withTaskCancellationHandler` | Manual check required |
| **Kotlin** | `Job.cancel()` | Cooperative (check `isActive`) | `finally` blocks run | `ensureActive()` checkpoints |
| **Zig** | Caller stops calling `io` methods | Cooperative (no resume = cancelled) | `defer`/`errdefer` | Caller manages state |
| **C++** | Destroy coroutine handle | Cooperative (at co_await) | Promise destructor | RAII in frame |
| **Python** | `Task.cancel()` raises `CancelledError` | Cooperative (at await points) | `try/finally`, `async with` | `CancelledError` propagation |
| **Simple** | **Proposed: `CancellationToken` + supervisor** | **Cooperative (at await/receive)** | **Arena free (bulk) + resource cleanup hooks** | **Supervisor restart policy** |

### Actor Model Comparison

| Aspect | Erlang | Swift | Simple (Proposed) |
|--------|--------|-------|-------------------|
| **Isolation Unit** | Process (lightweight, 300B) | Actor (class-like, heap-allocated) | Actor (maps to ActorHeap) |
| **Mailbox** | Unbounded, selective receive | Serial executor queue | Bounded, configurable capacity |
| **Message Passing** | Copy semantics (data copied between heaps) | Sendable types only (compiler-checked) | Copy for nogc_async_mut; shared ref for gc_async_mut |
| **Scheduling** | Preemptive (reduction counting) | Cooperative (Swift concurrency runtime) | Cooperative with yield budgets |
| **State Access** | Only via message passing | Actor-isolated (compiler enforced) | `@async` effect annotation on types |
| **Failure Handling** | Supervision trees, "let it crash" | Task cancellation, structured concurrency | Supervisor + CancellationToken |
| **GC Impact** | Per-process GC, no global pauses | ARC, no GC pauses | Per-actor-heap GC or arena (no GC) |
| **Backpressure** | Manual (bounded channels) | Automatic (serial executor) | Configurable mailbox capacity |
| **Hot Code Reload** | Built-in (code server) | Not supported | Not yet designed |
| **Distribution** | Built-in (Erlang distribution) | Not built-in | Not yet designed |

---

## Recommendations for Simple

Based on the cross-language analysis, the following four design pillars are recommended
for Simple's async system. Each maps to existing or planned Simple infrastructure.

### 1. Per-Task Isolation (Erlang-Style)

**Mapping:** `src/lib/gc_async_mut/` and `actor_heap.spl`

Erlang's per-process heap eliminates global GC pauses and provides natural fault
isolation. Simple should adopt this pattern for the `gc_async_mut` memory regime.

**Design:**

```simple
# Each actor/task gets its own heap
# GC of one actor does not pause others
actor CounterActor:
    var count: i64 = 0

    receive Increment(n: i64):
        count = count + n

    receive GetCount(reply: Mailbox<i64>):
        reply.send(count)
```

**Key properties:**

- Each actor's heap is independently collected.
- Message passing between actors copies data (small messages) or transfers ownership
  (large buffers, zero-copy for `nogc_async_mut`).
- Actor crash does not corrupt other actors' heaps.
- Supervisor can restart a failed actor with a fresh heap.

**What to borrow from Erlang:**

| Feature | Borrow? | Rationale |
|---------|---------|-----------|
| Per-process heap | Yes | Core design for `gc_async_mut` |
| Selective receive | Yes (simplified) | Pattern matching on mailbox messages |
| Supervision trees | Yes | Maps to `Supervisor` with restart strategies |
| Reduction-based preemption | No | Too complex; use cooperative yield |
| Distributed actors | Defer | Not needed for initial async design |
| Hot code reload | Defer | Complex; revisit after stable release |

### 2. Arenas (Zig-Style)

**Mapping:** `ActorHeap` with `no_gc` preset in `src/lib/nogc_async_mut/`

For the `nogc_async_mut` memory regime, arena allocation provides deterministic,
zero-overhead memory management. All allocations within a task scope use the arena;
when the task completes, the entire arena is freed in O(1).

**Design:**

```simple
# Arena-scoped task: all allocations freed when scope exits
fn handle_request(request: Request) -> Response:
    # Implicit arena tied to task scope
    val parsed = parse_body(request.body)
    val validated = validate(parsed)
    val response = build_response(validated)
    response
    # Arena freed here: O(1), no individual frees
```

**Arena lifecycle rules:**

1. Arena is created when a task is spawned.
2. All allocations within the task use the arena by default.
3. Data that must outlive the task is explicitly `promote`d to the parent scope.
4. When the task completes (or is cancelled), the arena is freed in bulk.
5. No finalizers run on arena-allocated objects (they are just memory).

**What to borrow from Zig:**

| Feature | Borrow? | Rationale |
|---------|---------|-----------|
| Explicit allocator parameter | No | Too verbose for Simple's ergonomics |
| Arena allocator | Yes | Core design for nogc tasks |
| `defer`/`errdefer` | Partially | Simple has no exceptions; use scope-exit hooks |
| No function coloring (Io pattern) | Defer | Interesting but requires deeper runtime changes |
| Comptime execution | Already have | `comptime val` already implemented |

### 3. Sendable (Swift-Style)

**Mapping:** `effects.spl` with `@async` annotation in `src/compiler/00.common/`

Swift's `Sendable` protocol prevents data races by ensuring only safe types cross
actor boundaries. Simple should adopt an effect-based version of this.

**Design:**

```simple
# @async annotation marks types safe for cross-task transfer
@async
struct Config:
    host: text
    port: i64

# Mutable types cannot be @async unless wrapped
# var fields prevent @async annotation
struct MutableState:
    var count: i64  # Cannot be @async: mutable

# Effect annotation on functions
@async
fn fetch_data(url: text) -> text:
    # This function can be called from any task
    pass_todo
```

**Enforcement rules:**

1. Only `@async`-annotated types can be sent via `Mailbox.send()`.
2. Immutable value types (`val` fields only) are implicitly `@async`.
3. Mutable types require explicit wrapping (e.g., `AtomicRef<T>` or actor encapsulation).
4. The compiler checks `@async` safety at module boundaries using the existing
   effect system.

**What to borrow from Swift:**

| Feature | Borrow? | Rationale |
|---------|---------|-----------|
| `Sendable` protocol | Yes (as `@async` effect) | Prevents data races at compile time |
| Actor isolation | Yes (simplified) | Maps to actor-scoped state |
| Structured concurrency (TaskGroup) | Yes | See recommendation 4 |
| ARC for coroutine frames | No | Simple uses arenas or per-task GC |
| Global actors (`@MainActor`) | Defer | Relevant for UI, not initial design |

### 4. Structured Concurrency (Kotlin-Style)

**Mapping:** `Supervisor` + `CancellationToken` in `src/lib/nogc_async_mut/`

Kotlin's structured concurrency ensures that all child tasks complete before their
parent scope exits, and that cancellation propagates from parent to children. This
eliminates task leaks (Go's goroutine leak problem) by construction.

**Design:**

```simple
# TaskScope: all spawned tasks must complete before scope exits
fn load_dashboard(user_id: i64) -> Dashboard:
    task_scope:
        val user = spawn fetch_user(user_id)
        val posts = spawn fetch_posts(user_id)
        val notifs = spawn fetch_notifications(user_id)

        Dashboard(
            user: user.await(),
            posts: posts.await(),
            notifications: notifs.await()
        )
    # Scope exit: all tasks guaranteed complete
    # If any task fails, siblings are cancelled

# Supervisor: long-lived scope with restart policy
fn start_server():
    supervisor(strategy: one_for_one, max_restarts: 5):
        spawn_permanent http_listener()
        spawn_permanent db_pool()
        spawn_transient metrics_reporter()
```

**Cancellation model:**

```simple
# CancellationToken: cooperative cancellation
fn long_running_task(cancel: CancellationToken):
    var batch = 0
    while not cancel.requested?:
        val items = fetch_batch(batch)
        process(items)
        batch = batch + 1
    # Clean exit when cancelled

# Timeout-based cancellation
fn with_timeout():
    val result = timeout(5000):
        expensive_computation()
    match result:
        Some(v): use(v)
        nil: handle_timeout()
```

**What to borrow from Kotlin:**

| Feature | Borrow? | Rationale |
|---------|---------|-----------|
| `coroutineScope` | Yes (as `task_scope`) | Structured concurrency primitive |
| `supervisorScope` | Yes (as `supervisor`) | Fault isolation for long-lived scopes |
| `Job` hierarchy | Yes (simplified) | Parent-child task relationships |
| `CancellationException` | No (no exceptions) | Use `CancellationToken` + nil returns |
| `Dispatchers` | Partially | Separate CPU-bound vs I/O pools |
| `Flow` | Defer | Streaming can come later |
| Channels | Yes | Already have `Mailbox` infrastructure |

### Summary: Integrated Design

The four recommendations combine into a coherent async architecture:

```
+--------------------------------------------------+
|                  Simple Async                     |
+--------------------------------------------------+
|                                                   |
|  Structured Concurrency (Kotlin)                  |
|  +--------------------------------------------+  |
|  | task_scope / supervisor                     |  |
|  | - Child tasks bounded by parent scope       |  |
|  | - Cancellation propagates down              |  |
|  | - CancellationToken (cooperative)           |  |
|  +--------------------------------------------+  |
|                                                   |
|  Actor Isolation (Erlang + Swift)                 |
|  +--------------------------------------------+  |
|  | actor Foo:                                  |  |
|  |   receive Bar(x): ...                       |  |
|  | - Per-actor heap (gc_async_mut)             |  |
|  | - Per-actor arena (nogc_async_mut)          |  |
|  | - @async types for cross-actor safety       |  |
|  +--------------------------------------------+  |
|                                                   |
|  Memory Model                                     |
|  +--------------------------------------------+  |
|  | gc_async_mut:   Per-actor tracing GC        |  |
|  | nogc_async_mut: Per-task arena, bulk free   |  |
|  | nogc_sync_mut:  No async (synchronous only) |  |
|  +--------------------------------------------+  |
|                                                   |
+--------------------------------------------------+
```

**Module mapping:**

| Concept | File/Module | Status |
|---------|------------|--------|
| Actor definition | `src/lib/nogc_async_mut/actors/` | Exists (basic) |
| Mailbox | `src/std/mailbox.spl` | Exists |
| Supervisor | `src/std/gen_server.spl` | Exists (basic) |
| CancellationToken | `src/lib/nogc_async_mut/` | To implement |
| TaskScope | `src/lib/nogc_async_mut/` | To implement |
| ActorHeap (arena) | `src/lib/gc_async_mut/` | To implement |
| @async effect | `src/compiler/00.common/effects.spl` | To implement |
| Io interface (Zig-style) | Deferred | Future consideration |

### Anti-Patterns to Avoid

Lessons from other languages on what NOT to do:

1. **Do NOT adopt Go's unstructured goroutines.** Goroutine leaks are Go's most
   persistent concurrency bug. Always require explicit scope bounding.

2. **Do NOT adopt Rust's Pin complexity.** Pin exists because Rust allows
   self-referential types. Simple should forbid self-referential coroutine captures
   and avoid the problem entirely.

3. **Do NOT adopt Python's retrofit approach.** Python added async to an existing GC
   runtime, creating frame retention and cycle issues. Simple should design the
   async-GC interaction from the start (per-task heaps).

4. **Do NOT adopt C++'s promise-type complexity.** C++20 coroutines require ~100 lines
   of boilerplate for a basic task type. Simple should provide built-in task types with
   sensible defaults.

5. **Do NOT adopt function coloring without escape hatch.** If Simple distinguishes
   async and sync functions, provide a way to call async from sync (like Zig's Io
   pattern or Kotlin's `runBlocking`). Total function coloring without bridging creates
   ecosystem splits.

---

## References

- Rust async book: https://rust-lang.github.io/async-book/
- Tokio documentation: https://tokio.rs/tokio/tutorial
- Go scheduler design: https://go.dev/src/runtime/proc.go
- Erlang/OTP design principles: https://www.erlang.org/doc/design_principles
- Swift concurrency manifesto: https://github.com/apple/swift-evolution/blob/main/proposals/0296-async-await.md
- Kotlin coroutines guide: https://kotlinlang.org/docs/coroutines-guide.html
- Zig 0.14 Io redesign: https://github.com/ziglang/zig/issues/17017
- C++20 coroutines: https://en.cppreference.com/w/cpp/language/coroutines
- Python asyncio: https://docs.python.org/3/library/asyncio.html
- Lewis Baker, "C++ Coroutines: Understanding Symmetric Transfer"
- Nathaniel J. Smith, "Notes on structured concurrency" (Trio)
