# Simple Language Concurrency

This document covers the actor model, async/await, isolated threads, futures, and concurrency primitives.

## Overview

Simple adopts a message-passing concurrency model inspired by Erlang's actor model. Instead of shared mutable threads, concurrency is achieved by spawning lightweight processes (actors) that communicate via immutable messages. This model greatly simplifies writing concurrent programs by eliminating data races and locking concerns.

> Implementation note: Compiled actors call runtime FFI for spawn/send/recv, but actor bodies are still a no-op stub until `body_block` outlining is added. The interpreter runs full actor bodies.

---

## Actors (Processes)

### Key Primitives

**Process (Actor)**: An independent thread of execution (managed by the runtime as a green thread or fiber) that does not share memory with other processes. Processes are extremely lightweight, allowing many to run concurrently.

**spawn**: Creates a new process:

```simple
let pid = spawn(fn():
    do_work()
    send(self(), :done)
)
```

**send**: Sends an asynchronous message to a process:

```simple
send(pid, "hello")
send(pid, Msg(data))
```

Sending is non-blocking - the sender continues immediately. Messages must be immutable data (value types, immutable structs, enums).

**receive**: Waits for messages using pattern matching:

```simple
receive:
    case "ping":
        print "pong"
    case ("add", x, y):
        print "{x} + {y} = {x+y}"
    case Msg(data):
        handle_data(data)
    case _:
        print "Got something"
```

### Example: Ping-Pong

```simple
fn ping(pong_pid, count: i32):
    for i in range(count):
        send(pong_pid, "ping")
        receive:
            case "pong":
                print "Ping received pong"
    print "Ping finished"

fn pong():
    loop:
        receive:
            case "ping":
                print "Pong received ping"
                send(sender(), "pong")
            case :done:
                print "Pong finished"
                break loop

let pong_pid = spawn(fn(): pong())
spawn(fn(): ping(pong_pid, count: 3))
send(pong_pid, :done)
```

### Immutability in Concurrency

Only immutable (or deeply copied) data is allowed in messages. This eliminates shared mutable state between processes, preventing data races. This follows the Erlang/Elixir philosophy: "share nothing, communicate by messages".

---

## Async Effects and Stackless Coroutine Actors

Simple provides specialized actors optimized for high-performance, predictable execution: **stackless coroutine actors** with **async** message handlers.

### The Async Effect

A `async` function is guaranteed by the compiler not to block or spin forever:

```simple
fn handle(msg: Msg) async:
    # guaranteed non-blocking
    ...
```

**Forbidden in async functions**:

| Construct | Reason |
|-----------|--------|
| `await` | Suspends execution |
| `receive` | Blocks waiting for messages |
| Blocking I/O | Can stall indefinitely |
| Direct recursion | Cannot prove termination |
| Unbounded loops | Cannot prove termination |

**Allowed loops** (must be statically finite):

```simple
# OK: constant-bounded range
for i in 0 .. 100:
    process(i)

# OK: fixed-size array iteration
let items: [i64; 10] = ...
for elem in items:
    handle(elem)
```

### Effect Classification

| Effect | Description |
|--------|-------------|
| `async` | Statically checked to be non-blocking |
| `may_block` | Default; can perform any operation |

**Call rule**: A `async` function may only call other `async` functions or whitelisted intrinsics.

### Stackless Coroutine Actors

```simple
actor Counter:
    state:
        value: i64 = 0

    on Inc(by: i64) async:
        self.value = self.value + by

    on Get(reply_to: Pid[i64]) async:
        send reply_to, self.value

    on Reset() async:
        self.value = 0
```

**Semantics**:

- `actor Name:` defines an actor type
- `state:` block declares actor-local fields
- `on MessageType(...) async:` defines message handlers
- Every handler must be `async` (guaranteed non-blocking)

### Stackless and Run-to-Completion

Each incoming message is processed by calling the corresponding handler:

1. Handler runs on the current execution stack
2. Must not suspend (`await`, `receive`, blocking API)
3. Must return to the runtime when done

Multi-step behavior is modeled by storing state in `self` fields (state machines):

```simple
enum ParserMode:
    ReadingHeader
    ReadingBody
    Done

actor StreamParser:
    state:
        mode: ParserMode = ParserMode.ReadingHeader
        buffer: Bytes = Bytes.empty()

    on Data(chunk: Bytes) async:
        match self.mode:
            case ReadingHeader:
                self.buffer->append(chunk)
                if header_complete(self.buffer):
                    self.mode = ParserMode.ReadingBody
            case ReadingBody:
                self.buffer->append(chunk)
                if body_complete(self.buffer):
                    self.mode = ParserMode.Done
            case Done:
                pass
```

---

## Isolated Threads

Simple provides **isolated threads** for safe, parallel execution without shared mutable state.

### Core Principles

1. **No shared mutable state** - Cannot access mutable globals
2. **Copy or const only** - Data must be copied or const
3. **Channel-only communication** - Use channels for inter-thread communication
4. **Global const access** - Can read global constants

### Spawning Isolated Threads

```simple
let data = [1, 2, 3, 4, 5]
let result_channel = Channel[i64].new()

spawn_isolated(data, result_channel) \copied_data, chan:
    let sum = copied_data.sum()
    chan.send(sum)

let total = result_channel.recv()
```

### Data Access Rules

**Allowed**:

| Data Type | Access | Reason |
|-----------|--------|--------|
| `const` globals | Read | Truly immutable |
| Copied values | Read/Write | Thread owns copy |
| Channels | Send/Recv | Thread-safe communication |
| Thread-local state | Read/Write | No sharing |

**Forbidden**:

| Data Type | Reason |
|-----------|--------|
| Mutable globals | Would create data races |
| `static mut` variables | Shared mutable state |
| Non-const references | Could alias mutable data |

### Channel Communication

```simple
let numbers = Channel[i64].new()
let results = Channel[str].new()

# Producer thread
spawn_isolated(numbers) \out:
    for i in 0..100:
        out.send(i)
    out.close()

# Consumer thread
spawn_isolated(numbers, results) \inp, out:
    while let Some(n) = inp.recv():
        out.send("processed: {n}")
    out.close()

for msg in results:
    print msg
```

### Comparison: Actors vs Isolated Threads

| Feature | Actors | Isolated Threads |
|---------|--------|------------------|
| Execution | Cooperative (green threads) | Preemptive (OS threads) |
| State | Actor-local state | No persistent state |
| Communication | Message passing | Channels |
| Use case | Many lightweight tasks | CPU-bound parallelism |
| Blocking | Discouraged (async) | Allowed |

---

## Futures and Promises

Simple provides TypeScript-style async/await for asynchronous computations.

### Future Type

```simple
enum Future<T>:
    Pending
    Running
    Resolved(T)
    Rejected(Error)
```

### Promise Type

```simple
let (future, promise) = promise<i64>()

# Later, resolve or reject
promise.resolve(42)
# or
promise.reject(Error("Something went wrong"))
```

### Async/Await Syntax

```simple
fn fetch_data() async -> Data:
    let response = await http_get("https://api.example.com")
    return parse(response)
```

`await` can only be used inside `async` functions.

### Future Combinators

| Combinator | Description |
|------------|-------------|
| `then` | Transform result |
| `catch` | Handle errors |
| `finally` | Always execute |
| `all` | Wait for all (reject if any rejects) |
| `race` | First to complete |
| `any` | First success |
| `all_settled` | Wait for all (no short-circuit) |

```simple
let futures = [get_a(), get_b(), get_c()]
let all_results = Future.all(futures)
let first = Future.race(futures)
let first_success = Future.any(futures)
```

### Integration with Actors

```simple
actor DataService:
    state:
        cache: Dict<String, Data> = {}

    on FetchData(key: String, reply_to: Pid) async:
        if key in self.cache:
            send reply_to, self.cache[key]
        else:
            let data = await fetch_from_remote(key)
            self.cache[key] = data
            send reply_to, data
```

### Request-Response Pattern

```simple
fn request<T>(pid: Pid, msg: Msg) async -> T:
    let (future, promise) = promise<T>()
    send pid, Request(msg, promise)
    return await future

let result = await request(service_pid, GetData("key"))
```

---

## Runtime Guards

### TLS Context Flag

When entering a `async` function, the runtime sets a thread-local flag:

```simple
TLS.current_context = Context.Async
```

All blocking APIs check this flag:

```simple
fn sleep(ms: i64):
    if TLS.current_context == Context.Async:
        panic("sleep() called from async context")
```

### Stack Depth Counter

Runtime maintains a recursion-depth counter:

- On function entry: `depth++`
- On exit: `depth--`
- If `depth > threshold` → panic

### Time Slice Watchdog

Optional scheduler monitoring:

1. Track instruction count/wall-clock time per handler
2. If budget exceeded: log, preempt, or kill/restart actor

---

## Failure Handling

In Erlang style, processes can monitor or link to each other:

```simple
# Link processes (crash propagation)
link(pid)

# Monitor process (receive notification on crash)
let monitor_ref = monitor(pid)

receive:
    case Down(ref, pid, reason) if ref == monitor_ref:
        print "Process {pid} died: {reason}"
```

Supervisors can restart crashed processes:

```simple
actor Supervisor:
    state:
        workers: List[Pid] = []

    on WorkerCrashed(pid: Pid, reason: Error) async:
        # Restart the worker
        let new_pid = spawn_worker()
        self.workers->replace(pid, new_pid)
```

---

## Summary

| Model | Use Case | Blocking | State |
|-------|----------|----------|-------|
| Standard Actors | General concurrency | With receive | Actor-local |
| Stackless Actors | High-performance, predictable | Never | Actor-local |
| Isolated Threads | CPU-bound parallelism | Allowed | No persistent |
| Async/Await | Asynchronous I/O | With await | Function-local |

---

## Note on Semantic Types

Actor message types and handler signatures should use semantic types:

```simple
# Message types with semantic fields
struct SpawnEnemy:
    pos: Position        # Not (f64, f64)
    hp: HitPoints        # Not i32

struct DamageEnemy:
    target: EnemyId      # Not i64
    amount: Damage       # Not i32

actor GameWorld:
    on SpawnEnemy(msg: SpawnEnemy) async:
        ...

    on DamageEnemy(msg: DamageEnemy) async:
        ...
```

See [Unit Types](units.md) for the complete type safety policy.

---

## Related Specifications

- [Memory and Ownership](memory.md)
- [Functions](functions.md)
- [Data Structures](data_structures.md)
- [Unit Types](units.md)
