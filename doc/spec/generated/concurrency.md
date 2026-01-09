# Simple Language Concurrency - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/concurrency_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/concurrency_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** concurrency.md
**Note:** This is a test extraction file. For complete specification text,

## Overview

This file contains executable test cases extracted from concurrency.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/concurrency.md

---

## Test Cases (24 total)

| Test | Section | Description |
|------|---------|-------------|
| [actors_processes_1](#test-1) | Actors (Processes) | spawn: Creates a new process: |
| [actors_processes_2](#test-2) | Actors (Processes) | send: Sends an asynchronous message to a process: |
| [actors_processes_3](#test-3) | Actors (Processes) | receive: Waits for messages using pattern matching: |
| [ping](#test-4) | Actors (Processes) | ```simple... |
| [handle](#test-5) | Async Effects and Stackless Coroutine Actors | A `async` function is guaranteed by the compiler not to bloc... |
| [async_effects_and_stackless_coroutine_actors_6](#test-6) | Async Effects and Stackless Coroutine Actors | Allowed loops (must be statically finite): |
| [async_effects_and_stackless_coroutine_actors_7](#test-7) | Async Effects and Stackless Coroutine Actors | Call rule: A `async` function may only call other `async` fu... |
| [async_effects_and_stackless_coroutine_actors_8](#test-8) | Async Effects and Stackless Coroutine Actors | Multi-step behavior is modeled by storing state in `self` fi... |
| [isolated_threads_9](#test-9) | Isolated Threads | 1. No shared mutable state - Cannot access mutable globals... |
| [isolated_threads_10](#test-10) | Isolated Threads | \| Data Type \| Reason \|... |
| [futures_and_promises_11](#test-11) | Futures and Promises | In threaded mode, futures execute in a background thread poo... |
| [futures_and_promises_12](#test-12) | Futures and Promises | Configure the thread pool size: |
| [futures_and_promises_13](#test-13) | Futures and Promises | For embedded systems or game loops where you need precise co... |
| [futures_and_promises_14](#test-14) | Futures and Promises | \| Function \| Description \|... |
| [futures_and_promises_15](#test-15) | Futures and Promises | ```simple... |
| [fetch_data](#test-16) | Futures and Promises | ```simple... |
| [futures_and_promises_17](#test-17) | Futures and Promises | \| Combinator \| Description \|... |
| [futures_and_promises_18](#test-18) | Futures and Promises | ```simple... |
| [unnamed_test](#test-19) | Futures and Promises | on FetchData(key: String, reply_to: Pid) async:... |
| [runtime_guards_20](#test-20) | Runtime Guards | When entering a `async` function, the runtime sets a thread-... |
| [sleep](#test-21) | Runtime Guards | All blocking APIs check this flag: |
| [failure_handling_22](#test-22) | Failure Handling | In Erlang style, processes can monitor or link to each other... |
| [failure_handling_23](#test-23) | Failure Handling | Supervisors can restart crashed processes: |
| [note_on_semantic_types_24](#test-24) | Note on Semantic Types | Actor message types and handler signatures should use semant... |

---

### Test 1: Actors (Processes)

*Source line: ~9*

**Test name:** `actors_processes_1`

**Description:**

spawn: Creates a new process:

**Code:**

```simple
test "actors_processes_1":
    let pid = spawn(fn():
        do_work()
        send(self(), :done)
    )
    assert_compiles()
```

### Test 2: Actors (Processes)

*Source line: ~18*

**Test name:** `actors_processes_2`

**Description:**

send: Sends an asynchronous message to a process:

**Code:**

```simple
test "actors_processes_2":
    send(pid, "hello")
    send(pid, Msg(data))
    assert_compiles()
```

### Test 3: Actors (Processes)

*Source line: ~27*

**Test name:** `actors_processes_3`

**Description:**

receive: Waits for messages using pattern matching:

**Code:**

```simple
test "actors_processes_3":
    receive:
        case "ping":
            print "pong"
        case ("add", x, y):
            print "{x} + {y} = {x+y}"
        case Msg(data):
            handle_data(data)
        case _:
            print "Got something"
    assert_compiles()
```

### Test 4: Actors (Processes)

*Source line: ~41*

**Test name:** `ping`

**Description:**

```simple
receive:
    case "ping":
        print "pong"
    case ("add", x, y):
        print "{x} ...

**Code:**

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

### Test 5: Async Effects and Stackless Coroutine Actors

*Source line: ~9*

**Test name:** `handle`

**Description:**

A `async` function is guaranteed by the compiler not to block or spin forever:

**Code:**

```simple
fn handle(msg: Msg) async:
    # guaranteed non-blocking
    ...
```

### Test 6: Async Effects and Stackless Coroutine Actors

*Source line: ~27*

**Test name:** `async_effects_and_stackless_coroutine_actors_6`

**Description:**

Allowed loops (must be statically finite):

**Code:**

```simple
test "async_effects_and_stackless_coroutine_actors_6":
    # OK: constant-bounded range
    for i in 0 .. 100:
        process(i)

    # OK: fixed-size array iteration
    let items: [i64; 10] = ...
    for elem in items:
        handle(elem)
    assert_compiles()
```

### Test 7: Async Effects and Stackless Coroutine Actors

*Source line: ~49*

**Test name:** `async_effects_and_stackless_coroutine_actors_7`

**Description:**

Call rule: A `async` function may only call other `async` functions or whitelisted intrinsics.

**Code:**

```simple
test "async_effects_and_stackless_coroutine_actors_7":
    actor Counter:
        state:
            value: i64 = 0

        on Inc(by: i64) async:
            self.value = self.value + by

        on Get(reply_to: Pid[i64]) async:
            send reply_to, self.value

        on Reset() async:
            self.value = 0
    assert_compiles()
```

### Test 8: Async Effects and Stackless Coroutine Actors

*Source line: ~81*

**Test name:** `async_effects_and_stackless_coroutine_actors_8`

**Description:**

Multi-step behavior is modeled by storing state in `self` fields (state machines):

**Code:**

```simple
test "async_effects_and_stackless_coroutine_actors_8":
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
    assert_compiles()
```

### Test 9: Isolated Threads

*Source line: ~14*

**Test name:** `isolated_threads_9`

**Description:**

1. No shared mutable state - Cannot access mutable globals
2. Copy or const only - Data must be copi...

**Code:**

```simple
test "isolated_threads_9":
    let data = [1, 2, 3, 4, 5]
    let result_channel = Channel[i64].new()

    spawn_isolated(data, result_channel) \copied_data, chan:
        let sum = copied_data.sum()
        chan.send(sum)

    let total = result_channel.recv()
    assert_compiles()
```

### Test 10: Isolated Threads

*Source line: ~46*

**Test name:** `isolated_threads_10`

**Description:**

| Data Type | Reason |
|-----------|--------|
| Mutable globals | Would create data races |
| `stati...

**Code:**

```simple
test "isolated_threads_10":
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
    assert_compiles()
```

### Test 11: Futures and Promises

*Source line: ~18*

**Test name:** `futures_and_promises_11`

**Description:**

In threaded mode, futures execute in a background thread pool similar to JavaScript's event loop. Wh...

**Code:**

```simple
test "futures_and_promises_11":
    # Futures run in background automatically
    let f1 = future(expensive_computation())
    let f2 = future(fetch_data())

    # await blocks until the future completes
    let result1 = await f1
    let result2 = await f2
    assert_compiles()
```

### Test 12: Futures and Promises

*Source line: ~30*

**Test name:** `futures_and_promises_12`

**Description:**

Configure the thread pool size:

**Code:**

```simple
test "futures_and_promises_12":
    async_workers(8)  # Use 8 worker threads
    assert_compiles()
```

### Test 13: Futures and Promises

*Source line: ~38*

**Test name:** `futures_and_promises_13`

**Description:**

For embedded systems or game loops where you need precise control over when async work executes, use...

**Code:**

```simple
test "futures_and_promises_13":
    # Set manual mode before creating any futures
    async_mode("manual")

    # Create futures - they don't execute yet
    let f1 = future(compute_physics())
    let f2 = future(update_ai())

    # In your main loop, poll futures explicitly
    fn game_loop():
        while running:
            # Poll individual futures
            poll_future(f1)
            poll_future(f2)

            # Or poll all pending futures
            poll_all_futures()

            # Check results
            if is_ready(f1):
                let physics = await f1

            render()
    assert_compiles()
```

### Test 14: Futures and Promises

*Source line: ~77*

**Test name:** `futures_and_promises_14`

**Description:**

| Function | Description |
|----------|-------------|
| `async_mode()` | Get current mode ("threaded...

**Code:**

```simple
test "futures_and_promises_14":
    enum FutureState:
        Pending     # Not started
        Running     # Currently executing
        Fulfilled   # Completed successfully
        Rejected    # Completed with error
    assert_compiles()
```

### Test 15: Futures and Promises

*Source line: ~87*

**Test name:** `futures_and_promises_15`

**Description:**

```simple
enum FutureState:
    Pending     # Not started
    Running     # Currently executing
    ...

**Code:**

```simple
test "futures_and_promises_15":
    # Create a future that computes a value
    let f = future(compute_value())

    # Create an already-resolved future
    let resolved = resolved(42)

    # Create an already-rejected future
    let rejected = rejected("error message")

    # Check if a future is ready
    if is_ready(f):
        let result = await f
    assert_compiles()
```

### Test 16: Futures and Promises

*Source line: ~104*

**Test name:** `fetch_data`

**Description:**

```simple
# Create a future that computes a value
let f = future(compute_value())

**Code:**

```simple
fn fetch_data() async -> Data:
    let response = await http_get("https://api.example.com")
    return parse(response)
```

### Test 17: Futures and Promises

*Source line: ~124*

**Test name:** `futures_and_promises_17`

**Description:**

| Combinator | Description |
|------------|-------------|
| `then` | Transform result |
| `catch` | ...

**Code:**

```simple
test "futures_and_promises_17":
    let futures = [get_a(), get_b(), get_c()]
    let all_results = Future.all(futures)
    let first = Future.race(futures)
    let first_success = Future.any(futures)
    assert_compiles()
```

### Test 18: Futures and Promises

*Source line: ~133*

**Test name:** `futures_and_promises_18`

**Description:**

```simple
let futures = [get_a(), get_b(), get_c()]
let all_results = Future.all(futures)
let first ...

**Code:**

```simple
test "futures_and_promises_18":
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
    assert_compiles()
```

### Test 19: Futures and Promises

*Source line: ~149*

**Test name:** `unnamed_test`

**Description:**

on FetchData(key: String, reply_to: Pid) async:
        if key in self.cache:
            send reply...

**Code:**

```simple
fn request<T>(pid: Pid, msg: Msg) async -> T:
    let (future, promise) = promise<T>()
    send pid, Request(msg, promise)
    return await future

let result = await request(service_pid, GetData("key"))
```

### Test 20: Runtime Guards

*Source line: ~7*

**Test name:** `runtime_guards_20`

**Description:**

When entering a `async` function, the runtime sets a thread-local flag:

**Code:**

```simple
test "runtime_guards_20":
    TLS.current_context = Context.Async
    assert_compiles()
```

### Test 21: Runtime Guards

*Source line: ~13*

**Test name:** `sleep`

**Description:**

All blocking APIs check this flag:

**Code:**

```simple
fn sleep(ms: i64):
    if TLS.current_context == Context.Async:
        panic("sleep() called from async context")
```

### Test 22: Failure Handling

*Source line: ~5*

**Test name:** `failure_handling_22`

**Description:**

In Erlang style, processes can monitor or link to each other:

**Code:**

```simple
test "failure_handling_22":
    # Link processes (crash propagation)
    link(pid)

    # Monitor process (receive notification on crash)
    let monitor_ref = monitor(pid)

    receive:
        case Down(ref, pid, reason) if ref == monitor_ref:
            print "Process {pid} died: {reason}"
    assert_compiles()
```

### Test 23: Failure Handling

*Source line: ~19*

**Test name:** `failure_handling_23`

**Description:**

Supervisors can restart crashed processes:

**Code:**

```simple
test "failure_handling_23":
    actor Supervisor:
        state:
            workers: List[Pid] = []

        on WorkerCrashed(pid: Pid, reason: Error) async:
            # Restart the worker
            let new_pid = spawn_worker()
            self.workers->replace(pid, new_pid)
    assert_compiles()
```

### Test 24: Note on Semantic Types

*Source line: ~5*

**Test name:** `note_on_semantic_types_24`

**Description:**

Actor message types and handler signatures should use semantic types:

**Code:**

```simple
test "note_on_semantic_types_24":
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
    assert_compiles()
```

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/concurrency_spec.spl`*
