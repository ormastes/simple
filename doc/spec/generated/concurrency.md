# Simple Language Concurrency - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/concurrency_spec.spl`
> **Generated:** 2026-01-10 04:47:40
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/concurrency_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** concurrency.md
**Note:** This is a test extraction file. For complete specification text,

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (24 tests)
- [Source Code](#source-code)

## Overview

This file contains executable test cases extracted from concurrency.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/concurrency.md

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `Actors` | [1](#actors_processes_1), [2](#actors_processes_2), [3](#actors_processes_3), [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), ... (6 total) |
| `ActorsProcesses` | [1](#actors_processes_1), [2](#actors_processes_2), [3](#actors_processes_3) |
| `And` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8), [11](#futures_and_promises_11), [12](#futures_and_promises_12), ... (10 total) |
| `Async` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8), [20](#runtime_guards_20), [21](#sleep) |
| `AsyncEffectsAndStacklessCoroutineActors` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `Bytes` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `Channel` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `Check` | [13](#futures_and_promises_13), [15](#futures_and_promises_15) |
| `Completed` | [14](#futures_and_promises_14) |
| `Consumer` | [10](#isolated_threads_10) |
| `Context` | [20](#runtime_guards_20), [21](#sleep) |
| `Coroutine` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `Counter` | [7](#async_effects_and_stackless_coroutine_actors_7) |
| `Create` | [13](#futures_and_promises_13), [15](#futures_and_promises_15) |
| `Currently` | [14](#futures_and_promises_14) |
| `Damage` | [24](#note_on_semantic_types_24) |
| `DamageEnemy` | [24](#note_on_semantic_types_24) |
| `Data` | [8](#async_effects_and_stackless_coroutine_actors_8), [16](#fetch_data), [18](#futures_and_promises_18) |
| `DataService` | [18](#futures_and_promises_18) |
| `Dict` | [18](#futures_and_promises_18) |
| `Done` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `Down` | [22](#failure_handling_22) |
| `Effects` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `EnemyId` | [24](#note_on_semantic_types_24) |
| `Error` | [23](#failure_handling_23) |
| `Failure` | [22](#failure_handling_22), [23](#failure_handling_23) |
| `FailureHandling` | [22](#failure_handling_22), [23](#failure_handling_23) |
| `Fetch` | [16](#fetch_data) |
| `FetchData` | [16](#fetch_data), [18](#futures_and_promises_18) |
| `Fulfilled` | [14](#futures_and_promises_14) |
| `Future` | [17](#futures_and_promises_17) |
| `FutureState` | [14](#futures_and_promises_14) |
| `Futures` | [11](#futures_and_promises_11), [12](#futures_and_promises_12), [13](#futures_and_promises_13), [14](#futures_and_promises_14), [15](#futures_and_promises_15), ... (7 total) |
| `FuturesAndPromises` | [11](#futures_and_promises_11), [12](#futures_and_promises_12), [13](#futures_and_promises_13), [14](#futures_and_promises_14), [15](#futures_and_promises_15), ... (7 total) |
| `GameWorld` | [24](#note_on_semantic_types_24) |
| `Get` | [7](#async_effects_and_stackless_coroutine_actors_7) |
| `GetData` | [19](#unnamed_test) |
| `Got` | [3](#actors_processes_3) |
| `Guards` | [20](#runtime_guards_20) |
| `Handle` | [5](#handle) |
| `Handling` | [22](#failure_handling_22), [23](#failure_handling_23) |
| `HitPoints` | [24](#note_on_semantic_types_24) |
| `Inc` | [7](#async_effects_and_stackless_coroutine_actors_7) |
| `Isolated` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `IsolatedThreads` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `Link` | [22](#failure_handling_22) |
| `List` | [23](#failure_handling_23) |
| `Message` | [24](#note_on_semantic_types_24) |
| `Monitor` | [22](#failure_handling_22) |
| `Msg` | [2](#actors_processes_2), [3](#actors_processes_3), [5](#handle), [19](#unnamed_test) |
| `Not` | [14](#futures_and_promises_14), [24](#note_on_semantic_types_24) |
| `Note` | [24](#note_on_semantic_types_24) |
| `NoteOnSemanticTypes` | [24](#note_on_semantic_types_24) |
| `ParserMode` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `Pending` | [14](#futures_and_promises_14) |
| `Pid` | [7](#async_effects_and_stackless_coroutine_actors_7), [18](#futures_and_promises_18), [19](#unnamed_test), [23](#failure_handling_23) |
| `Ping` | [4](#ping) |
| `Poll` | [13](#futures_and_promises_13) |
| `Pong` | [4](#ping) |
| `Position` | [24](#note_on_semantic_types_24) |
| `Process` | [22](#failure_handling_22) |
| `Processes` | [1](#actors_processes_1), [2](#actors_processes_2), [3](#actors_processes_3) |
| `Producer` | [10](#isolated_threads_10) |
| `Promises` | [11](#futures_and_promises_11), [12](#futures_and_promises_12), [13](#futures_and_promises_13), [14](#futures_and_promises_14), [15](#futures_and_promises_15), ... (7 total) |
| `ReadingBody` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `ReadingHeader` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `Rejected` | [14](#futures_and_promises_14) |
| `Request` | [19](#unnamed_test) |
| `Reset` | [7](#async_effects_and_stackless_coroutine_actors_7) |
| `Restart` | [23](#failure_handling_23) |
| `Running` | [14](#futures_and_promises_14) |
| `Runtime` | [20](#runtime_guards_20) |
| `RuntimeGuards` | [20](#runtime_guards_20) |
| `Semantic` | [24](#note_on_semantic_types_24) |
| `Set` | [13](#futures_and_promises_13) |
| `Sleep` | [21](#sleep) |
| `SpawnEnemy` | [24](#note_on_semantic_types_24) |
| `Stackless` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `StreamParser` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `String` | [18](#futures_and_promises_18) |
| `Supervisor` | [23](#failure_handling_23) |
| `TLS` | [20](#runtime_guards_20), [21](#sleep) |
| `Threads` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `Types` | [24](#note_on_semantic_types_24) |
| `Unnamed` | [19](#unnamed_test) |
| `Use` | [12](#futures_and_promises_12) |
| `WorkerCrashed` | [23](#failure_handling_23) |
| `actors` | [1](#actors_processes_1), [2](#actors_processes_2), [3](#actors_processes_3), [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), ... (6 total) |
| `actors_processes` | [1](#actors_processes_1), [2](#actors_processes_2), [3](#actors_processes_3) |
| `all` | [17](#futures_and_promises_17) |
| `and` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8), [11](#futures_and_promises_11), [12](#futures_and_promises_12), ... (10 total) |
| `any` | [17](#futures_and_promises_17) |
| `append` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `assert_compiles` | [1](#actors_processes_1), [2](#actors_processes_2), [3](#actors_processes_3), [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), ... (19 total) |
| `async` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `async_effects_and_stackless_coroutine_actors` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `async_mode` | [13](#futures_and_promises_13) |
| `async_workers` | [12](#futures_and_promises_12) |
| `body_complete` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `case` | [3](#actors_processes_3) |
| `close` | [10](#isolated_threads_10) |
| `compute_physics` | [13](#futures_and_promises_13) |
| `compute_value` | [15](#futures_and_promises_15) |
| `coroutine` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `data` | [16](#fetch_data) |
| `do_work` | [1](#actors_processes_1) |
| `effects` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `empty` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `expensive_computation` | [11](#futures_and_promises_11) |
| `failure` | [22](#failure_handling_22), [23](#failure_handling_23) |
| `failure_handling` | [22](#failure_handling_22), [23](#failure_handling_23) |
| `fetch` | [16](#fetch_data) |
| `fetch_data` | [11](#futures_and_promises_11), [16](#fetch_data) |
| `fetch_from_remote` | [18](#futures_and_promises_18) |
| `future` | [11](#futures_and_promises_11), [13](#futures_and_promises_13), [15](#futures_and_promises_15) |
| `futures` | [11](#futures_and_promises_11), [12](#futures_and_promises_12), [13](#futures_and_promises_13), [14](#futures_and_promises_14), [15](#futures_and_promises_15), ... (7 total) |
| `futures_and_promises` | [11](#futures_and_promises_11), [12](#futures_and_promises_12), [13](#futures_and_promises_13), [14](#futures_and_promises_14), [15](#futures_and_promises_15), ... (7 total) |
| `game_loop` | [13](#futures_and_promises_13) |
| `get_a` | [17](#futures_and_promises_17) |
| `get_b` | [17](#futures_and_promises_17) |
| `get_c` | [17](#futures_and_promises_17) |
| `guards` | [20](#runtime_guards_20) |
| `handle` | [5](#handle), [6](#async_effects_and_stackless_coroutine_actors_6) |
| `handle_data` | [3](#actors_processes_3) |
| `handling` | [22](#failure_handling_22), [23](#failure_handling_23) |
| `header_complete` | [8](#async_effects_and_stackless_coroutine_actors_8) |
| `http_get` | [16](#fetch_data) |
| `is_ready` | [13](#futures_and_promises_13), [15](#futures_and_promises_15) |
| `isolated` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `isolated_threads` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `let` | [19](#unnamed_test) |
| `link` | [22](#failure_handling_22) |
| `monitor` | [22](#failure_handling_22) |
| `new` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `note` | [24](#note_on_semantic_types_24) |
| `note_on_semantic_types` | [24](#note_on_semantic_types_24) |
| `panic` | [21](#sleep) |
| `parse` | [16](#fetch_data) |
| `ping` | [4](#ping) |
| `poll_all_futures` | [13](#futures_and_promises_13) |
| `poll_future` | [13](#futures_and_promises_13) |
| `pong` | [4](#ping) |
| `process` | [6](#async_effects_and_stackless_coroutine_actors_6), [22](#failure_handling_22) |
| `processes` | [1](#actors_processes_1), [2](#actors_processes_2), [3](#actors_processes_3), [22](#failure_handling_22) |
| `promises` | [11](#futures_and_promises_11), [12](#futures_and_promises_12), [13](#futures_and_promises_13), [14](#futures_and_promises_14), [15](#futures_and_promises_15), ... (7 total) |
| `race` | [17](#futures_and_promises_17) |
| `range` | [4](#ping) |
| `recv` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `rejected` | [15](#futures_and_promises_15) |
| `render` | [13](#futures_and_promises_13) |
| `replace` | [23](#failure_handling_23) |
| `request` | [19](#unnamed_test) |
| `resolved` | [15](#futures_and_promises_15) |
| `runtime` | [20](#runtime_guards_20) |
| `runtime_guards` | [20](#runtime_guards_20) |
| `self` | [1](#actors_processes_1) |
| `semantic` | [24](#note_on_semantic_types_24) |
| `send` | [1](#actors_processes_1), [2](#actors_processes_2), [4](#ping), [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `sender` | [4](#ping) |
| `sleep` | [21](#sleep) |
| `spawn` | [1](#actors_processes_1), [4](#ping) |
| `spawn_isolated` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `spawn_worker` | [23](#failure_handling_23) |
| `stackless` | [6](#async_effects_and_stackless_coroutine_actors_6), [7](#async_effects_and_stackless_coroutine_actors_7), [8](#async_effects_and_stackless_coroutine_actors_8) |
| `sum` | [9](#isolated_threads_9) |
| `threads` | [9](#isolated_threads_9), [10](#isolated_threads_10) |
| `types` | [24](#note_on_semantic_types_24) |
| `unnamed` | [19](#unnamed_test) |
| `update_ai` | [13](#futures_and_promises_13) |

---

## Test Cases (24 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [actors_processes_1](#actors_processes_1) | Actors (Processes) | `Actors`, `actors_processes`, `Processes` +8 |
| 2 | [actors_processes_2](#actors_processes_2) | Actors (Processes) | `Actors`, `actors_processes`, `Processes` +6 |
| 3 | [actors_processes_3](#actors_processes_3) | Actors (Processes) | `Actors`, `actors_processes`, `Processes` +8 |
| 4 | [ping](#ping) | Actors (Processes) | `Ping`, `ping`, `Pong` +5 |
| 5 | [handle](#handle) | Async Effects and Stackless Coroutine Actors | `handle`, `Handle`, `Msg` |
| 6 | [async_effects_and_stackless_coroutine_actors_6](#async_effects_and_stackless_coroutine_actors_6) | Async Effects and Stackless Coroutine Actors | `Stackless`, `stackless`, `and` +14 |
| 7 | [async_effects_and_stackless_coroutine_actors_7](#async_effects_and_stackless_coroutine_actors_7) | Async Effects and Stackless Coroutine Actors | `Stackless`, `stackless`, `and` +17 |
| 8 | [async_effects_and_stackless_coroutine_actors_8](#async_effects_and_stackless_coroutine_actors_8) | Async Effects and Stackless Coroutine Actors | `Stackless`, `stackless`, `and` +23 |
| 9 | [isolated_threads_9](#isolated_threads_9) | Isolated Threads | `IsolatedThreads`, `threads`, `isolated_threads` +10 |
| 10 | [isolated_threads_10](#isolated_threads_10) | Isolated Threads | `IsolatedThreads`, `threads`, `isolated_threads` +12 |
| 11 | [futures_and_promises_11](#futures_and_promises_11) | Futures and Promises | `FuturesAndPromises`, `and`, `Futures` +9 |
| 12 | [futures_and_promises_12](#futures_and_promises_12) | Futures and Promises | `FuturesAndPromises`, `and`, `Futures` +8 |
| 13 | [futures_and_promises_13](#futures_and_promises_13) | Futures and Promises | `FuturesAndPromises`, `and`, `Futures` +19 |
| 14 | [futures_and_promises_14](#futures_and_promises_14) | Futures and Promises | `FuturesAndPromises`, `and`, `Futures` +14 |
| 15 | [futures_and_promises_15](#futures_and_promises_15) | Futures and Promises | `FuturesAndPromises`, `and`, `Futures` +13 |
| 16 | [fetch_data](#fetch_data) | Futures and Promises | `Fetch`, `FetchData`, `data` +5 |
| 17 | [futures_and_promises_17](#futures_and_promises_17) | Futures and Promises | `FuturesAndPromises`, `and`, `Futures` +13 |
| 18 | [futures_and_promises_18](#futures_and_promises_18) | Futures and Promises | `FuturesAndPromises`, `and`, `Futures` +13 |
| 19 | [unnamed_test](#unnamed_test) | Futures and Promises | `unnamed`, `Unnamed`, `Pid` +5 |
| 20 | [runtime_guards_20](#runtime_guards_20) | Runtime Guards | `Guards`, `RuntimeGuards`, `runtime_guards` +7 |
| 21 | [sleep](#sleep) | Runtime Guards | `Sleep`, `sleep`, `Context` +3 |
| 22 | [failure_handling_22](#failure_handling_22) | Failure Handling | `failure_handling`, `FailureHandling`, `failure` +12 |
| 23 | [failure_handling_23](#failure_handling_23) | Failure Handling | `failure_handling`, `FailureHandling`, `failure` +12 |
| 24 | [note_on_semantic_types_24](#note_on_semantic_types_24) | Note on Semantic Types | `types`, `Types`, `Note` +15 |

---

### Test 1: Actors (Processes) {#actors_processes_1}

*Source line: ~9*

**Test name:** `actors_processes_1`

**Description:**

spawn: Creates a new process:

**Linked Symbols:**
- `Actors`
- `actors_processes`
- `Processes`
- `processes`
- `actors`
- `ActorsProcesses`
- `send`
- `assert_compiles`
- `do_work`
- `self`
- ... and 1 more

**Code:**

```simple
test "actors_processes_1":
    let pid = spawn(fn():
        do_work()
        send(self(), :done)
    )
    assert_compiles()
```

### Test 2: Actors (Processes) {#actors_processes_2}

*Source line: ~18*

**Test name:** `actors_processes_2`

**Description:**

send: Sends an asynchronous message to a process:

**Linked Symbols:**
- `Actors`
- `actors_processes`
- `Processes`
- `processes`
- `actors`
- `ActorsProcesses`
- `assert_compiles`
- `Msg`
- `send`

**Code:**

```simple
test "actors_processes_2":
    send(pid, "hello")
    send(pid, Msg(data))
    assert_compiles()
```

### Test 3: Actors (Processes) {#actors_processes_3}

*Source line: ~27*

**Test name:** `actors_processes_3`

**Description:**

receive: Waits for messages using pattern matching:

**Linked Symbols:**
- `Actors`
- `actors_processes`
- `Processes`
- `processes`
- `actors`
- `ActorsProcesses`
- `case`
- `assert_compiles`
- `Msg`
- `Got`
- ... and 1 more

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

### Test 4: Actors (Processes) {#ping}

*Source line: ~41*

**Test name:** `ping`

**Description:**

```simple
receive:
    case "ping":
        print "pong"
    case ("add", x, y):
        print "{x} ...

**Linked Symbols:**
- `Ping`
- `ping`
- `Pong`
- `send`
- `range`
- `pong`
- `sender`
- `spawn`

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

### Test 5: Async Effects and Stackless Coroutine Actors {#handle}

*Source line: ~9*

**Test name:** `handle`

**Description:**

A `async` function is guaranteed by the compiler not to block or spin forever:

**Linked Symbols:**
- `handle`
- `Handle`
- `Msg`

**Code:**

```simple
fn handle(msg: Msg) async:
    # guaranteed non-blocking
    ...
```

### Test 6: Async Effects and Stackless Coroutine Actors {#async_effects_and_stackless_coroutine_actors_6}

*Source line: ~27*

**Test name:** `async_effects_and_stackless_coroutine_actors_6`

**Description:**

Allowed loops (must be statically finite):

**Linked Symbols:**
- `Stackless`
- `stackless`
- `and`
- `coroutine`
- `Actors`
- `And`
- `effects`
- `AsyncEffectsAndStacklessCoroutineActors`
- `Effects`
- `Async`
- ... and 7 more

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

### Test 7: Async Effects and Stackless Coroutine Actors {#async_effects_and_stackless_coroutine_actors_7}

*Source line: ~49*

**Test name:** `async_effects_and_stackless_coroutine_actors_7`

**Description:**

Call rule: A `async` function may only call other `async` functions or whitelisted intrinsics.

**Linked Symbols:**
- `Stackless`
- `stackless`
- `and`
- `coroutine`
- `Actors`
- `And`
- `effects`
- `AsyncEffectsAndStacklessCoroutineActors`
- `Effects`
- `Async`
- ... and 10 more

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

### Test 8: Async Effects and Stackless Coroutine Actors {#async_effects_and_stackless_coroutine_actors_8}

*Source line: ~81*

**Test name:** `async_effects_and_stackless_coroutine_actors_8`

**Description:**

Multi-step behavior is modeled by storing state in `self` fields (state machines):

**Linked Symbols:**
- `Stackless`
- `stackless`
- `and`
- `coroutine`
- `Actors`
- `And`
- `effects`
- `AsyncEffectsAndStacklessCoroutineActors`
- `Effects`
- `Async`
- ... and 16 more

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

### Test 9: Isolated Threads {#isolated_threads_9}

*Source line: ~14*

**Test name:** `isolated_threads_9`

**Description:**

1. No shared mutable state - Cannot access mutable globals
2. Copy or const only - Data must be copi...

**Linked Symbols:**
- `IsolatedThreads`
- `threads`
- `isolated_threads`
- `isolated`
- `Threads`
- `Isolated`
- `new`
- `send`
- `sum`
- `assert_compiles`
- ... and 3 more

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

### Test 10: Isolated Threads {#isolated_threads_10}

*Source line: ~46*

**Test name:** `isolated_threads_10`

**Description:**

| Data Type | Reason |
|-----------|--------|
| Mutable globals | Would create data races |
| `stati...

**Linked Symbols:**
- `IsolatedThreads`
- `threads`
- `isolated_threads`
- `isolated`
- `Threads`
- `Isolated`
- `new`
- `Consumer`
- `send`
- `close`
- ... and 5 more

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

### Test 11: Futures and Promises {#futures_and_promises_11}

*Source line: ~18*

**Test name:** `futures_and_promises_11`

**Description:**

In threaded mode, futures execute in a background thread pool similar to JavaScript's event loop. Wh...

**Linked Symbols:**
- `FuturesAndPromises`
- `and`
- `Futures`
- `And`
- `futures`
- `promises`
- `Promises`
- `futures_and_promises`
- `future`
- `assert_compiles`
- ... and 2 more

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

### Test 12: Futures and Promises {#futures_and_promises_12}

*Source line: ~30*

**Test name:** `futures_and_promises_12`

**Description:**

Configure the thread pool size:

**Linked Symbols:**
- `FuturesAndPromises`
- `and`
- `Futures`
- `And`
- `futures`
- `promises`
- `Promises`
- `futures_and_promises`
- `Use`
- `async_workers`
- ... and 1 more

**Code:**

```simple
test "futures_and_promises_12":
    async_workers(8)  # Use 8 worker threads
    assert_compiles()
```

### Test 13: Futures and Promises {#futures_and_promises_13}

*Source line: ~38*

**Test name:** `futures_and_promises_13`

**Description:**

For embedded systems or game loops where you need precise control over when async work executes, use...

**Linked Symbols:**
- `FuturesAndPromises`
- `and`
- `Futures`
- `And`
- `futures`
- `promises`
- `Promises`
- `futures_and_promises`
- `Poll`
- `compute_physics`
- ... and 12 more

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

### Test 14: Futures and Promises {#futures_and_promises_14}

*Source line: ~77*

**Test name:** `futures_and_promises_14`

**Description:**

| Function | Description |
|----------|-------------|
| `async_mode()` | Get current mode ("threaded...

**Linked Symbols:**
- `FuturesAndPromises`
- `and`
- `Futures`
- `And`
- `futures`
- `promises`
- `Promises`
- `futures_and_promises`
- `FutureState`
- `Rejected`
- ... and 7 more

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

### Test 15: Futures and Promises {#futures_and_promises_15}

*Source line: ~87*

**Test name:** `futures_and_promises_15`

**Description:**

```simple
enum FutureState:
    Pending     # Not started
    Running     # Currently executing
    ...

**Linked Symbols:**
- `FuturesAndPromises`
- `and`
- `Futures`
- `And`
- `futures`
- `promises`
- `Promises`
- `futures_and_promises`
- `is_ready`
- `Check`
- ... and 6 more

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

### Test 16: Futures and Promises {#fetch_data}

*Source line: ~104*

**Test name:** `fetch_data`

**Description:**

```simple
# Create a future that computes a value
let f = future(compute_value())

**Linked Symbols:**
- `Fetch`
- `FetchData`
- `data`
- `fetch`
- `Data`
- `fetch_data`
- `parse`
- `http_get`

**Code:**

```simple
fn fetch_data() async -> Data:
    let response = await http_get("https://api.example.com")
    return parse(response)
```

### Test 17: Futures and Promises {#futures_and_promises_17}

*Source line: ~124*

**Test name:** `futures_and_promises_17`

**Description:**

| Combinator | Description |
|------------|-------------|
| `then` | Transform result |
| `catch` | ...

**Linked Symbols:**
- `FuturesAndPromises`
- `and`
- `Futures`
- `And`
- `futures`
- `promises`
- `Promises`
- `futures_and_promises`
- `get_b`
- `assert_compiles`
- ... and 6 more

**Code:**

```simple
test "futures_and_promises_17":
    let futures = [get_a(), get_b(), get_c()]
    let all_results = Future.all(futures)
    let first = Future.race(futures)
    let first_success = Future.any(futures)
    assert_compiles()
```

### Test 18: Futures and Promises {#futures_and_promises_18}

*Source line: ~133*

**Test name:** `futures_and_promises_18`

**Description:**

```simple
let futures = [get_a(), get_b(), get_c()]
let all_results = Future.all(futures)
let first ...

**Linked Symbols:**
- `FuturesAndPromises`
- `and`
- `Futures`
- `And`
- `futures`
- `promises`
- `Promises`
- `futures_and_promises`
- `Pid`
- `DataService`
- ... and 6 more

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

### Test 19: Futures and Promises {#unnamed_test}

*Source line: ~149*

**Test name:** `unnamed_test`

**Description:**

on FetchData(key: String, reply_to: Pid) async:
        if key in self.cache:
            send reply...

**Linked Symbols:**
- `unnamed`
- `Unnamed`
- `Pid`
- `GetData`
- `request`
- `let`
- `Request`
- `Msg`

**Code:**

```simple
fn request<T>(pid: Pid, msg: Msg) async -> T:
    let (future, promise) = promise<T>()
    send pid, Request(msg, promise)
    return await future

let result = await request(service_pid, GetData("key"))
```

### Test 20: Runtime Guards {#runtime_guards_20}

*Source line: ~7*

**Test name:** `runtime_guards_20`

**Description:**

When entering a `async` function, the runtime sets a thread-local flag:

**Linked Symbols:**
- `Guards`
- `RuntimeGuards`
- `runtime_guards`
- `Runtime`
- `runtime`
- `guards`
- `Async`
- `assert_compiles`
- `Context`
- `TLS`

**Code:**

```simple
test "runtime_guards_20":
    TLS.current_context = Context.Async
    assert_compiles()
```

### Test 21: Runtime Guards {#sleep}

*Source line: ~13*

**Test name:** `sleep`

**Description:**

All blocking APIs check this flag:

**Linked Symbols:**
- `Sleep`
- `sleep`
- `Context`
- `TLS`
- `Async`
- `panic`

**Code:**

```simple
fn sleep(ms: i64):
    if TLS.current_context == Context.Async:
        panic("sleep() called from async context")
```

### Test 22: Failure Handling {#failure_handling_22}

*Source line: ~5*

**Test name:** `failure_handling_22`

**Description:**

In Erlang style, processes can monitor or link to each other:

**Linked Symbols:**
- `failure_handling`
- `FailureHandling`
- `failure`
- `handling`
- `Failure`
- `Handling`
- `process`
- `Down`
- `assert_compiles`
- `monitor`
- ... and 5 more

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

### Test 23: Failure Handling {#failure_handling_23}

*Source line: ~19*

**Test name:** `failure_handling_23`

**Description:**

Supervisors can restart crashed processes:

**Linked Symbols:**
- `failure_handling`
- `FailureHandling`
- `failure`
- `handling`
- `Failure`
- `Handling`
- `Pid`
- `Error`
- `assert_compiles`
- `replace`
- ... and 5 more

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

### Test 24: Note on Semantic Types {#note_on_semantic_types_24}

*Source line: ~5*

**Test name:** `note_on_semantic_types_24`

**Description:**

Actor message types and handler signatures should use semantic types:

**Linked Symbols:**
- `types`
- `Types`
- `Note`
- `NoteOnSemanticTypes`
- `note`
- `Semantic`
- `note_on_semantic_types`
- `semantic`
- `DamageEnemy`
- `EnemyId`
- ... and 8 more

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

## Source Code

**View full specification:** [concurrency_spec.spl](../../tests/specs/concurrency_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/concurrency_spec.spl`*
