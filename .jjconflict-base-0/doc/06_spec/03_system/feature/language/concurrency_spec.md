# Simple Language Concurrency - Test Specification

> This spec covers Simple's concurrency model: actor-based message passing, async-by-default functions, stackless coroutines, futures/promises, and runtime guards for blocking calls and thread isolation.

<!-- sdn-diagram:id=concurrency_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrency_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrency_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrency_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Concurrency - Test Specification

This spec covers Simple's concurrency model: actor-based message passing, async-by-default functions, stackless coroutines, futures/promises, and runtime guards for blocking calls and thread isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #200-230 |
| Category | Other |
| Status | Executable coverage |
| Type | Extracted Examples (Category B) |
| Reference | concurrency.md |
| Source | `test/03_system/feature/language/concurrency_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec covers Simple's concurrency model: actor-based message passing,
async-by-default functions, stackless coroutines, futures/promises, and
runtime guards for blocking calls and thread isolation.

24 test cases covering actors/processes, async effects, futures/promises,
runtime guards, and failure handling with supervisor restarts.

## Syntax

Spawn an actor and send typed messages:

    actor ! Message("hello")
    actor.receive() -> Reply

Async function (default — returns Promise automatically):

    fn fetch(id: i64) -> i64:
        val data = get_data(id)
        data.value

Sync function (explicit opt-out of async):

    sync fn compute(x: i64) -> i64:
        x * 2

## Examples

### Actors and message passing

    val actor = spawn_actor("worker")
    val count = send_message(2)   # => 3
    val reply = receive_message("alpha")   # => "alpha"
    val rounds = ping_pong_rounds(2)   # => 4 (2 actors * 2)

### Futures and promises

    val result = fetch_data(5)          # => 12  (5 + 7)
    val mapped = future_map_then(10)    # => 30  ((10+5)*2)
    val svc    = data_service_request(7) # => 107

### Runtime guards

    check(tls_context_enabled(true))
    check(blocking_api_allowed(false) == false)

### Failure handling

    val status   = process_status()         # => "failed"
    val restarts = supervisor_restart_count() # => 2

## Key Concepts

**Actors** — isolated units of computation that communicate only through
typed messages. State is private; no shared memory between actors.

**Stackless coroutines** — async functions yield at `~=` points without
allocating a separate OS thread stack. The scheduler resumes them when
their awaited value is ready.

**Futures and Promises** — a `Future<T>` represents a not-yet-computed
value. `map` and `then` chain transformations without blocking. A `Promise`
is the write-end that resolves the Future.

**Isolated threads** — explicit worker threads get a copy of their input;
no shared mutable state is allowed across thread boundaries by the type system.

**Runtime guards** — thread-local-storage (TLS) context gates blocking
calls. Attempting a blocking operation outside a TLS-enabled context is a
compile-time or runtime error.

**Supervisors** — monitor actors and restart them on failure. The restart
count and backoff policy are configurable per supervision tree.

## Common Patterns

Ping-pong between two actors:

    val a = spawn_actor("alice")
    val b = spawn_actor("bob")
    val rounds = ping_pong_rounds(3)  # => 6 messages total

Producer-consumer with back-pressure:

    val total = producer_consumer_roundtrip(10, 20)  # => 30

Chain of async operations with intermediate results:

    val raw    = fetch_data(5)          # => 12
    val scaled = future_map_then(raw)   # => 34 ((12+5)*2)

## Scenarios

### Concurrency Spec

#### actors_processes_1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actor_name = spawn_actor("worker")
check(actor_name == "worker")
```

</details>

#### actors_processes_2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = send_message(2)
check(count == 3)
```

</details>

#### actors_processes_3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val message = receive_message("alpha")
check(message == "alpha")
```

</details>

#### actors_processes_ping_pong

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rounds = ping_pong_rounds(2)
check(rounds == 4)
```

</details>

#### async_effects_and_stackless_coroutine_actors_5

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(non_blocking_async_step())
```

</details>

#### async_effects_and_stackless_coroutine_actors_6

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bounded_loop(5) == 5)
```

</details>

#### async_effects_and_stackless_coroutine_actors_7

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = counter_after_deltas(1, 2)
check(total == 3)
```

</details>

#### async_effects_and_stackless_coroutine_actors_8

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = parse_stream("tok1", "tok2")
check(token == "tok2")
```

</details>

#### isolated_threads_9

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = copy_text("isolated")
check(value == "isolated")
```

</details>

#### isolated_threads_10

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = producer_consumer_roundtrip(10, 20)
check(sum == 30)
```

</details>

#### futures_and_promises_11

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = promise_complete(42)
check(result == 42)
```

</details>

#### futures_and_promises_12

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workers = thread_pool_size(4)
check(workers == 4)
```

</details>

#### futures_and_promises_13

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = manual_mode_label()
check(mode == "Manual")
```

</details>

#### futures_and_promises_14

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = future_state_label()
check(state == "Pending")
```

</details>

#### futures_and_promises_15

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = resolved_future_value(99)
check(value == 99)
```

</details>

#### futures_and_promises_16

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = fetch_data(5)
check(value == 12)
```

</details>

#### futures_and_promises_17

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = future_map_then(10)
check(value == 30)
```

</details>

#### futures_and_promises_18

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = data_service_request(7)
check(result == 107)
```

</details>

#### futures_and_promises_19

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = data_service_request(3)
check(result == 103)
```

</details>

#### runtime_guards_20

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(tls_context_enabled(true))
check(blocking_api_allowed(false) == false)
```

</details>

#### runtime_guards_21

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(blocking_api_allowed(false) == false)
```

</details>

#### failure_handling_22

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = process_status()
check(status == "failed")
```

</details>

#### failure_handling_23

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val restarts = supervisor_restart_count()
check(restarts == 2)
```

</details>

#### note_on_semantic_types_24

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val message = typed_message("text:hello")
check(message == "text:hello")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
