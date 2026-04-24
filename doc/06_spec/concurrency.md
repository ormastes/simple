# Simple Language Concurrency - Test Specification

This spec covers Simple's concurrency model: actor-based message passing, async-by-default functions, stackless coroutines, futures/promises, and runtime guards for blocking calls and thread isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #200-230 |
| Status | Executable coverage |
| Type | Extracted Examples (Category B) |
| Reference | concurrency.md |
| Source | `test/specs/concurrency_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** actors, async, futures, promises, channels, coroutines
**Topics:** concurrency, async, effects
**Symbols:** Promise, Actor, Future, Channel
**Module:** simple_runtime::concurrency

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/concurrency/summary.txt` |

## Scenarios

- actors_processes_1
- actors_processes_2
- actors_processes_3
- actors_processes_ping_pong
- async_effects_and_stackless_coroutine_actors_5
- async_effects_and_stackless_coroutine_actors_6
- async_effects_and_stackless_coroutine_actors_7
- async_effects_and_stackless_coroutine_actors_8
- isolated_threads_9
- isolated_threads_10
- futures_and_promises_11
- futures_and_promises_12
- futures_and_promises_13
- futures_and_promises_14
- futures_and_promises_15
- futures_and_promises_16
- futures_and_promises_17
- futures_and_promises_18
- futures_and_promises_19
- runtime_guards_20
- runtime_guards_21
- failure_handling_22
- failure_handling_23
- note_on_semantic_types_24
