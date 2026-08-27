# Simple Language Concurrency - Test Specification

> This spec covers Simple's concurrency model: actor-based message passing, async-by-default functions, stackless coroutines, futures/promises, and runtime guards for blocking calls and thread isolation.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- actors_processes_1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actors_processes_1")
val actor_name = spawn_actor("worker")
check(actor_name == "worker")
```

</details>

#### actors_processes_2

- actors_processes_2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actors_processes_2")
val count = send_message(2)
check(count == 3)
```

</details>

#### actors_processes_3

- actors_processes_3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actors_processes_3")
val message = receive_message("alpha")
check(message == "alpha")
```

</details>

#### actors_processes_ping_pong

- actors_processes_ping_pong


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actors_processes_ping_pong")
val rounds = ping_pong_rounds(2)
check(rounds == 4)
```

</details>

#### async_effects_and_stackless_coroutine_actors_5

- async_effects_and_stackless_coroutine_actors_5


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async_effects_and_stackless_coroutine_actors_5")
check(non_blocking_async_step())
```

</details>

#### async_effects_and_stackless_coroutine_actors_6

- async_effects_and_stackless_coroutine_actors_6


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async_effects_and_stackless_coroutine_actors_6")
check(bounded_loop(5) == 5)
```

</details>

#### async_effects_and_stackless_coroutine_actors_7

- async_effects_and_stackless_coroutine_actors_7


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async_effects_and_stackless_coroutine_actors_7")
val total = counter_after_deltas(1, 2)
check(total == 3)
```

</details>

#### async_effects_and_stackless_coroutine_actors_8

- async_effects_and_stackless_coroutine_actors_8


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async_effects_and_stackless_coroutine_actors_8")
val token = parse_stream("tok1", "tok2")
check(token == "tok2")
```

</details>

#### isolated_threads_9

- isolated_threads_9


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("isolated_threads_9")
val value = copy_text("isolated")
check(value == "isolated")
```

</details>

#### isolated_threads_10

- isolated_threads_10


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("isolated_threads_10")
val sum = producer_consumer_roundtrip(10, 20)
check(sum == 30)
```

</details>

#### futures_and_promises_11

- futures_and_promises_11


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_11")
val result = promise_complete(42)
check(result == 42)
```

</details>

#### futures_and_promises_12

- futures_and_promises_12


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_12")
val workers = thread_pool_size(4)
check(workers == 4)
```

</details>

#### futures_and_promises_13

- futures_and_promises_13


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_13")
val mode = manual_mode_label()
check(mode == "Manual")
```

</details>

#### futures_and_promises_14

- futures_and_promises_14


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_14")
val state = future_state_label()
check(state == "Pending")
```

</details>

#### futures_and_promises_15

- futures_and_promises_15


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_15")
val value = resolved_future_value(99)
check(value == 99)
```

</details>

#### futures_and_promises_16

- futures_and_promises_16


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_16")
val value = fetch_data(5)
check(value == 12)
```

</details>

#### futures_and_promises_17

- futures_and_promises_17


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_17")
val value = future_map_then(10)
check(value == 30)
```

</details>

#### futures_and_promises_18

- futures_and_promises_18


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_18")
val result = data_service_request(7)
check(result == 107)
```

</details>

#### futures_and_promises_19

- futures_and_promises_19


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("futures_and_promises_19")
val result = data_service_request(3)
check(result == 103)
```

</details>

#### runtime_guards_20

- runtime_guards_20


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runtime_guards_20")
check(tls_context_enabled(true))
check(blocking_api_allowed(false) == false)
```

</details>

#### runtime_guards_21

- runtime_guards_21


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runtime_guards_21")
check(blocking_api_allowed(false) == false)
```

</details>

#### failure_handling_22

- failure_handling_22


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("failure_handling_22")
val status = process_status()
check(status == "failed")
```

</details>

#### failure_handling_23

- failure_handling_23


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("failure_handling_23")
val restarts = supervisor_restart_count()
check(restarts == 2)
```

</details>

#### note_on_semantic_types_24

- note_on_semantic_types_24


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("note_on_semantic_types_24")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c81fe02ce5d5f3bc6e8f076d5393a5d0e7bfd5f913eec8e2a2d7f3bd935ab7a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c81fe02ce5d5f3bc6e8f076d5393a5d0e7bfd5f913eec8e2a2d7f3bd935ab7a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c81fe02ce5d5f3bc6e8f076d5393a5d0e7bfd5f913eec8e2a2d7f3bd935ab7a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/language/concurrency_spec.spl
mirror: doc/06_spec/03_system/feature/language/concurrency_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/language/concurrency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/concurrency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/concurrency_spec.spl:193:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actors_processes_1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/concurrency_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actors_processes_2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/concurrency_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actors_processes_3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
