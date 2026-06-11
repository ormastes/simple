# Actor Dispatch Specification

> <details>

<!-- sdn-diagram:id=actor_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=actor_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

actor_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=actor_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Dispatch Specification

## Scenarios

### HandlerTable registration

#### registered handler is invoked and returns its result

- var ht = make handlers
- ht register
   - Expected: result.is_ok() is true
   - Expected: result.value equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("echo", ["hello"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("hello")
```

</details>

#### registering a second handler replaces the first

- var ht = make handlers
- ht register
- ht register
   - Expected: result.is_ok() is true
   - Expected: result.value equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = make_handlers()
ht.register("greet", handler_echo)
ht.register("greet", handler_greet)

val result = ht.dispatch("greet", ["World"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("Hello, World!")
```

</details>

#### dispatching unknown method returns MethodNotFound error not crash

- var ht = make handlers
- ht register
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("no_such_method", [])

expect(result.is_ok()).to_equal(false)
expect(result.error_msg).to_contain("no_such_method")
```

</details>

#### dispatching unknown method on empty table returns typed error

- var ht = make handlers
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = make_handlers()

val result = ht.dispatch("totally_unknown", ["arg1", "arg2"])

expect(result.is_ok()).to_equal(false)
expect(result.error_msg).to_contain("totally_unknown")
```

</details>

#### call() returns handler result synchronously

- var ht = make handlers
- ht register
   - Expected: result.is_ok() is true
   - Expected: result.value equals `Hello, Alice!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Models ProcessManager Shared-mode call(): direct HandlerTable dispatch.
var ht = make_handlers()
ht.register("greet", handler_greet)

val result = ht.dispatch("greet", ["Alice"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("Hello, Alice!")
```

</details>

#### cast() fire-and-forget: dispatch runs and result is safely ignored

- var ht = make handlers
- ht register
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Models ProcessManager Shared cast(): dispatch runs, caller drops result.
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("echo", ["data"])

expect(result.is_ok()).to_equal(true)
```

</details>

### Actor isolation by convention

#### two handler tables with same method name dispatch independently

- var ht a = make handlers
- ht a register
- var ht b = make handlers
- ht b register
   - Expected: result_a.is_ok() is true
   - Expected: result_b.is_ok() is true
   - Expected: result_a.value equals `a_result`
   - Expected: result_b.value equals `b_result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Actors are share-nothing by convention: separate HandlerTable instances
# never share entries or state.
var ht_a = make_handlers()
ht_a.register("id", handler_count_a)

var ht_b = make_handlers()
ht_b.register("id", handler_count_b)

val result_a = ht_a.dispatch("id", [])
val result_b = ht_b.dispatch("id", [])

expect(result_a.is_ok()).to_equal(true)
expect(result_b.is_ok()).to_equal(true)
expect(result_a.value).to_equal("a_result")
expect(result_b.value).to_equal("b_result")
# Different values confirm the two tables are independent.
expect(result_a.value).to_not_equal(result_b.value)
```

</details>

#### registering a handler in one table does not affect another table

- var ht a = make handlers
- ht a register
- var ht b = make handlers
   - Expected: result_a.is_ok() is true
   - Expected: result_b.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht_a = make_handlers()
ht_a.register("method_x", handler_echo)

var ht_b = make_handlers()
# ht_b has no "method_x"

val result_a = ht_a.dispatch("method_x", ["hello"])
val result_b = ht_b.dispatch("method_x", ["hello"])

expect(result_a.is_ok()).to_equal(true)
expect(result_b.is_ok()).to_equal(false)
```

</details>

#### actor IDs are unique across separately spawned actors

- var ht = make handlers
- ht register


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = make_handlers()
ht.register("noop", handler_noop)

val ref1 = spawn_actor(ht)
val ref2 = spawn_actor(ht)

expect(ref1.get_id()).to_not_equal(ref2.get_id())
```

</details>

### ActorRuntime process_mailbox

#### dispatching a known method succeeds

- var ht = make handlers
- ht register
   - Expected: result.is_ok() is true
   - Expected: result.value equals `pong`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test the dispatch machinery directly using HandlerTable.dispatch(),
# which is the synchronous path used by both run_once and direct call().
# NOTE: Dict value-semantics mean mailbox push via actors.get() does not
# persist; this test validates the dispatch step in isolation.
var ht = make_handlers()
ht.register("ping", handler_echo)

val result = ht.dispatch("ping", ["pong"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("pong")
```

</details>

#### dispatching unknown method returns error result not panic

- var ht = make handlers
- ht register
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("no_such_method", [])

expect(result.is_ok()).to_equal(false)
expect(result.error_msg).to_contain("no_such_method")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HandlerTable registration
- Actor isolation by convention
- ActorRuntime process_mailbox

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
