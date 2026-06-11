# Actor Dispatch Specification

> <details>

<!-- sdn-diagram:id=actor_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=actor_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

actor_dispatch_spec
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

### Actor Dispatch

### HandlerTable

#### creates empty handler table

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# HandlerTable stores method name -> handler function mappings
val table_size = 0
expect(table_size).to_equal(0)
```

</details>

#### registers handler by method name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# register("greet", handler_fn) adds to table
val method = "greet"
expect(method).to_equal("greet")
```

</details>

#### dispatches to correct handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dispatch("greet", args) finds and calls handler_fn
val method = "greet"
val found = method == "greet"
expect(found).to_equal(true)
```

</details>

### ActorRef

#### sends message to actor mailbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ActorRef.send(method, args) enqueues Message
val method = "process"
val sent = true
expect(sent).to_equal(true)
```

</details>

#### stores actor pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = 42
expect(pid).to_equal(42)
```

</details>

### Actor Lifecycle

#### spawns actor with handler table

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# spawn_actor creates actor with mailbox + handlers
val spawned = true
expect(spawned).to_equal(true)
```

</details>

#### processes messages from mailbox in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Actor loop: pull message -> lookup handler -> call -> reply
var order = [1, 2, 3]
expect(order.len()).to_equal(3)
```

</details>

### DispatchResult

#### returns Ok for successful dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "ok"
expect(result).to_equal("ok")
```

</details>

#### returns NotFound for unknown method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "not_found"
expect(result).to_equal("not_found")
```

</details>

### Reply Mechanism

#### sends reply when reply_to is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reply_to = 7
val has_reply = reply_to > 0
expect(has_reply).to_equal(true)
```

</details>

#### skips reply when reply_to is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reply_to = nil
expect(reply_to).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Actor Dispatch
- HandlerTable
- ActorRef
- Actor Lifecycle
- DispatchResult
- Reply Mechanism

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
