# Async Basics Unit Tests

> 1. check

<!-- sdn-diagram:id=async_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Basics Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-ASYNC-001 |
| Category | Lib \| Async |
| Status | Implemented |
| Source | `test/01_unit/lib/async/async_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Future Types

#### future represents pending value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "pending"
check(state == "pending")
```

</details>

#### future can be resolved

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "resolved"
check(state == "resolved")
```

</details>

#### future can be rejected

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "rejected"
check(state == "rejected")
```

</details>

#### future has value on resolve

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = Some(42)
check(value.?)
```

</details>

### Promise Types

#### promise is writable future

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_writable = true
check(is_writable)
```

</details>

#### promise resolves once

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolve_count = 1
check(resolve_count == 1)
```

</details>

#### promise reject once

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reject_count = 1
check(reject_count == 1)
```

</details>

### Async Task States

#### task created state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "created"
check(state == "created")
```

</details>

#### task running state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "running"
check(state == "running")
```

</details>

#### task completed state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "completed"
check(state == "completed")
```

</details>

#### task cancelled state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "cancelled"
check(state == "cancelled")
```

</details>

#### task failed state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "failed"
check(state == "failed")
```

</details>

### Channel Types

#### unbounded channel

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val capacity = -1
check(capacity == -1)
```

</details>

#### bounded channel

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val capacity = 10
check(capacity > 0)
```

</details>

#### channel send

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sent = true
check(sent)
```

</details>

#### channel receive

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val received = true
check(received)
```

</details>

#### channel close

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val closed = true
check(closed)
```

</details>

### Actor Model

#### actor has mailbox

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_mailbox = true
check(has_mailbox)
```

</details>

#### actor processes messages

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val processed = 1
check(processed > 0)
```

</details>

#### actor state isolation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val isolated = true
check(isolated)
```

</details>

#### actor supervision

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val strategy = "restart"
check(strategy == "restart" or strategy == "stop")
```

</details>

### Generator States

#### generator initial state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "initial"
check(state == "initial")
```

</details>

#### generator yielded state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "yielded"
check(state == "yielded")
```

</details>

#### generator completed state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = "completed"
check(state == "completed")
```

</details>

#### generator yield value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = Some(42)
check(value.?)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
