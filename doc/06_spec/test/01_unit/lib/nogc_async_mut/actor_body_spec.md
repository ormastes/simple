# Actor Body Specification

> 1. fn worker

<!-- sdn-diagram:id=actor_body_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=actor_body_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

actor_body_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=actor_body_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Body Specification

## Scenarios

### Actor Body Execution

#### spawns actor that returns value

1. fn worker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn worker():
    return 42

val pid = spawn(worker)
expect pid != nil
```

</details>

#### spawns multiple actors

1. fn worker1
2. fn worker2


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn worker1():
    return 10

fn worker2():
    return 20

val pid1 = spawn(worker1)
val pid2 = spawn(worker2)

expect pid1 != nil
expect pid2 != nil
```

</details>

### Actor Messaging

#### sends message to actor

1. fn echo worker
2. send


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn echo_worker():
    # Actor waits for a message and returns it
    val msg = recv()
    return msg

val pid = spawn(echo_worker)
send(pid, 42)
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_body_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Actor Body Execution
- Actor Messaging

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
