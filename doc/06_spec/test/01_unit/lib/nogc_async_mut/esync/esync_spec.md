# Esync Specification

> <details>

<!-- sdn-diagram:id=esync_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=esync_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

esync_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=esync_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Esync Specification

## Scenarios

### esync NT event/semaphore

#### create returns a positive handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
expect(h).to_be_greater_than(0)
```

</details>

#### two creates return distinct handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = esync_create()
val h2 = esync_create()
expect(h1).to_not_equal(h2)
```

</details>

#### wait on unsignaled handle with timeout=0 returns timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
val result = esync_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### signal then wait returns signaled

1. esync signal
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
esync_signal(h)
val result = esync_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### wait consumes signal (auto-reset)

1. esync signal
2. esync wait
   - Expected: result2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
esync_signal(h)
esync_wait(h, 0)
val result2 = esync_wait(h, 0)
expect(result2).to_equal("timeout")
```

</details>

#### reset clears a signaled handle

1. esync signal
2. esync reset
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
esync_signal(h)
esync_reset(h)
val result = esync_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### wait on invalid handle returns invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = esync_wait(-1, 0)
expect(result).to_equal("invalid")
```

</details>

#### signal on invalid handle does not panic

1. esync signal
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
esync_signal(-99)
expect(1).to_equal(1)
```

</details>

#### close removes handle from active set

1. esync close
   - Expected: result equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = esync_create()
esync_close(h)
val result = esync_wait(h, 0)
expect(result).to_equal("invalid")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/esync/esync_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- esync NT event/semaphore

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
