# Green Channel Closed Specification

> <details>

<!-- sdn-diagram:id=green_channel_closed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_channel_closed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_channel_closed_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_channel_closed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Green Channel Closed Specification

## Scenarios

### GreenChannel closed-state signaling (H8)

#### is_closed / close() flag

#### new channel is not closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
expect(green_channel_is_closed(ch)).to_equal(false)
```

</details>

#### close() marks channel as closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val closed_ch = green_channel_close(ch)
expect(green_channel_is_closed(closed_ch)).to_equal(true)
```

</details>

#### closing an already-closed channel is idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val c1 = green_channel_close(ch)
val c2 = green_channel_close(c1)
expect(green_channel_is_closed(c2)).to_equal(true)
```

</details>

#### recv on closed + empty channel

#### returns channel_closed=true without parking

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val closed_ch = green_channel_close(ch)
val result = green_channel_recv(closed_ch, 77)
expect(result.channel_closed).to_equal(true)
expect(result.parked).to_equal(false)
expect(result.received).to_equal(false)
expect(result.reason).to_equal("channel_closed")
```

</details>

#### waiting_task_ids stays empty after recv-on-closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val closed_ch = green_channel_close(ch)
val result = green_channel_recv(closed_ch, 55)
val waiting = green_channel_waiting_count(result.channel)
expect(waiting).to_equal(0)
```

</details>

#### recv on closed + non-empty channel drains buffered values first

#### delivers buffered value before reporting closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val s = green_channel_send(ch, 42)
val closed_ch = green_channel_close(s.channel)
val result = green_channel_recv(closed_ch, 1)
expect(result.received).to_equal(true)
expect(result.value).to_equal(42)
expect(result.channel_closed).to_equal(false)
```

</details>

#### second recv on now-empty closed channel returns channel_closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val s = green_channel_send(ch, 42)
val closed_ch = green_channel_close(s.channel)
val r1 = green_channel_recv(closed_ch, 1)
val r2 = green_channel_recv(r1.channel, 2)
expect(r1.received).to_equal(true)
expect(r2.channel_closed).to_equal(true)
expect(r2.parked).to_equal(false)
```

</details>

#### send after close

#### green_channel_send returns sent=false and channel_closed=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val closed_ch = green_channel_close(ch)
val result = green_channel_send(closed_ch, 99)
expect(result.sent).to_equal(false)
expect(result.channel_closed).to_equal(true)
expect(result.reason).to_equal("channel_closed")
```

</details>

#### green_channel_try_send returns sent=false after close

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val closed_ch = green_channel_close(ch)
val result = green_channel_try_send(closed_ch, 77)
expect(result.sent).to_equal(false)
expect(result.channel_closed).to_equal(true)
```

</details>

#### green_channel_close_drain wakes parked receivers

#### drain returns the parked task IDs in woken_task_ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
# Park two receivers
val r1 = green_channel_recv(ch, 10)
val r2 = green_channel_recv(r1.channel, 20)
val drain = green_channel_close_drain(r2.channel)
val woken_count = drain.woken_task_ids.len()
expect(woken_count).to_equal(2)
```

</details>

#### drain leaves waiting_task_ids empty in closed channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val r1 = green_channel_recv(ch, 10)
val drain = green_channel_close_drain(r1.channel)
val waiting = green_channel_waiting_count(drain.channel)
expect(waiting).to_equal(0)
```

</details>

#### drain marks channel as closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val r1 = green_channel_recv(ch, 10)
val drain = green_channel_close_drain(r1.channel)
expect(green_channel_is_closed(drain.channel)).to_equal(true)
```

</details>

#### drain on channel with no waiters returns empty woken list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val drain = green_channel_close_drain(ch)
val woken_count = drain.woken_task_ids.len()
expect(woken_count).to_equal(0)
```

</details>

#### happy-path: open channel behavior unchanged

#### send + recv still works on open channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val s = green_channel_send(ch, 55)
val r = green_channel_recv(s.channel, 1)
expect(r.received).to_equal(true)
expect(r.value).to_equal(55)
expect(r.channel_closed).to_equal(false)
```

</details>

#### park on empty open channel still sets parked=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = green_channel_new(2)
val result = green_channel_recv(ch, 99)
expect(result.parked).to_equal(true)
expect(result.channel_closed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent/green_channel_closed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GreenChannel closed-state signaling (H8)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
