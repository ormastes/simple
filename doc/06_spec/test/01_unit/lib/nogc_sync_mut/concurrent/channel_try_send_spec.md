# Channel Try Send Specification

> <details>

<!-- sdn-diagram:id=channel_try_send_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=channel_try_send_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

channel_try_send_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=channel_try_send_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Channel Try Send Specification

## Scenarios

### Channel try_send (H7 — closed-state signaling)

#### try_send on open channel

#### returns true when channel is open

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val result = ch.try_send(42)
expect(result).to_equal(true)
```

</details>

#### try_send on closed channel

#### returns false after close()

- ch close
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
val result = ch.try_send(99)
expect(result).to_equal(false)
```

</details>

#### returns false on second try_send after close

- ch close
   - Expected: r1 is false
   - Expected: r2 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
val r1 = ch.try_send(1)
val r2 = ch.try_send(2)
expect(r1).to_equal(false)
expect(r2).to_equal(false)
```

</details>

#### is_closed reflects close()

#### is_closed returns false before close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val closed = ch.is_closed()
expect(closed).to_equal(false)
```

</details>

#### is_closed returns true after close

- ch close
   - Expected: closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
val closed = ch.is_closed()
expect(closed).to_equal(true)
```

</details>

#### send() backward compatibility

#### send() to closed channel is still a silent no-op (compat)

- ch close
- ch send
   - Expected: closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# send() must not crash or change the closed state
val ch = channel_new()
ch.close()
ch.send(7)
# channel remains closed, no crash
val closed = ch.is_closed()
expect(closed).to_equal(true)
```

</details>

#### send() to open channel still delivers message

- ch send
   - Expected: got equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(123)
val got = ch.try_recv()
expect(got).to_equal(123)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/concurrent/channel_try_send_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Channel try_send (H7 — closed-state signaling)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
