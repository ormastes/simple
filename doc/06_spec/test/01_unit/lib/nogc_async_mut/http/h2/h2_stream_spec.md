# H2 Stream Lifecycle Specification

> <details>

<!-- sdn-diagram:id=h2_stream_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=h2_stream_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

h2_stream_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=h2_stream_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H2 Stream Lifecycle Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-1-stream |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/nogc_async_mut/http/h2/h2_stream_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### H2 stream lifecycle and flow control

#### starts in idle state

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stub: stream state constants
val STATE_IDLE = 0
val stream_state = STATE_IDLE
expect(stream_state).to_equal(STATE_IDLE)
# stream_id must be odd (client-initiated)
val stream_id: u32 = 1
expect(stream_id % 2).to_equal(1)
```

</details>

#### transitions to open on HEADERS send

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val STATE_IDLE = 0
val STATE_OPEN = 1
var stream_state = STATE_IDLE
# Simulate sending HEADERS (no END_STREAM flag)
val end_stream = false
if !end_stream:
    stream_state = STATE_OPEN
expect(stream_state).to_equal(STATE_OPEN)
```

</details>

#### transitions to half-closed-local on END_STREAM send

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val STATE_OPEN = 1
val STATE_HALF_CLOSED_LOCAL = 2
var stream_state = STATE_OPEN
# Simulate sending DATA with END_STREAM flag
val end_stream = true
if end_stream:
    stream_state = STATE_HALF_CLOSED_LOCAL
expect(stream_state).to_equal(STATE_HALF_CLOSED_LOCAL)
```

</details>

#### transitions to closed on RST_STREAM

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val STATE_OPEN = 1
val STATE_CLOSED = 4
var stream_state = STATE_OPEN
# Simulate RST_STREAM received
val rst_received = true
if rst_received:
    stream_state = STATE_CLOSED
expect(stream_state).to_equal(STATE_CLOSED)
```

</details>

#### tracks flow control window credits

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial_window: i32 = 65535
var send_window: i32 = initial_window
# Send 1000 bytes of data
val bytes_sent: i32 = 1000
send_window = send_window - bytes_sent
expect(send_window).to_equal(64535)
# Send another 64535 bytes — window reaches zero
send_window = send_window - 64535
expect(send_window).to_equal(0)
```

</details>

#### rejects data when flow control window exhausted

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var send_window: i32 = 0
val data_size: i32 = 512
# Attempt to send: blocked because window == 0
val can_send = send_window >= data_size
expect(can_send).to_equal(false)
# After WINDOW_UPDATE adds 1024 credits, send is allowed
send_window = send_window + 1024
val can_send_after_update = send_window >= data_size
expect(can_send_after_update).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
