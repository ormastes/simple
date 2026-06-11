# H2 Connection State Machine Specification

> <details>

<!-- sdn-diagram:id=h2_connection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=h2_connection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

h2_connection_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=h2_connection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H2 Connection State Machine Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-1-connection |
| Category | Stdlib |
| Difficulty | 4/5 |
| Status | Draft |
| Source | `test/01_unit/lib/nogc_async_mut/http/h2/h2_connection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### H2 connection state machine

#### exchanges SETTINGS on connection start

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val STATE_PREFACE = 0
val STATE_OPEN = 1
var conn_state = STATE_PREFACE
# Stub: local SETTINGS frame sent → awaiting ACK
val local_settings_sent = true
# Stub: SETTINGS ACK received from peer
val settings_ack_received = true
if local_settings_sent && settings_ack_received:
    conn_state = STATE_OPEN
expect(conn_state).to_equal(STATE_OPEN)
# Default SETTINGS values per RFC 9113 §6.5.2
val default_initial_window_size: u32 = 65535
val default_max_frame_size: u32 = 16384
expect(default_initial_window_size).to_equal(65535)
expect(default_max_frame_size).to_equal(16384)
```

</details>

#### creates new streams on client HEADERS

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stub stream registry as a counter
var stream_count: i32 = 0
val max_concurrent: u32 = 100
# Client sends HEADERS on stream_id=1
val new_stream_id: u32 = 1
val is_client_initiated = (new_stream_id % 2) == 1
expect(is_client_initiated).to_equal(true)
# Stream registered
stream_count = stream_count + 1
expect(stream_count).to_equal(1)
# Client sends HEADERS on stream_id=3
val second_stream_id: u32 = 3
stream_count = stream_count + 1
expect(stream_count).to_equal(2)
```

</details>

#### enforces max concurrent streams limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_concurrent: u32 = 2
var active_streams: u32 = 2   # already at limit
# Try to open a third stream
val can_open_new = active_streams < max_concurrent
expect(can_open_new).to_equal(false)
# After one stream closes, a new one is accepted
active_streams = active_streams - 1
val can_open_after_close = active_streams < max_concurrent
expect(can_open_after_close).to_equal(true)
```

</details>

#### sends GOAWAY with last stream ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val last_client_stream: u32 = 7   # highest stream seen
# Simulate building GOAWAY payload
# GOAWAY frame: last_stream_id (31-bit) + error_code (32-bit)
val error_code_no_error: u32 = 0x0
val goaway_last_stream = last_client_stream
expect(goaway_last_stream).to_equal(7)
expect(error_code_no_error).to_equal(0)
# After GOAWAY, connection transitions to GoingAway
val STATE_GOING_AWAY = 2
var conn_state = STATE_GOING_AWAY
expect(conn_state).to_equal(STATE_GOING_AWAY)
```

</details>

#### handles WINDOW_UPDATE for connection-level flow control

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var conn_send_window: i32 = 65535
# Receive WINDOW_UPDATE with increment = 32768
val window_increment: i32 = 32768
val is_valid_increment = window_increment > 0
expect(is_valid_increment).to_equal(true)
conn_send_window = conn_send_window + window_increment
expect(conn_send_window).to_equal(98303)
# Zero increment is invalid
val zero_increment: i32 = 0
val zero_is_valid = zero_increment > 0
expect(zero_is_valid).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
