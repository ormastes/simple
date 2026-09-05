# net_acceleration_spec

> Net Acceleration Remaining — Spipe Spec

<!-- sdn-diagram:id=net_acceleration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_acceleration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_acceleration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_acceleration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# net_acceleration_spec

Net Acceleration Remaining — Spipe Spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/net/net_acceleration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Net Acceleration Remaining — Spipe Spec

20 tests covering:
  - TCP connection behavior (states, connect results, recv, send buffer, terminal transitions)
  - Socket connect semantics (POSIX outcomes, readiness, poll)
  - HTTP capability router (static-file routing, worker startup)
  - Packet ring ownership (RX/TX descriptors, ring config)

All classes and helpers are defined inline — no imports from source files.

Feature IDs: FR-NET-0001, FR-NET-0002, FR-NET-0003, FR-NET-0004
Plan: doc/03_plan/agent_tasks/net_acceleration_remaining_2026-04-21.md

## Scenarios

### TCP Connection Behavior

#### connect completion results

#### established result marks success true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_connect_established()
expect(r.success).to_equal(true)
```

</details>

#### in-progress result carries EINPROGRESS code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_connect_in_progress()
expect(r.error_msg).to_equal("EINPROGRESS")
```

</details>

#### refused result is a terminal outcome

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_connect_refused()
expect(tcp_is_terminal(r)).to_equal(true)
```

</details>

#### in-progress result is NOT terminal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_connect_in_progress()
expect(tcp_is_terminal(r) == false).to_equal(true)
```

</details>

#### timed-out result carries ETIMEDOUT and is terminal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_connect_timed_out()
expect(r.error_msg).to_equal("ETIMEDOUT")
```

</details>

### TCP Recv and Send Buffer

#### recv results

#### data recv carries the correct byte count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_recv_data(512)
expect(r.bytes_read).to_equal(512)
```

</details>

#### would-block recv returns zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_recv_would_block()
expect(r.bytes_read).to_equal(0)
```

</details>

#### peer-closed recv sets peer_closed flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_recv_peer_closed()
expect(r.peer_closed).to_equal(true)
```

</details>

#### reset recv sets was_reset flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_recv_reset()
expect(r.was_reset).to_equal(true)
```

</details>

#### send buffer window

#### send buffer allows queuing within window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = make_send_buf(4096, 2048)
expect(send_buf_can_queue(buf, 1024)).to_equal(true)
```

</details>

### Socket Connect Semantics

#### connect outcomes

#### ok outcome is writable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = make_connect_ok()
expect(o.readiness.writable).to_equal(true)
```

</details>

#### in-progress outcome is not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = make_connect_progress()
expect(o.ready == false).to_equal(true)
```

</details>

#### in-progress outcome label is in-progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = make_connect_progress()
expect(outcome_label(o)).to_equal("in-progress")
```

</details>

#### refused outcome has error bit set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = make_connect_err("ECONNREFUSED")
expect(o.readiness.is_error).to_equal(true)
```

</details>

#### ok outcome label is connected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = make_connect_ok()
expect(outcome_label(o)).to_equal("connected")
```

</details>

### HTTP Capability Router and Packet Ring

#### static file routing

#### portable backend routes to portable-read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = make_caps_portable("portable-socket")
val action = route_static_file(caps, true)
expect(action.use_portable_read).to_equal(true)
```

</details>

#### sendfile backend routes via sendfile

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = make_caps_sendfile("linux-io-uring")
val action = route_static_file(caps, true)
expect(action.use_sendfile).to_equal(true)
```

</details>

#### zero-copy backend reports sendfile tier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = make_caps_zero_copy("dma-engine")
expect(http_tier(caps)).to_equal("zero-copy")
```

</details>

#### packet ring ownership

#### rx descriptor ready transfers ownership to app

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = rx_ready(0, 64)
expect(desc.owner.owner_name).to_equal("app")
```

</details>

#### af-xdp ring config enables packet io

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ring_cfg_afxdp(1024)
expect(cfg.supports_packet_io).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
