# Async UDP I/O Specification

> AsyncUdpSocket provides epoll-driven non-blocking UDP. Implements AsyncClose (UDP is message-based, not stream-based).

<!-- sdn-diagram:id=async_udp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_udp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_udp_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_udp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async UDP I/O Specification

AsyncUdpSocket provides epoll-driven non-blocking UDP. Implements AsyncClose (UDP is message-based, not stream-based).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #IO-ASYNC-UDP |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AsyncUdpSocket provides epoll-driven non-blocking UDP.
Implements AsyncClose (UDP is message-based, not stream-based).

## Syntax

```simple
val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
await socket.send_to([72, 105], "127.0.0.1:9001")?
val (data, sender) = await socket.recv_from(1024)?
await socket.close()?
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| AsyncUdpSocket | Non-blocking UDP socket (epoll) — AsyncClose |
| send_to/recv_from | Addressed async datagram operations |
| connect/send/recv | Connected async datagram operations |

## Behavior

- bind() sets socket to non-blocking
- send_to/recv_from are epoll-driven futures
- connect() and local_addr() are sync (immediate operations)
- close() deregisters from event loop

## Sync vs Async Comparison

```simple
# Sync:
val socket = UdpSocket.bind("127.0.0.1:0")?
socket.send_to(data, addr)?

# Async — same names, just add await:
val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
await socket.send_to(data, addr)?
```

## Scenarios

### AsyncUdpSocket

#### bind

#### documents async bind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
# expect socket.is_open() == true
pass
```

</details>

#### send_to and recv_from

#### documents async datagram exchange

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
# await socket.send_to([72, 105], "127.0.0.1:9001")?
# val (data, sender) = await socket.recv_from(1024)?
# await socket.close()?
pass
```

</details>

#### connected mode

#### documents async connected mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
# socket.connect("127.0.0.1:9001")?  # sync
# await socket.send([72, 105])?
# val data = await socket.recv(1024)?
# await socket.close()?
pass
```

</details>

#### broadcast (sync)

#### documents broadcast setup

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val socket = await AsyncUdpSocket.bind("0.0.0.0:0")?
# socket.set_broadcast(true)?  # sync
# await socket.send_to(data, "255.255.255.255:9000")?
pass
```

</details>

#### close

#### documents async close

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
# await socket.close()?
# expect socket.is_open() == false
pass
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
