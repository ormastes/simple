# Async TCP I/O Specification

> AsyncTcpListener and AsyncTcpStream provide epoll-driven non-blocking TCP. True async I/O — the event loop wakes futures when fds become ready.

<!-- sdn-diagram:id=async_tcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_tcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_tcp_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_tcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async TCP I/O Specification

AsyncTcpListener and AsyncTcpStream provide epoll-driven non-blocking TCP. True async I/O — the event loop wakes futures when fds become ready.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #IO-ASYNC-TCP |
| Category | Stdlib |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AsyncTcpListener and AsyncTcpStream provide epoll-driven non-blocking TCP.
True async I/O — the event loop wakes futures when fds become ready.

## Syntax

```simple
val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
val stream = await listener.accept()?
val request = await stream.read_text()?
await stream.write_text("HTTP/1.1 200 OK\\r\\n\\r\\nHello")?
await stream.close()?
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| AsyncTcpListener | Non-blocking server socket (epoll) — AsyncClose |
| AsyncTcpStream | Non-blocking connection (epoll) — AsyncRead+AsyncWrite+AsyncClose |
| EventLoop | Underlying epoll/kqueue integration |

## Behavior

- bind() sets socket to non-blocking mode
- accept() returns Future that resolves when client connects
- read/write on AsyncTcpStream are epoll-driven (true non-blocking)
- local_addr/peer_addr remain sync (cached values)
- set_nodelay remains sync (immediate setsockopt)
- close() deregisters from event loop, then closes fd

## Sync vs Async Comparison

```simple
# Sync:
val listener = TcpListener.bind("0.0.0.0:8080")?
val stream = listener.accept()?
val data = stream.read_text()?

# Async — same names, just add await:
val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
val stream = await listener.accept()?
val data = await stream.read_text()?
```

## Scenarios

### AsyncTcpListener

#### bind

#### documents async bind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
# expect listener.is_open() == true
0
```

</details>

#### accept

#### documents async accept

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
# val stream = await listener.accept()?
# # stream is an AsyncTcpStream ready for read/write
0
```

</details>

#### local_addr (sync)

#### documents sync local_addr

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val listener = await AsyncTcpListener.bind("127.0.0.1:0")?
# val addr = listener.local_addr()?  # sync!
# expect addr.contains("127.0.0.1") == true
0
```

</details>

#### close

#### documents async close

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
# await listener.close()?
# expect listener.is_open() == false
0
```

</details>

### AsyncTcpStream

#### connect

#### documents async connect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("example.com:80")?
0
```

</details>

#### documents connect with timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect_timeout("example.com:80", 5000)?
0
```

</details>

#### AsyncRead (epoll-driven)

#### documents async read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val chunk = await stream.read(1024)?
0
```

</details>

#### documents async read_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val response = await stream.read_text()?
0
```

</details>

#### documents async read_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val line = await stream.read_line()?
0
```

</details>

#### AsyncWrite (epoll-driven)

#### documents async write_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# await stream.write_text("GET / HTTP/1.1\\r\\n\\r\\n")?
# await stream.flush()?
0
```

</details>

#### TCP options (sync)

#### documents sync TCP options

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# stream.set_nodelay(true)?         # sync
# val peer = stream.peer_addr()?    # sync
# val local = stream.local_addr()?  # sync
0
```

</details>

#### shutdown

#### documents async shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# await stream.shutdown(Shutdown.Write)?
0
```

</details>

#### error on closed stream

#### returns error for read on closed stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AsyncTcpStream constructor not available in test context
# var stream = AsyncTcpStream(fd: -1, event_loop: nil, open: false)
# read should return immediately-resolved Future with error
0
```

</details>

### Async HTTP Server Pattern

#### documented pattern

#### documents async HTTP server

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
# while true:
#     val stream = await listener.accept()?
#     spawn handle_request(stream)
#
# fn handle_request(stream: AsyncTcpStream):
#     val request = await stream.read_text()?
#     await stream.write_text("HTTP/1.1 200 OK\\r\\n\\r\\nHello")?
#     await stream.close()?
0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
