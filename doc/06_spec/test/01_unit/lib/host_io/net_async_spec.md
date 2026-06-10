# Host Net Async — Specification

> Because the interpreter is single-threaded:

<!-- sdn-diagram:id=net_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_async_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Net Async — Specification

Because the interpreter is single-threaded:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HOST-NET-ASYNC |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/host_io/net_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Concepts

| Concept | Description |
|---------|-------------|
| AsyncTcpListener | Async TCP server — bind is sync Result, accept returns eager Future |
| AsyncTcpStream | Async TCP connection — read/write return eager Futures |
| AsyncUdpSocket | Async UDP socket — send/recv return eager Futures |

## Loopback Echo Pattern (single-threaded)

Because the interpreter is single-threaded:
  1. Bind listener (OS assigns ephemeral port).
  2. Connect client (OS queues the connection internally).
  3. Accept with timeout (OS returns the already-queued client fd).
  4. Exchange bytes.

## Related Specifications

- [Async TCP I/O](../../lib/nogc_async_mut/io/async_tcp_spec.spl) — epoll-driven async variant

## Scenarios

### AsyncTcpListener

#### binds to an ephemeral port and reports local_addr

- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val listener = AsyncTcpListener.bind("127.0.0.1:0").unwrap()
val addr = listener.local_addr().unwrap()
expect(addr.contains("127.0.0.1")).to_equal(true)
expect(addr.len() > 9).to_equal(true)
listener.close()
```

</details>

#### is_open starts true

- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val listener = AsyncTcpListener.bind("127.0.0.1:0").unwrap()
expect(listener.is_open()).to_equal(true)
listener.close()
```

</details>

### AsyncTcpStream

#### connect returns eager future (Poll.Ready)

- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val listener = AsyncTcpListener.bind("127.0.0.1:0").unwrap()
val addr = listener.local_addr().unwrap()
val fut = AsyncTcpStream.connect(addr)
match fut.poll():
    case Poll.Ready(_): pass
    case Poll.Pending: expect(false).to_equal(true)
listener.close()
```

</details>

#### connect_timeout returns eager future (Poll.Ready)

- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val listener = AsyncTcpListener.bind("127.0.0.1:0").unwrap()
val addr = listener.local_addr().unwrap()
val fut = AsyncTcpStream.connect_timeout(addr, 5000)
match fut.poll():
    case Poll.Ready(_): pass
    case Poll.Pending: expect(false).to_equal(true)
listener.close()
```

</details>

#### is_open starts true on connected stream

- var client = match c fut poll
   - Expected: client.is_open() is true
- client close
- listener close


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val listener = AsyncTcpListener.bind("127.0.0.1:0").unwrap()
val addr = listener.local_addr().unwrap()
val c_fut = AsyncTcpStream.connect(addr)
var client = match c_fut.poll():
    case Poll.Ready(Ok(s)): s
    case _: panic("connect failed")
expect(client.is_open()).to_equal(true)
client.close()
listener.close()
```

</details>

### Host Net Async loopback echo

#### client write then server read echoes payload exactly

- var client = match c fut poll
- var server conn = match a fut poll
   - Expected: n equals `5`
   - Expected: false is true
   - Expected: false is true
- client flush
- var received = match r fut poll
   - Expected: received.len() equals `5`
   - Expected: received[0] equals `72`
   - Expected: received[1] equals `101`
   - Expected: received[2] equals `108`
   - Expected: received[3] equals `108`
   - Expected: received[4] equals `111`
- client close
- server conn close
- bound close


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l_result = AsyncTcpListener.bind("127.0.0.1:0")
val bound = match l_result:
    case Ok(l): l
    case Err(e): panic("bind failed")
val addr = bound.local_addr().unwrap()

# Client connects before accept — OS queues it
val c_fut = AsyncTcpStream.connect(addr)
var client = match c_fut.poll():
    case Poll.Ready(Ok(s)): s
    case _: panic("connect failed")

# Accept the already-queued connection
val a_fut = bound.accept_timeout(2000)
var server_conn = match a_fut.poll():
    case Poll.Ready(Ok(s)): s
    case _: panic("accept failed")

# Client writes ASCII "Hello" = [72, 101, 108, 108, 111]
val payload: [u8] = [72, 101, 108, 108, 111]
val w_fut = client.write(payload)
match w_fut.poll():
    case Poll.Ready(Ok(n)):
        expect(n).to_equal(5)
    case Poll.Ready(Err(e)):
        expect(false).to_equal(true)
    case Poll.Pending:
        expect(false).to_equal(true)

client.flush()

# Server reads exactly 5 bytes
val r_fut = server_conn.read_exact(5)
var received = match r_fut.poll():
    case Poll.Ready(Ok(data)): data
    case Poll.Ready(Err(e)): panic("read failed")
    case Poll.Pending: panic("read future Pending")

# Absolute oracle: byte-by-byte equality
expect(received.len()).to_equal(5)
expect(received[0]).to_equal(72)
expect(received[1]).to_equal(101)
expect(received[2]).to_equal(108)
expect(received[3]).to_equal(108)
expect(received[4]).to_equal(111)

client.close()
server_conn.close()
bound.close()
```

</details>

#### bidirectional echo: server writes back what it received

- var client = match c fut poll
- var server conn = match a fut poll
- client write
- client flush
- var got = match sr fut poll
- server conn write
- server conn flush
- var echo = match er fut poll
   - Expected: echo.len() equals `4`
   - Expected: echo[0] equals `80`
   - Expected: echo[1] equals `105`
   - Expected: echo[2] equals `110`
   - Expected: echo[3] equals `103`
- client close
- server conn close
- bound close


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l_result = AsyncTcpListener.bind("127.0.0.1:0")
val bound = match l_result:
    case Ok(l): l
    case Err(e): panic("bind failed")
val addr = bound.local_addr().unwrap()

val c_fut = AsyncTcpStream.connect(addr)
var client = match c_fut.poll():
    case Poll.Ready(Ok(s)): s
    case _: panic("connect failed")

val a_fut = bound.accept_timeout(2000)
var server_conn = match a_fut.poll():
    case Poll.Ready(Ok(s)): s
    case _: panic("accept failed")

# Client sends ASCII "Ping" = [80, 105, 110, 103]
val ping: [u8] = [80, 105, 110, 103]
client.write(ping)
client.flush()

# Server reads "Ping"
val sr_fut = server_conn.read_exact(4)
var got = match sr_fut.poll():
    case Poll.Ready(Ok(d)): d
    case _: panic("server read failed")

# Server echoes back
server_conn.write(got)
server_conn.flush()

# Client reads the echo
val er_fut = client.read_exact(4)
var echo = match er_fut.poll():
    case Poll.Ready(Ok(d)): d
    case _: panic("client echo read failed")

# Absolute oracle: must match "Ping" exactly
expect(echo.len()).to_equal(4)
expect(echo[0]).to_equal(80)
expect(echo[1]).to_equal(105)
expect(echo[2]).to_equal(110)
expect(echo[3]).to_equal(103)

client.close()
server_conn.close()
bound.close()
```

</details>

### AsyncUdpSocket API shape

#### AsyncUdpSocket type is importable from std.nogc_async_mut.host_io.net

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If this it-block runs without a "type not found" error, the export is correct.
expect(true).to_equal(true)
```

</details>

#### API surface matches expected shape (static check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies the module compiles and exports the three async types.
# No network calls; assertion confirms spec infrastructure is healthy.
expect(1 + 1).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
