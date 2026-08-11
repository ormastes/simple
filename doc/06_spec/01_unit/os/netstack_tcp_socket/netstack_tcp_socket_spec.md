# Netstack Tcp Socket Specification

> 1. var table = SocketTable new

<!-- sdn-diagram:id=netstack_tcp_socket_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=netstack_tcp_socket_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

netstack_tcp_socket_spec -> std
netstack_tcp_socket_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=netstack_tcp_socket_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Netstack Tcp Socket Specification

## Scenarios

### netstack TCP socket lifecycle

#### keeps active open connecting until the TCP handshake is established

1. var table = SocketTable new
2. check ok
3. table attach connecting
   - Expected: socket_state_name(connecting.state) equals `CONNECTING`
   - Expected: connecting.conn_id equals `42u64`
   - Expected: table.connect_status(fd) equals `in-progress`
   - Expected: table.is_write_ready(fd) is false
   - Expected: table.mark_connected_by_conn(42u64) is true
   - Expected: socket_state_name(connected.state) equals `CONNECTED`
   - Expected: connected.conn_id equals `42u64`
   - Expected: table.connect_status(fd) equals `established`
   - Expected: table.is_write_ready(fd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SocketTable.new()
val fd = table.create(SocketProtocol.Tcp)
val remote = SockAddr(ip: Ipv4Address.from_u32(0x0A000202u32), port: 80u16)
val local = SockAddr(ip: Ipv4Address.from_u32(0x0A00020Fu32), port: 49152u16)

check_ok(table.connect(fd, remote))
table.attach_connecting(fd, local, 42u64)

val connecting = table.get_socket(fd).unwrap()
expect(socket_state_name(connecting.state)).to_equal("CONNECTING")
expect(connecting.conn_id).to_equal(42u64)
expect(table.connect_status(fd)).to_equal("in-progress")
expect(table.is_write_ready(fd)).to_equal(false)

expect(table.mark_connected_by_conn(42u64)).to_equal(true)

val connected = table.get_socket(fd).unwrap()
expect(socket_state_name(connected.state)).to_equal("CONNECTED")
expect(connected.conn_id).to_equal(42u64)
expect(table.connect_status(fd)).to_equal("established")
expect(table.is_write_ready(fd)).to_equal(true)

match table.send(fd, [1u8, 2u8]):
    Ok(n): expect(n).to_equal(0u64)
    Err(msg): expect(msg).to_contain("TCP send buffers")

match table.recv(fd, 16u64):
    Ok(data): expect(data.len()).to_equal(999u64)
    Err(msg): expect(msg).to_contain("TCP receive buffers")
```

</details>

#### moves a client TCP connection from SYN_SENT to ESTABLISHED on SYN ACK

1. var conn = TcpConnection new client
   - Expected: tcp_state_name(conn.state) equals `SYN_SENT`
   - Expected: syn.len() equals `1u64`
   - Expected: tcp_state_name(conn.state) equals `ESTABLISHED`
   - Expected: replies.len() equals `1u64`
   - Expected: replies[0].header.flags & TCP_FLAG_ACK equals `TCP_FLAG_ACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local_ip = Ipv4Address.from_u32(0x0A00020Fu32)
val remote_ip = Ipv4Address.from_u32(0x0A000202u32)
var conn = TcpConnection.new_client(local_ip, 49152u16, remote_ip, 80u16)

val syn = conn.connect()
expect(tcp_state_name(conn.state)).to_equal("SYN_SENT")
expect(syn.len()).to_equal(1u64)

val syn_ack = TcpSegment(
    header: TcpHeader(
        src_port: 80u16,
        dst_port: 49152u16,
        seq_num: 1000u32,
        ack_num: conn.snd_nxt,
        data_offset: 5u8,
        flags: TCP_FLAG_SYN | TCP_FLAG_ACK,
        window: TCP_DEFAULT_WINDOW,
        checksum: 0u16,
        urgent_ptr: 0u16
    ),
    data: []
)

val replies = conn.process_segment(syn_ack, remote_ip)
expect(tcp_state_name(conn.state)).to_equal("ESTABLISHED")
expect(replies.len()).to_equal(1u64)
expect(replies[0].header.flags & TCP_FLAG_ACK).to_equal(TCP_FLAG_ACK)
```

</details>

#### records refused and timeout connect completion separately

1. var table = SocketTable new
2. check ok
3. table attach connecting
   - Expected: table.mark_connect_failed_by_conn(43u64, "refused") is true
   - Expected: table.connect_status(fd_refused) equals `refused`
   - Expected: table.is_write_ready(fd_refused) is false
4. check ok
5. table attach connecting
   - Expected: table.mark_connect_failed_by_conn(44u64, "timeout") is true
   - Expected: table.connect_status(fd_timeout) equals `timeout`
   - Expected: table.is_write_ready(fd_timeout) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SocketTable.new()
val fd_refused = table.create(SocketProtocol.Tcp)
val fd_timeout = table.create(SocketProtocol.Tcp)
val remote = SockAddr(ip: Ipv4Address.from_u32(0x0A000202u32), port: 80u16)
val local = SockAddr(ip: Ipv4Address.from_u32(0x0A00020Fu32), port: 49152u16)

check_ok(table.connect(fd_refused, remote))
table.attach_connecting(fd_refused, local, 43u64)
expect(table.mark_connect_failed_by_conn(43u64, "refused")).to_equal(true)
expect(table.connect_status(fd_refused)).to_equal("refused")
expect(table.is_write_ready(fd_refused)).to_equal(false)

check_ok(table.connect(fd_timeout, remote))
table.attach_connecting(fd_timeout, local, 44u64)
expect(table.mark_connect_failed_by_conn(44u64, "timeout")).to_equal(true)
expect(table.connect_status(fd_timeout)).to_equal("timeout")
expect(table.is_write_ready(fd_timeout)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/netstack_tcp_socket/netstack_tcp_socket_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- netstack TCP socket lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
