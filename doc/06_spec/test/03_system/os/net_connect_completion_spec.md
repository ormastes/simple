# Net Connect Completion Specification

> 1. var table = SocketTable new

<!-- sdn-diagram:id=net_connect_completion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_connect_completion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_connect_completion_spec -> std
net_connect_completion_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_connect_completion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Connect Completion Specification

## Scenarios

### FR-NET-0001 TCP connect completion

#### socket readiness

#### keeps a queued SYN non-writable until TCP reaches ESTABLISHED

1. var table = SocketTable new

2. ok bool

3. table attach connecting
   - Expected: table.connect_status(fd) equals `in-progress`
   - Expected: table.is_write_ready(fd) is false
   - Expected: socket_state_name(connecting.state) equals `CONNECTING`
   - Expected: false is true
   - Expected: table.mark_connected_by_conn(101u64) is true
   - Expected: table.connect_status(fd) equals `established`
   - Expected: table.is_write_ready(fd) is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SocketTable.new()
val fd = table.create(SocketProtocol.Tcp)
val remote = SockAddr(ip: Ipv4Address.from_u32(0x0A000202u32), port: 80u16)
val local = SockAddr(ip: Ipv4Address.from_u32(0x0A00020Fu32), port: 49152u16)

ok_bool(table.connect(fd, remote))
table.attach_connecting(fd, local, 101u64)

expect(table.connect_status(fd)).to_equal("in-progress")
expect(table.is_write_ready(fd)).to_equal(false)
val connecting = table.get_socket(fd)
if connecting.?:
    expect(socket_state_name(connecting.state)).to_equal("CONNECTING")
else:
    expect(false).to_equal(true)

expect(table.mark_connected_by_conn(101u64)).to_equal(true)
expect(table.connect_status(fd)).to_equal("established")
expect(table.is_write_ready(fd)).to_equal(true)
```

</details>

#### surfaces refused and timeout completion separately

1. var table = SocketTable new

2. ok bool

3. table attach connecting
   - Expected: table.mark_connect_failed_by_conn(102u64, "refused") is true
   - Expected: table.connect_status(fd_refused) equals `refused`
   - Expected: table.is_write_ready(fd_refused) is false

4. ok bool

5. table attach connecting
   - Expected: table.mark_connect_failed_by_conn(103u64, "timeout") is true
   - Expected: table.connect_status(fd_timeout) equals `timeout`
   - Expected: table.is_write_ready(fd_timeout) is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SocketTable.new()
val remote = SockAddr(ip: Ipv4Address.from_u32(0x0A000202u32), port: 80u16)
val local = SockAddr(ip: Ipv4Address.from_u32(0x0A00020Fu32), port: 49152u16)
val fd_refused = table.create(SocketProtocol.Tcp)
val fd_timeout = table.create(SocketProtocol.Tcp)

ok_bool(table.connect(fd_refused, remote))
table.attach_connecting(fd_refused, local, 102u64)
expect(table.mark_connect_failed_by_conn(102u64, "refused")).to_equal(true)
expect(table.connect_status(fd_refused)).to_equal("refused")
expect(table.is_write_ready(fd_refused)).to_equal(false)

ok_bool(table.connect(fd_timeout, remote))
table.attach_connecting(fd_timeout, local, 103u64)
expect(table.mark_connect_failed_by_conn(103u64, "timeout")).to_equal(true)
expect(table.connect_status(fd_timeout)).to_equal("timeout")
expect(table.is_write_ready(fd_timeout)).to_equal(false)
```

</details>

#### TCP handshake

#### publishes completion only after a valid SYN ACK

1. var conn = TcpConnection new client
   - Expected: syn.len() equals `1u64`
   - Expected: tcp_state_name(conn.state) equals `SYN_SENT`
   - Expected: tcp_state_name(conn.state) equals `ESTABLISHED`
   - Expected: replies.len() equals `1u64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local_ip = Ipv4Address.from_u32(0x0A00020Fu32)
val remote_ip = Ipv4Address.from_u32(0x0A000202u32)
var conn = TcpConnection.new_client(local_ip, 49152u16, remote_ip, 80u16)

val syn = conn.connect()
expect(syn.len()).to_equal(1u64)
expect(tcp_state_name(conn.state)).to_equal("SYN_SENT")

val syn_ack = TcpSegment(
    header: TcpHeader(
        src_port: 80u16,
        dst_port: 49152u16,
        seq_num: 2000u32,
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
```

</details>

#### treats a reset during active open as connection reset

1. var conn = TcpConnection new client
   - Expected: syn.len() equals `1u64`
   - Expected: replies.len() equals `0u64`
   - Expected: tcp_state_name(conn.state) equals `CLOSED`
   - Expected: conn.recv_status() equals `connection-reset`


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local_ip = Ipv4Address.from_u32(0x0A00020Fu32)
val remote_ip = Ipv4Address.from_u32(0x0A000202u32)
var conn = TcpConnection.new_client(local_ip, 49152u16, remote_ip, 80u16)
val syn = conn.connect()
expect(syn.len()).to_equal(1u64)

val rst = TcpSegment(
    header: TcpHeader(
        src_port: 80u16,
        dst_port: 49152u16,
        seq_num: 2000u32,
        ack_num: conn.snd_nxt,
        data_offset: 5u8,
        flags: TCP_FLAG_RST | TCP_FLAG_ACK,
        window: 0u16,
        checksum: 0u16,
        urgent_ptr: 0u16
    ),
    data: []
)
val replies = conn.process_segment(rst, remote_ip)
expect(replies.len()).to_equal(0u64)
expect(tcp_state_name(conn.state)).to_equal("CLOSED")
expect(conn.recv_status()).to_equal("connection-reset")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_connect_completion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0001 TCP connect completion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
