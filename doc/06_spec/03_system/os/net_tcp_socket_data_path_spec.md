# Net Tcp Socket Data Path Specification

> 1. var conn = established

<!-- sdn-diagram:id=net_tcp_socket_data_path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_tcp_socket_data_path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_tcp_socket_data_path_spec -> std
net_tcp_socket_data_path_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_tcp_socket_data_path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Tcp Socket Data Path Specification

## Scenarios

### FR-NET-0002 TCP socket data path semantics

#### recv readiness

#### reports would-block when no receive data is available

1. var conn = established

2. Ok

3. Err
   - Expected: conn.recv_status() equals `would-block`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var conn = established(TCP_DEFAULT_WINDOW)
match conn.recv_data_result(16u64):
    Ok(_): expect(false).to_equal(true)
    Err(msg): expect(msg).to_equal("would-block")
expect(conn.recv_status()).to_equal("would-block")
```

</details>

#### returns partial receive chunks in order

1. var conn = established
   - Expected: replies.len() equals `1u64`
   - Expected: conn.recv_status() equals `ready`

2. Ok
   - Expected: data.len() equals `2u64`
   - Expected: data[0] equals `1u8`
   - Expected: data[1] equals `2u8`

3. Err

4. Ok
   - Expected: data.len() equals `1u64`
   - Expected: data[0] equals `3u8`

5. Err


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val remote_ip = Ipv4Address.from_u32(0x0A000202u32)
var conn = established(TCP_DEFAULT_WINDOW)
val segment = data_segment(conn, [1u8, 2u8, 3u8])
val replies = conn.process_segment(segment, remote_ip)
expect(replies.len()).to_equal(1u64)
expect(conn.recv_status()).to_equal("ready")

match conn.recv_data_result(2u64):
    Ok(data):
        expect(data.len()).to_equal(2u64)
        expect(data[0]).to_equal(1u8)
        expect(data[1]).to_equal(2u8)
    Err(msg): expect(msg.len()).to_equal(0u64)

match conn.recv_data_result(8u64):
    Ok(data):
        expect(data.len()).to_equal(1u64)
        expect(data[0]).to_equal(3u8)
    Err(msg): expect(msg.len()).to_equal(0u64)
```

</details>

#### send readiness

#### caps queued sends by the advertised window

1. var conn = established

2. Ok

3. Err
   - Expected: conn.send_buf.len() equals `4u64`

4. Ok

5. Err


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var conn = established(4u16)
match conn.send_data([1u8, 2u8, 3u8, 4u8, 5u8, 6u8]):
    Ok(n): expect(n).to_equal(4u64)
    Err(msg): expect(msg.len()).to_equal(0u64)
expect(conn.send_buf.len()).to_equal(4u64)

match conn.send_data([7u8]):
    Ok(n): expect(n).to_equal(0u64)
    Err(msg): expect(msg).to_contain("would-block")
```

</details>

#### close and error propagation

#### exposes peer close after FIN

1. var conn = established
   - Expected: replies.len() equals `1u64`
   - Expected: conn.recv_status() equals `peer-closed`

2. Ok

3. Err


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val remote_ip = Ipv4Address.from_u32(0x0A000202u32)
var conn = established(TCP_DEFAULT_WINDOW)
val fin = TcpSegment(
    header: TcpHeader(
        src_port: 80u16,
        dst_port: 49152u16,
        seq_num: conn.rcv_nxt,
        ack_num: conn.snd_nxt,
        data_offset: 5u8,
        flags: TCP_FLAG_FIN | TCP_FLAG_ACK,
        window: TCP_DEFAULT_WINDOW,
        checksum: 0u16,
        urgent_ptr: 0u16
    ),
    data: []
)
val replies = conn.process_segment(fin, remote_ip)
expect(replies.len()).to_equal(1u64)
expect(conn.recv_status()).to_equal("peer-closed")
match conn.recv_data_result(16u64):
    Ok(data): expect(data.len()).to_equal(0u64)
    Err(msg): expect(msg.len()).to_equal(0u64)
```

</details>

#### propagates reset as a receive and send error

1. var conn = established
   - Expected: replies.len() equals `0u64`
   - Expected: conn.recv_status() equals `connection-reset`

2. Ok

3. Err

4. Ok

5. Err


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val remote_ip = Ipv4Address.from_u32(0x0A000202u32)
var conn = established(TCP_DEFAULT_WINDOW)
val rst = TcpSegment(
    header: TcpHeader(
        src_port: 80u16,
        dst_port: 49152u16,
        seq_num: conn.rcv_nxt,
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
expect(conn.recv_status()).to_equal("connection-reset")
match conn.recv_data_result(16u64):
    Ok(_): expect(false).to_equal(true)
    Err(msg): expect(msg).to_equal("connection-reset")
match conn.send_data([1u8]):
    Ok(_): expect(false).to_equal(true)
    Err(msg): expect(msg).to_equal("connection-reset")
```

</details>

#### reports retransmission timeout after retry exhaustion

1. Ipv4Address from u32

2. Ipv4Address from u32
   - Expected: syn.len() equals `1u64`
   - Expected: conn.retransmit_status_at(10000000000u64) equals `timeout`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var conn = TcpConnection.new_client(
    Ipv4Address.from_u32(0x0A00020Fu32),
    49152u16,
    Ipv4Address.from_u32(0x0A000202u32),
    80u16
)
val syn = conn.connect()
expect(syn.len()).to_equal(1u64)

expect(conn.retransmit_status_at(10000000000u64)).to_equal("timeout")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_tcp_socket_data_path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0002 TCP socket data path semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
