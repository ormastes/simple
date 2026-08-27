# Net Tcp Socket Data Path Specification

> Tests covering FR-NET-0002 TCP socket data path semantics.

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

- reports would-block when no receive data is available
   - Expected: conn.recv_status() equals `would-block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports would-block when no receive data is available")
var conn = established(TCP_DEFAULT_WINDOW)
match conn.recv_data_result(16u64):
    Ok(_): fail("recv_data_result unexpectedly returned data when receive buffer was empty")
    Err(msg): expect(msg).to_equal("would-block")
expect(conn.recv_status()).to_equal("would-block")
```

</details>

#### returns partial receive chunks in order

- returns partial receive chunks in order
   - Expected: replies.len() equals `1u64`
   - Expected: conn.recv_status() equals `ready`
   - Expected: data.len() equals `2u64`
   - Expected: data[0] equals `1u8`
   - Expected: data[1] equals `2u8`
   - Expected: data.len() equals `1u64`
   - Expected: data[0] equals `3u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns partial receive chunks in order")
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

- caps queued sends by the advertised window
   - Expected: conn.send_buf.len() equals `4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caps queued sends by the advertised window")
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

- exposes peer close after FIN
   - Expected: replies.len() equals `1u64`
   - Expected: conn.recv_status() equals `peer-closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes peer close after FIN")
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

- propagates reset as a receive and send error
   - Expected: replies.len() equals `0u64`
   - Expected: conn.recv_status() equals `connection-reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates reset as a receive and send error")
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
    Ok(_): fail("recv_data_result unexpectedly succeeded after RST")
    Err(msg): expect(msg).to_equal("connection-reset")
match conn.send_data([1u8]):
    Ok(_): fail("send_data unexpectedly succeeded after RST")
    Err(msg): expect(msg).to_equal("connection-reset")
```

</details>

#### reports retransmission timeout after retry exhaustion

- reports retransmission timeout after retry exhaustion
   - Expected: syn.len() equals `1u64`
   - Expected: conn.retransmit_status_at(10000000000u64) equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports retransmission timeout after retry exhaustion")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0002 TCP socket data path semantics.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7fc91a407e0384e4e01c07bc095ef3971e3f340eda4d607a89bf2f705a499cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7fc91a407e0384e4e01c07bc095ef3971e3f340eda4d607a89bf2f705a499cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7fc91a407e0384e4e01c07bc095ef3971e3f340eda4d607a89bf2f705a499cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/net_tcp_socket_data_path_spec.spl
mirror: doc/06_spec/03_system/os/net_tcp_socket_data_path_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_tcp_socket_data_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_tcp_socket_data_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_tcp_socket_data_path_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports would-block when no receive data is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_tcp_socket_data_path_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns partial receive chunks in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_tcp_socket_data_path_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caps queued sends by the advertised window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
