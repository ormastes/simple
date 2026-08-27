# Net Connect Completion Specification

> Tests covering FR-NET-0001 TCP connect completion.

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

- keeps a queued SYN non-writable until TCP reaches ESTABLISHED
   - Expected: table.connect_status(fd) equals `in-progress`
   - Expected: table.is_write_ready(fd) is false
   - Expected: socket_state_name(connecting.state) equals `CONNECTING`
   - Expected: table.mark_connected_by_conn(101u64) is true
   - Expected: table.connect_status(fd) equals `established`
   - Expected: table.is_write_ready(fd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps a queued SYN non-writable until TCP reaches ESTABLISHED")
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
    fail("connecting socket disappeared after attach_connecting")

expect(table.mark_connected_by_conn(101u64)).to_equal(true)
expect(table.connect_status(fd)).to_equal("established")
expect(table.is_write_ready(fd)).to_equal(true)
```

</details>

#### surfaces refused and timeout completion separately

- surfaces refused and timeout completion separately
   - Expected: table.mark_connect_failed_by_conn(102u64, "refused") is true
   - Expected: table.connect_status(fd_refused) equals `refused`
   - Expected: table.is_write_ready(fd_refused) is false
   - Expected: table.mark_connect_failed_by_conn(103u64, "timeout") is true
   - Expected: table.connect_status(fd_timeout) equals `timeout`
   - Expected: table.is_write_ready(fd_timeout) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surfaces refused and timeout completion separately")
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

- publishes completion only after a valid SYN ACK
   - Expected: syn.len() equals `1u64`
   - Expected: tcp_state_name(conn.state) equals `SYN_SENT`
   - Expected: tcp_state_name(conn.state) equals `ESTABLISHED`
   - Expected: replies.len() equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes completion only after a valid SYN ACK")
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

- treats a reset during active open as connection reset
   - Expected: syn.len() equals `1u64`
   - Expected: replies.len() equals `0u64`
   - Expected: tcp_state_name(conn.state) equals `CLOSED`
   - Expected: conn.recv_status() equals `connection-reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats a reset during active open as connection reset")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0001 TCP connect completion.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `635a7ae62e7cef692ba523705554bc5c194c011694dfbd1a599ab81b7a031cd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `635a7ae62e7cef692ba523705554bc5c194c011694dfbd1a599ab81b7a031cd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `635a7ae62e7cef692ba523705554bc5c194c011694dfbd1a599ab81b7a031cd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/net_connect_completion_spec.spl
mirror: doc/06_spec/03_system/os/net_connect_completion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_connect_completion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_connect_completion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_connect_completion_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a queued SYN non-writable until TCP reaches ESTABLISHED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_connect_completion_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'surfaces refused and timeout completion separately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_connect_completion_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes completion only after a valid SYN ACK' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
