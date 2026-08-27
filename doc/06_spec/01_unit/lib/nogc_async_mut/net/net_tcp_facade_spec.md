# Net Tcp Facade Specification

> Tests covering std.net.tcp facade reaches the live socket path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Tcp Facade Specification

## Scenarios

### std.net.tcp facade reaches the live socket path

<details>
<summary>Advanced: binds an ephemeral loopback port and reports the kernel-assigned address</summary>

#### binds an ephemeral loopback port and reports the kernel-assigned address

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds an ephemeral loopback port and reports the kernel-assigned address
   - Expected: addr contains `127.0.0.1`
   - Expected: addr does not contain `:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds an ephemeral loopback port and reports the kernel-assigned address")
val bind_result = TcpListener.bind("127.0.0.1:0")
var listener = match bind_result:
    Err(e): panic("bind failed: {e.message}")
    Ok(l): l

val addr_result = listener.local_addr()
val addr = match addr_result:
    Err(e): panic("local_addr failed: {e.message}")
    Ok(a): a

# A silent-nil extern could not produce a real loopback address.
expect(addr.contains("127.0.0.1")).to_equal(true)
# ":0" means "pick a port"; the kernel must have replaced it.
expect(addr.contains(":0")).to_equal(false)

val _ = listener.close()
```

</details>


</details>

#### moves bytes client-to-server byte-exactly

- moves bytes client-to-server byte-exactly
   - Expected: got equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves bytes client-to-server byte-exactly")
val bind_result = TcpListener.bind("127.0.0.1:0")
var listener = match bind_result:
    Err(e): panic("bind failed: {e.message}")
    Ok(l): l
val addr = match listener.local_addr():
    Err(e): panic("local_addr failed: {e.message}")
    Ok(a): a

# Connect before accept — the OS queues it in the backlog.
var client = match TcpStream.connect(addr):
    Err(e): panic("connect failed: {e.message}")
    Ok(c): c

# ASCII "Hello"
val payload: [u8] = [72, 101, 108, 108, 111]
match client.write_all(payload):
    Err(e): panic("client write_all failed: {e.message}")
    Ok(_): pass
val _ = client.flush()

var server = match listener.accept():
    Err(e): panic("accept failed: {e.message}")
    Ok(s): s

val got = match server.read_exact(5):
    Err(e): panic("server read_exact failed: {e.message}")
    Ok(d): d

# Absolute oracle: byte-exact, not a length or substring check.
expect(got).to_equal(payload)

val _ = server.close()
val _ = client.close()
val _ = listener.close()
```

</details>

#### moves bytes server-to-client byte-exactly

- moves bytes server-to-client byte-exactly
   - Expected: got equals `reply`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves bytes server-to-client byte-exactly")
val bind_result = TcpListener.bind("127.0.0.1:0")
var listener = match bind_result:
    Err(e): panic("bind failed: {e.message}")
    Ok(l): l
val addr = match listener.local_addr():
    Err(e): panic("local_addr failed: {e.message}")
    Ok(a): a

var client = match TcpStream.connect(addr):
    Err(e): panic("connect failed: {e.message}")
    Ok(c): c

var server = match listener.accept():
    Err(e): panic("accept failed: {e.message}")
    Ok(s): s

# ASCII "PONG!"
val reply: [u8] = [80, 79, 78, 71, 33]
match server.write_all(reply):
    Err(e): panic("server write_all failed: {e.message}")
    Ok(_): pass
val _ = server.flush()

val got = match client.read_exact(5):
    Err(e): panic("client read_exact failed: {e.message}")
    Ok(d): d

expect(got).to_equal(reply)

val _ = server.close()
val _ = client.close()
val _ = listener.close()
```

</details>

#### reports the same peer port on both ends of one connection

- reports the same peer port on both ends of one connection
   - Expected: server_peer equals `client_local`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the same peer port on both ends of one connection")
val bind_result = TcpListener.bind("127.0.0.1:0")
var listener = match bind_result:
    Err(e): panic("bind failed: {e.message}")
    Ok(l): l
val addr = match listener.local_addr():
    Err(e): panic("local_addr failed: {e.message}")
    Ok(a): a

var client = match TcpStream.connect(addr):
    Err(e): panic("connect failed: {e.message}")
    Ok(c): c
var server = match listener.accept():
    Err(e): panic("accept failed: {e.message}")
    Ok(s): s

# The kernel — not Simple — brokered this pair, so the client's local
# address must equal the server's view of its peer.
val client_local = match client.local_addr():
    Err(e): panic("client local_addr failed: {e.message}")
    Ok(a): a
val server_peer = match server.peer_addr():
    Err(e): panic("server peer_addr failed: {e.message}")
    Ok(a): a

expect(server_peer).to_equal(client_local)

val _ = server.close()
val _ = client.close()
val _ = listener.close()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.net.tcp facade reaches the live socket path.
- std.net.tcp facade reaches the live socket path

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4195824a8bd65b025c52f872a37d6f70b02dc2145b21b918ba49234e461a8aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4195824a8bd65b025c52f872a37d6f70b02dc2145b21b918ba49234e461a8aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4195824a8bd65b025c52f872a37d6f70b02dc2145b21b918ba49234e461a8aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds an ephemeral loopback port and reports the kernel-assigned address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves bytes client-to-server byte-exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves bytes server-to-client byte-exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
