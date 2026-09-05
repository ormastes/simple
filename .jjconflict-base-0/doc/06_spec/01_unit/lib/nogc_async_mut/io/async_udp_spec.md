# Async Udp Specification

> Tests covering AsyncUdpSocket.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Udp Specification

## Scenarios

### AsyncUdpSocket

#### bind

#### documents async bind

- documents async bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("documents async bind")
# val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
# expect socket.is_open() == true
pass
```

</details>

#### send_to and recv_from

#### documents async datagram exchange

- documents async datagram exchange


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("documents async datagram exchange")
# val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
# await socket.send_to([72, 105], "127.0.0.1:9001")?
# val (data, sender) = await socket.recv_from(1024)?
# await socket.close()?
pass
```

</details>

#### connected mode

#### documents async connected mode

- documents async connected mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("documents async connected mode")
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

- documents broadcast setup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("documents broadcast setup")
# val socket = await AsyncUdpSocket.bind("0.0.0.0:0")?
# socket.set_broadcast(true)?  # sync
# await socket.send_to(data, "255.255.255.255:9000")?
pass
```

</details>

#### close

#### documents async close

- documents async close


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("documents async close")
# val socket = await AsyncUdpSocket.bind("127.0.0.1:0")?
# await socket.close()?
# expect socket.is_open() == false
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AsyncUdpSocket.
- AsyncUdpSocket

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `154fe7b980792aa8d11c4f393eb9e1bb35d202f6c08832944d47f88ee453b113`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `154fe7b980792aa8d11c4f393eb9e1bb35d202f6c08832944d47f88ee453b113`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `154fe7b980792aa8d11c4f393eb9e1bb35d202f6c08832944d47f88ee453b113`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/io/async_udp_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_async_mut/io/async_udp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/io/async_udp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents async bind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents async datagram exchange' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/async_udp_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents async connected mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
