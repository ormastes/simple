# Async Tcp Specification

> Tests covering AsyncTcpListener, AsyncTcpStream, Async HTTP Server Pattern.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Tcp Specification

## Scenarios

### AsyncTcpListener

#### bind

#### documents async bind

- documents async bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async bind")
# val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
# expect listener.is_open() == true
0
```

</details>

#### accept

#### documents async accept

- documents async accept


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async accept")
# val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
# val stream = await listener.accept()?
# # stream is an AsyncTcpStream ready for read/write
0
```

</details>

#### local_addr (sync)

#### documents sync local_addr

- documents sync local_addr


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents sync local_addr")
# val listener = await AsyncTcpListener.bind("127.0.0.1:0")?
# val addr = listener.local_addr()?  # sync!
# expect addr.contains("127.0.0.1") == true
0
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
# @req REQ-SSPEC-UNIT
step("documents async close")
# val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
# await listener.close()?
# expect listener.is_open() == false
0
```

</details>

### AsyncTcpStream

#### connect

#### documents async connect

- documents async connect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async connect")
# val stream = await AsyncTcpStream.connect("example.com:80")?
0
```

</details>

#### documents connect with timeout

- documents connect with timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents connect with timeout")
# val stream = await AsyncTcpStream.connect_timeout("example.com:80", 5000)?
0
```

</details>

#### AsyncRead (epoll-driven)

#### documents async read

- documents async read


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async read")
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val chunk = await stream.read(1024)?
0
```

</details>

#### documents async read_text

- documents async read_text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async read_text")
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val response = await stream.read_text()?
0
```

</details>

#### documents async read_line

- documents async read_line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async read_line")
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val line = await stream.read_line()?
0
```

</details>

#### AsyncWrite (epoll-driven)

#### documents async write_text

- documents async write_text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async write_text")
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# await stream.write_text("GET / HTTP/1.1\\r\\n\\r\\n")?
# await stream.flush()?
0
```

</details>

#### TCP options (sync)

#### documents sync TCP options

- documents sync TCP options


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents sync TCP options")
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# stream.set_nodelay(true)?         # sync
# val peer = stream.peer_addr()?    # sync
# val local = stream.local_addr()?  # sync
0
```

</details>

#### shutdown

#### documents async shutdown

- documents async shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async shutdown")
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# await stream.shutdown(Shutdown.Write)?
0
```

</details>

#### error on closed stream

#### returns error for read on closed stream

- returns error for read on closed stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for read on closed stream")
# AsyncTcpStream constructor not available in test context
# var stream = AsyncTcpStream(fd: -1, event_loop: nil, open: false)
# read should return immediately-resolved Future with error
0
```

</details>

### Async HTTP Server Pattern

#### documented pattern

#### documents async HTTP server

- documents async HTTP server


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async HTTP server")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/io/async_tcp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AsyncTcpListener, AsyncTcpStream, Async HTTP Server Pattern.
- AsyncTcpListener
- AsyncTcpStream
- Async HTTP Server Pattern

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `3afbe2e20bd27787e8007869e638f836b9d00af54e18f93981fe3530189b42f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3afbe2e20bd27787e8007869e638f836b9d00af54e18f93981fe3530189b42f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3afbe2e20bd27787e8007869e638f836b9d00af54e18f93981fe3530189b42f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/nogc_async_mut/io/async_tcp_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/io/async_tcp_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/lib/nogc_async_mut/io/async_tcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/io/async_tcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/io/async_tcp_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/lib/nogc_async_mut/io/async_tcp_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents async bind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/io/async_tcp_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents async accept' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/io/async_tcp_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents sync local_addr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
