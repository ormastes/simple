# Quic Connection Provider Gate Specification

> Tests covering QUIC transport is gated on the provider, QUIC constructors fail closed, QUIC operations refuse an unusable connection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quic Connection Provider Gate Specification

## Scenarios

### QUIC transport is gated on the provider

#### reports the provider as unusable while the TLS blocker is open

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the provider as unusable while the TLS blocker is open


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the provider as unusable while the TLS blocker is open")
expect(quic_provider_is_usable(quic_provider_check())).to_be(false)
```

</details>

#### never treats a zero-handle connection as usable

- never treats a zero-handle connection as usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never treats a zero-handle connection as usable")
expect(quic_connection_is_usable(_zero_handle_connection())).to_be(false)
```

</details>

#### never treats a negative-handle connection as usable

- never treats a negative-handle connection as usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never treats a negative-handle connection as usable")
val conn = QuicConnection { handle: -1, is_server: false, established: false, closed: false }
expect(quic_connection_is_usable(conn)).to_be(false)
```

</details>

#### never treats a closed connection as usable

- never treats a closed connection as usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never treats a closed connection as usable")
val conn = QuicConnection { handle: 7, is_server: false, established: false, closed: true }
expect(quic_connection_is_usable(conn)).to_be(false)
```

</details>

### QUIC constructors fail closed

#### quic_accept returns a terminal connection with no handle

- quic_accept returns a terminal connection with no handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_accept returns a terminal connection with no handle")
val conn = quic_accept("0011223344556677", quic_config_default())
expect(conn.handle).to_be(0)
expect(conn.closed).to_be(true)
expect(conn.established).to_be(false)
expect(conn.is_server).to_be(true)
```

</details>

#### quic_connect returns a terminal connection with no handle

- quic_connect returns a terminal connection with no handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_connect returns a terminal connection with no handle")
val conn = quic_connect("example.com", "0011223344556677", quic_config_default())
expect(conn.handle).to_be(0)
expect(conn.closed).to_be(true)
expect(conn.is_server).to_be(false)
```

</details>

### QUIC operations refuse an unusable connection

#### quic_feed_udp does not establish a connection

- quic_feed_udp does not establish a connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_feed_udp does not establish a connection")
val out = quic_feed_udp(_zero_handle_connection(), "datagram", 8)
expect(out.established).to_be(false)
expect(out.closed).to_be(true)
expect(out.handle).to_be(0)
```

</details>

#### quic_get_outgoing emits no bytes

- quic_get_outgoing emits no bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_get_outgoing emits no bytes")
val out = quic_get_outgoing(_zero_handle_connection())
expect(out.data_len).to_be(0)
expect(out.data).to_be("")
```

</details>

#### quic_stream_recv reads no bytes

- quic_stream_recv reads no bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_stream_recv reads no bytes")
val read = quic_stream_recv(_zero_handle_connection(), 0, 1200)
expect(read.data_len).to_be(0)
expect(read.data).to_be("")
```

</details>

#### quic_stream_send reports failure instead of writing

- quic_stream_send reports failure instead of writing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_stream_send reports failure instead of writing")
expect(quic_stream_send(_zero_handle_connection(), 0, "payload", true)).to_be(-1)
```

</details>

#### quic_close stays terminal without a native call

- quic_close stays terminal without a native call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_close stays terminal without a native call")
val closed = quic_close(_zero_handle_connection(), "bye")
expect(closed.closed).to_be(true)
expect(closed.handle).to_be(0)
```

</details>

#### quic_check_timeout cannot promote an unusable connection

- quic_check_timeout cannot promote an unusable connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_check_timeout cannot promote an unusable connection")
val ticked = quic_check_timeout(_zero_handle_connection())
expect(ticked.established).to_be(false)
expect(ticked.closed).to_be(true)
```

</details>

#### quic_timeout_millis reports no timer

- quic_timeout_millis reports no timer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quic_timeout_millis reports no timer")
expect(quic_timeout_millis(_zero_handle_connection())).to_be(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QUIC transport is gated on the provider, QUIC constructors fail closed, QUIC operations refuse an unusable connection.
- QUIC transport is gated on the provider
- QUIC constructors fail closed
- QUIC operations refuse an unusable connection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `a1e8765eb768fba7f83a708ccfca6ae753f534675bf6034b0ed252928d10df82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1e8765eb768fba7f83a708ccfca6ae753f534675bf6034b0ed252928d10df82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1e8765eb768fba7f83a708ccfca6ae753f534675bf6034b0ed252928d10df82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the provider as unusable while the TLS blocker is open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never treats a zero-handle connection as usable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_connection_provider_gate_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never treats a negative-handle connection as usable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
