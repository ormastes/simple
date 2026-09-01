# Quic Connection Specification

> Tests covering QUIC Connection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quic Connection Specification

## Scenarios

### QUIC Connection

#### Default configuration

#### creates default config with RFC 9000 version 1

- creates default config with RFC 9000 version 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default config with RFC 9000 version 1")
val cfg = quic_config_default()
expect cfg.version == 1
```

</details>

#### sets max idle timeout to 30 000 ms per RFC 9000 §10.1

- sets max idle timeout to 30 000 ms per RFC 9000 §10.1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets max idle timeout to 30 000 ms per RFC 9000 §10.1")
val cfg = quic_config_default()
expect cfg.max_idle_timeout == 30000
```

</details>

#### sets max bidirectional streams to 100

- sets max bidirectional streams to 100


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets max bidirectional streams to 100")
val cfg = quic_config_default()
expect cfg.max_streams_bidi == 100
```

</details>

#### sets initial window to 65 535 bytes (64 KiB)

- sets initial window to 65 535 bytes (64 KiB)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets initial window to 65 535 bytes (64 KiB)")
val cfg = quic_config_default()
expect cfg.initial_window == 65535
```

</details>

#### Connection roles

#### tracks server role on accept

- tracks server role on accept


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks server role on accept")
val conn = make_server_conn(42)
expect conn.is_server == true
```

</details>

#### tracks client role on connect

- tracks client role on connect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks client role on connect")
val conn = make_client_conn(7)
expect conn.is_server == false
```

</details>

#### stores the opaque handle for extern dispatch

- stores the opaque handle for extern dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the opaque handle for extern dispatch")
val conn = make_server_conn(99)
expect conn.handle == 99
```

</details>

#### Handshake state

#### starts as not established

- starts as not established


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts as not established")
val conn = make_server_conn(1)
expect conn.established == false
```

</details>

#### transitions to established when flag is set

- transitions to established when flag is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions to established when flag is set")
val base = make_server_conn(1)
val up = QuicConnection {
    handle: base.handle,
    is_server: base.is_server,
    established: true,
    closed: false
}
expect up.established == true
```

</details>

#### Closure

#### closes connection and sets closed flag

- closes connection and sets closed flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes connection and sets closed flag")
val conn = make_server_conn(5)
val done = quic_close_local(conn, "test shutdown")
expect done.closed == true
```

</details>

#### clears established flag on close

- clears established flag on close


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears established flag on close")
val base = QuicConnection { handle: 3, is_server: true, established: true, closed: false }
val done = quic_close_local(base, "graceful")
expect done.established == false
```

</details>

#### preserves handle after close

- preserves handle after close


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves handle after close")
val conn = make_server_conn(77)
val done = quic_close_local(conn, "bye")
expect done.handle == 77
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QUIC Connection.
- QUIC Connection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `d736b61d9bdf211ed1d9028c66d5d72dc3c4722a855ee23201d0c416595838b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d736b61d9bdf211ed1d9028c66d5d72dc3c4722a855ee23201d0c416595838b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d736b61d9bdf211ed1d9028c66d5d72dc3c4722a855ee23201d0c416595838b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default config with RFC 9000 version 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets max idle timeout to 30 000 ms per RFC 9000 §10.1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_connection_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets max bidirectional streams to 100' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
