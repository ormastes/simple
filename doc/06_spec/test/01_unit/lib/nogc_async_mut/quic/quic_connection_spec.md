# Quic Connection Specification

> <details>

<!-- sdn-diagram:id=quic_connection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=quic_connection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

quic_connection_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=quic_connection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = quic_config_default()
expect cfg.version == 1
```

</details>

#### sets max idle timeout to 30 000 ms per RFC 9000 §10.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = quic_config_default()
expect cfg.max_idle_timeout == 30000
```

</details>

#### sets max bidirectional streams to 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = quic_config_default()
expect cfg.max_streams_bidi == 100
```

</details>

#### sets initial window to 65 535 bytes (64 KiB)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = quic_config_default()
expect cfg.initial_window == 65535
```

</details>

#### Connection roles

#### tracks server role on accept

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = make_server_conn(42)
expect conn.is_server == true
```

</details>

#### tracks client role on connect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = make_client_conn(7)
expect conn.is_server == false
```

</details>

#### stores the opaque handle for extern dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = make_server_conn(99)
expect conn.handle == 99
```

</details>

#### Handshake state

#### starts as not established

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = make_server_conn(1)
expect conn.established == false
```

</details>

#### transitions to established when flag is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = make_server_conn(5)
val done = quic_close_local(conn, "test shutdown")
expect done.closed == true
```

</details>

#### clears established flag on close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = QuicConnection { handle: 3, is_server: true, established: true, closed: false }
val done = quic_close_local(base, "graceful")
expect done.established == false
```

</details>

#### preserves handle after close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
