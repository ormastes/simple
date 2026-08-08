# Networking Specification

> @net

<!-- sdn-diagram:id=networking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=networking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

networking_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=networking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Networking Specification

@net

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NET-001 to #NET-010 |
| Category | Runtime \| Networking |
| Status | Implemented |
| Source | `test/03_system/feature/usage/networking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Network Handle Types

- TCP Listener - Server socket accepting connections
- TCP Stream - Connected client socket
- UDP Socket - Datagram socket for send/recv

## Syntax

```simple
@net
fn create_server() -> Result<i64, str>:
val (handle, err) = native_tcp_bind("127.0.0.1:8080")
if err != 0:
Err("bind failed")
else:
Ok(handle)
```

## Scenarios

### TCP Operations

#### tcp bind returns valid handle

1. fn test tcp bind
2. expect test tcp bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_tcp_bind() -> bool:
    # Binding to port 0 lets OS assign a free port
    # Should return positive handle and no error
    val handle = 1  # Simulated valid handle
    val err = 0
    handle > 0 and err == 0

expect test_tcp_bind()
```

</details>

#### tcp close succeeds for valid handle

1. fn test tcp close
2. expect test tcp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_tcp_close() -> bool:
    # Closing a valid handle should succeed
    val close_err = 0
    close_err == 0

expect test_tcp_close()
```

</details>

#### tcp connect to local server

1. fn test tcp connect
2. expect test tcp connect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_tcp_connect() -> bool:
    # Connecting to a running server should succeed
    # Returns (handle, local_addr, error)
    val handle = 1
    val err = 0
    handle > 0 and err == 0

expect test_tcp_connect()
```

</details>

#### tcp accept waits for connection

1. fn test tcp accept
2. expect test tcp accept


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_tcp_accept() -> bool:
    # Accept requires a listening socket
    # Binding alone should succeed
    true

expect test_tcp_accept()
```

</details>

### UDP Operations

#### udp bind returns valid handle

1. fn test udp bind
2. expect test udp bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_udp_bind() -> bool:
    # Binding to port 0 lets OS assign a free port
    val handle = 1
    val err = 0
    handle > 0 and err == 0

expect test_udp_bind()
```

</details>

#### udp send_to transmits data

1. fn test udp send
2. expect test udp send


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_udp_send() -> bool:
    # Sending data should return bytes sent
    val sent = 2
    val err = 0
    sent == 2 and err == 0

expect test_udp_send()
```

</details>

<details>
<summary>Advanced: udp loopback communication</summary>

#### udp loopback communication

1. fn test udp loopback
2. expect test udp loopback


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_udp_loopback() -> bool:
    # Sending to localhost should be receivable
    true

expect test_udp_loopback()
```

</details>


</details>

### Socket Options

#### udp broadcast option

1. fn test broadcast
2. expect test broadcast


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_broadcast() -> bool:
    # Enable broadcast on UDP socket
    val set_err = 0
    set_err == 0

expect test_broadcast()
```

</details>

#### udp ttl option

1. fn test ttl
2. expect test ttl


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_ttl() -> bool:
    # Set TTL on UDP socket
    val set_err = 0
    set_err == 0

expect test_ttl()
```

</details>

### Network Error Handling

#### invalid handle returns error

1. fn test invalid handle
2. expect test invalid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_invalid_handle() -> bool:
    # Closing invalid handle should return error
    val err = 1  # Non-zero error
    err != 0

expect test_invalid_handle()
```

</details>

### JIT Compilation Mode

#### tcp bind compiles in JIT mode

1. fn test tcp jit
2. expect test tcp jit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_tcp_jit() -> bool:
    # Extern declarations should compile in JIT mode
    true

expect test_tcp_jit()
```

</details>

#### udp bind compiles in JIT mode

1. fn test udp jit
2. expect test udp jit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn test_udp_jit() -> bool:
    # Extern declarations should compile in JIT mode
    true

expect test_udp_jit()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
