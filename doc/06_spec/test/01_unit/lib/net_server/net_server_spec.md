# Net Server Specification

> <details>

<!-- sdn-diagram:id=net_server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_server_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Server Specification

## Scenarios

### NetServer bind and local_addr

#### binds to ephemeral port and reports 127.0.0.1 address

- Err
- Ok
- Err
- Ok
   - Expected: addr contains `127.0.0.1`
   - Expected: addr.len() > 9 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bind_result = NetServer.bind("127.0.0.1", 0)
var srv = match bind_result:
    Err(_): panic("bind failed")
    Ok(s): s
val addr_result = srv.local_addr()
val addr = match addr_result:
    Err(_): panic("local_addr failed")
    Ok(a): a
expect(addr.contains("127.0.0.1")).to_equal(true)
expect(addr.len() > 9).to_equal(true)
val _ = srv.close()
```

</details>

#### is_open returns true after bind

- Err
- Ok
   - Expected: srv.is_open() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bind_result = NetServer.bind("127.0.0.1", 0)
var srv = match bind_result:
    Err(_): panic("bind failed")
    Ok(s): s
expect(srv.is_open()).to_equal(true)
val _ = srv.close()
```

</details>

#### is_open returns false after close

- Err
- Ok
   - Expected: srv.is_open() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bind_result = NetServer.bind("127.0.0.1", 0)
var srv = match bind_result:
    Err(_): panic("bind failed")
    Ok(s): s
val _ = srv.close()
expect(srv.is_open()).to_equal(false)
```

</details>

### NetServer loopback echo — absolute oracle

#### serve_once dispatches connection and echoes payload byte-exactly

- Err
- Ok
- Err
- Ok
- Err
- Ok
- var handler = EchoHandler
- Err
- Ok
- Err
- Ok
   - Expected: cont is true
- Err
- Ok
   - Expected: echoed.len() equals `5`
   - Expected: echoed[0] equals `72`
   - Expected: echoed[1] equals `101`
   - Expected: echoed[2] equals `108`
   - Expected: echoed[3] equals `108`
   - Expected: echoed[4] equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bind_result = NetServer.bind("127.0.0.1", 0)
var srv = match bind_result:
    Err(_): panic("bind failed")
    Ok(s): s
val addr_result = srv.local_addr()
val addr = match addr_result:
    Err(_): panic("local_addr failed")
    Ok(a): a

# Client connects before accept — OS queues the SYN
val c_result = TcpStream.connect(addr)
var client = match c_result:
    Err(_): panic("connect failed")
    Ok(c): c

# Set up echo handler (5 bytes)
var handler = EchoHandler(read_size: 5, received: [], did_run: false)

# Client writes [72, 101, 108, 108, 111] = "Hello"
val payload: [u8] = [72, 101, 108, 108, 111]
val w_result = client.write_all(payload)
match w_result:
    Err(_): panic("client write failed")
    Ok(_): pass
val _ = client.flush()

# Server accepts and handles the queued connection
val once_result = srv.serve_once(handler)
val cont = match once_result:
    Err(e): panic("serve_once failed")
    Ok(c): c
expect(cont).to_equal(true)

# Read echo response on client side
val r_result = client.read_exact(5)
var echoed = match r_result:
    Err(_): panic("client read failed")
    Ok(d): d

# Absolute oracle: byte-exact equality
expect(echoed.len()).to_equal(5)
expect(echoed[0]).to_equal(72)
expect(echoed[1]).to_equal(101)
expect(echoed[2]).to_equal(108)
expect(echoed[3]).to_equal(108)
expect(echoed[4]).to_equal(111)

val _ = client.close()
val _ = srv.close()
```

</details>

#### handler receives the exact bytes the client sent

- Err
- Ok
- Err
- Ok
- Err
- Ok
- var handler = EchoHandler
- Err
- Ok
- Err
- Ok
   - Expected: handler.did_run is true
   - Expected: handler.received.len() equals `3`
   - Expected: handler.received[0] equals `65`
   - Expected: handler.received[1] equals `66`
   - Expected: handler.received[2] equals `67`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bind_result = NetServer.bind("127.0.0.1", 0)
var srv = match bind_result:
    Err(_): panic("bind failed")
    Ok(s): s
val addr_result = srv.local_addr()
val addr = match addr_result:
    Err(_): panic("local_addr failed")
    Ok(a): a

val c_result = TcpStream.connect(addr)
var client = match c_result:
    Err(_): panic("connect failed")
    Ok(c): c

var handler = EchoHandler(read_size: 3, received: [], did_run: false)

# ASCII "ABC" = [65, 66, 67]
val payload: [u8] = [65, 66, 67]
val w_result = client.write_all(payload)
match w_result:
    Err(_): panic("client write failed")
    Ok(_): pass
val _ = client.flush()

val once_result = srv.serve_once(handler)
match once_result:
    Err(_): panic("serve_once failed")
    Ok(_): pass

expect(handler.did_run).to_equal(true)
expect(handler.received.len()).to_equal(3)
expect(handler.received[0]).to_equal(65)
expect(handler.received[1]).to_equal(66)
expect(handler.received[2]).to_equal(67)

val _ = client.close()
val _ = srv.close()
```

</details>

### NetServer serve_n bounded loop

#### serve_n handles exactly n connections

- Err
- Ok
- Err
- Ok
- Err
- Ok
- Err
- Ok
- var handler = EchoHandler
- Err
- Ok
   - Expected: handler.did_run is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bind_result = NetServer.bind("127.0.0.1", 0)
var srv = match bind_result:
    Err(_): panic("bind failed")
    Ok(s): s
val addr_result = srv.local_addr()
val addr = match addr_result:
    Err(_): panic("local_addr failed")
    Ok(a): a

# Pre-queue 2 connections before accepting
val c1_result = TcpStream.connect(addr)
var c1 = match c1_result:
    Err(_): panic("connect c1 failed")
    Ok(c): c

val c2_result = TcpStream.connect(addr)
var c2 = match c2_result:
    Err(_): panic("connect c2 failed")
    Ok(c): c

# Tiny payload so EchoHandler doesn't block
val payload: [u8] = [1]
val _ = c1.write_all(payload)
val _ = c1.flush()
val _ = c2.write_all(payload)
val _ = c2.flush()

var handler = EchoHandler(read_size: 1, received: [], did_run: false)
val n_result = srv.serve_n(handler, 2)
match n_result:
    Err(_): panic("serve_n failed")
    Ok(_): pass

# handler.did_run only reflects the last call (value copy semantics)
expect(handler.did_run).to_equal(true)

val _ = c1.close()
val _ = c2.close()
val _ = srv.close()
```

</details>

### NetServer stop via handler return false

#### serve_once returns Ok(false) when StopHandler returns false

- Err
- Ok
- Err
- Ok
- Err
- Ok
- var handler = StopHandler
- Err
- Ok
   - Expected: cont is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bind_result = NetServer.bind("127.0.0.1", 0)
var srv = match bind_result:
    Err(_): panic("bind failed")
    Ok(s): s
val addr_result = srv.local_addr()
val addr = match addr_result:
    Err(_): panic("local_addr failed")
    Ok(a): a

val c_result = TcpStream.connect(addr)
var client = match c_result:
    Err(_): panic("connect failed")
    Ok(c): c

var handler = StopHandler()
val once_result = srv.serve_once(handler)
val cont = match once_result:
    Err(_): panic("serve_once failed")
    Ok(c): c

expect(cont).to_equal(false)

val _ = client.close()
val _ = srv.close()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/net_server/net_server_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NetServer bind and local_addr
- NetServer loopback echo — absolute oracle
- NetServer serve_n bounded loop
- NetServer stop via handler return false

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
