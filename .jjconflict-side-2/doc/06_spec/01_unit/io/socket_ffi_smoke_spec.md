# socket_ffi_smoke_spec

> Smoke spec: real socket FFI via native_tcp_* and native_udp_* externs.

<!-- sdn-diagram:id=socket_ffi_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=socket_ffi_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

socket_ffi_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=socket_ffi_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# socket_ffi_smoke_spec

Smoke spec: real socket FFI via native_tcp_* and native_udp_* externs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/01_unit/io/socket_ffi_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Smoke spec: real socket FFI via native_tcp_* and native_udp_* externs.

Tests the REAL (non-simulated) socket path confirmed working in interpreter mode.
Do NOT use rt_io_tcp_*/rt_io_udp_* (class-based io/tcp.spl API): those trigger
HIR-JIT lowering on opaque types, which falls back to interpreter after possible
double-execution. Use native_tcp_*/native_udp_* directly.

Verified ABIs (interpreter_native_net.rs):
  native_tcp_bind(addr:text) -> (handle:i64, err_code:i64)
  native_tcp_connect(addr:text) -> (handle:i64, local_addr:text, err_code:i64)
  native_tcp_accept(handle:i64) -> Result<[stream_fd:i64], text>
  native_tcp_read(handle:i64, max:i64) -> Result<[i64], text>
  native_tcp_write(handle:i64, data:[i64]) -> Result<i64, text>
  native_tcp_set_read_timeout(handle:i64, ms:i64) -> Result<i64, text>
  native_tcp_close(handle:i64) -> i64
  native_udp_bind(addr:text) -> (handle:i64, err_code:i64)
  native_udp_send_to(fd:i64, data:[i64], len:i64, addr:text) -> (sent:i64, err_code:i64)
  native_udp_recv_from(fd:i64, max:i64) -> Result<[i64], text>
      Ok payload = [len:i64, addr_text_as_element, data_array:[i64]]
  native_udp_set_read_timeout(fd:i64, ms:i64) -> Result<i64, text>
  native_udp_close(fd:i64) -> i64

Run:
  export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
  SIMPLE_EXECUTION_MODE=interpreter bin/simple test test/01_unit/io/socket_ffi_smoke_spec.spl

## Scenarios

### socket FFI smoke

#### TCP bind returns non-negative handle

- native tcp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = native_tcp_bind("127.0.0.1:19480")
val fd = r.0
val err = r.1
native_tcp_close(fd)
expect(fd).to_be_greater_than(-1)
```

</details>

#### TCP connect to bound address succeeds

- native tcp set read timeout
   - Expected: cli_err equals `0`
- native tcp close
- native tcp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val srv_r = native_tcp_bind("127.0.0.1:19481")
val srv_fd = srv_r.0
expect(srv_fd).to_be_greater_than(-1)
native_tcp_set_read_timeout(srv_fd, 3000)

val cli_r = native_tcp_connect("127.0.0.1:19481")
val cli_fd = cli_r.0
val cli_err = cli_r.2
expect(cli_fd).to_be_greater_than(-1)
expect(cli_err).to_equal(0)

native_tcp_close(cli_fd)
native_tcp_close(srv_fd)
```

</details>

#### TCP accept returns stream handle after connect

- native tcp set read timeout
- Ok
- native tcp close
- Err
- native tcp close
- native tcp close
   - Expected: acc_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val srv_r = native_tcp_bind("127.0.0.1:19482")
val srv_fd = srv_r.0
expect(srv_fd).to_be_greater_than(-1)
native_tcp_set_read_timeout(srv_fd, 3000)

val cli_r = native_tcp_connect("127.0.0.1:19482")
val cli_fd = cli_r.0
expect(cli_fd).to_be_greater_than(-1)

val acc = native_tcp_accept(srv_fd)
var acc_ok = false
match acc:
    Ok(pair):
        val stream_fd = pair.get(0)
        if stream_fd != None:
            acc_ok = true
            native_tcp_close(stream_fd!)
    Err(e):
        acc_ok = false

native_tcp_close(cli_fd)
native_tcp_close(srv_fd)
expect(acc_ok).to_equal(true)
```

</details>

#### TCP write returns positive byte count

- native tcp set read timeout
- Ok
- Err
- Ok
- Err
- native tcp close
- native tcp close
- native tcp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val srv_r = native_tcp_bind("127.0.0.1:19483")
val srv_fd = srv_r.0
native_tcp_set_read_timeout(srv_fd, 3000)

val cli_r = native_tcp_connect("127.0.0.1:19483")
val cli_fd = cli_r.0

val acc = native_tcp_accept(srv_fd)
var stream_fd = -1
match acc:
    Ok(pair):
        val maybe_fd = pair.get(0)
        if maybe_fd != None:
            stream_fd = maybe_fd!
    Err(e):
        stream_fd = -1

val msg = rt_text_to_bytes("PING")
val write_r = native_tcp_write(cli_fd, msg)
var wrote = 0
match write_r:
    Ok(n): wrote = n
    Err(e): wrote = -1

expect(wrote).to_be_greater_than(0)

if stream_fd >= 0:
    native_tcp_close(stream_fd)
native_tcp_close(cli_fd)
native_tcp_close(srv_fd)
```

</details>

#### TCP read receives bytes written by peer

- native tcp set read timeout
- Ok
- Err
- native tcp write
- native tcp set read timeout
- Ok
- Err
- native tcp close
- native tcp close
- native tcp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val srv_r = native_tcp_bind("127.0.0.1:19484")
val srv_fd = srv_r.0
native_tcp_set_read_timeout(srv_fd, 3000)

val cli_r = native_tcp_connect("127.0.0.1:19484")
val cli_fd = cli_r.0

val acc = native_tcp_accept(srv_fd)
var stream_fd = -1
match acc:
    Ok(pair):
        val maybe_fd = pair.get(0)
        if maybe_fd != None:
            stream_fd = maybe_fd!
    Err(e):
        stream_fd = -1

# Client writes
val msg = rt_text_to_bytes("HELLO")
native_tcp_write(cli_fd, msg)

# Server reads
var recv_len = -1
if stream_fd >= 0:
    native_tcp_set_read_timeout(stream_fd, 2000)
    val read_r = native_tcp_read(stream_fd, 4096)
    match read_r:
        Ok(data): recv_len = data.len()
        Err(e): recv_len = -1

expect(recv_len).to_be_greater_than(0)

if stream_fd >= 0:
    native_tcp_close(stream_fd)
native_tcp_close(cli_fd)
native_tcp_close(srv_fd)
```

</details>

#### UDP bind returns non-negative handle

- native udp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = native_udp_bind("127.0.0.1:19485")
val fd = r.0
val err = r.1
native_udp_close(fd)
expect(fd).to_be_greater_than(-1)
```

</details>

<details>
<summary>Advanced: UDP send_to and recv_from loopback succeeds</summary>

#### UDP send_to and recv_from loopback succeeds

- native udp set read timeout
   - Expected: serr equals `0`
- Ok
- Err
- native udp close


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = "127.0.0.1:19486"
val bind_r = native_udp_bind(addr)
val fd = bind_r.0
expect(fd).to_be_greater_than(-1)

native_udp_set_read_timeout(fd, 2000)

val msg = rt_text_to_bytes("PING-UDP")
val send_r = native_udp_send_to(fd, msg, msg.len(), addr)
val sent = send_r.0
val serr = send_r.1
expect(sent).to_be_greater_than(0)
expect(serr).to_equal(0)

val recv_r = native_udp_recv_from(fd, 4096)
var recv_len = -1
match recv_r:
    Ok(arr):
        val maybe_len = arr.get(0)
        if maybe_len != None:
            recv_len = maybe_len!
    Err(e):
        recv_len = -1

native_udp_close(fd)
expect(recv_len).to_be_greater_than(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
