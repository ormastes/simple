# X25519mlkem768 Browser Tls Fail Closed Specification

> Tests covering X25519MLKEM768 browser TLS fail-closed policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Browser Tls Fail Closed Specification

## Scenarios

### X25519MLKEM768 browser TLS fail-closed policy

#### should REQ-017 rejects disabled certificate verification before transport

- Reject an insecure browser certificate-verification configuration
- logger,  browser tls config


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject an insecure browser certificate-verification configuration")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, false, []))
match manager.handshake_address(
    "192.0.2.1", "example.test", 443, 100
):
    case Ok(_): fail("browser accepted disabled peer verification")
    case Err(error):
        expect(error.message).to_equal(
            "TLS peer verification cannot be disabled for browser connections")
```

</details>

#### should REQ-017 rejects an empty service identity before transport

- Reject browser TLS without a certificate service identity
- logger,  browser tls config
   - Expected: error.message equals `TLS handshake: empty hostname`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject browser TLS without a certificate service identity")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, true, []))
match manager.handshake_address("192.0.2.1", "", 443, 100):
    case Ok(_): fail("browser accepted an empty certificate identity")
    case Err(error):
        expect(error.message).to_equal("TLS handshake: empty hostname")
```

</details>

#### should NFR-018 rejects invalid ports and expired deadlines before transport

- Validate transport bounds before opening a socket
- logger,  browser tls config
   - Expected: error.message equals `TLS handshake: invalid port 0`
   - Expected: error.message equals `TLS handshake: deadline exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate transport bounds before opening a socket")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, true, []))
match manager.handshake_address(
    "192.0.2.1", "example.test", 0, 100
):
    case Ok(_): fail("browser accepted an invalid port")
    case Err(error):
        expect(error.message).to_equal("TLS handshake: invalid port 0")
match manager.handshake_address(
    "192.0.2.1", "example.test", 443, 0
):
    case Ok(_): fail("browser accepted an expired deadline")
    case Err(error):
        expect(error.message).to_equal("TLS handshake: deadline exceeded")
```

</details>

#### should REQ-017 rejects TLS 1.2 on the pure-Simple hybrid browser path

- Require TLS 1.3 for the hybrid browser connection
-  browser tls config


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require TLS 1.3 for the hybrid browser connection")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger,
    _browser_tls_config(TlsVersion.Tls12, true, [[1u8]])
)
match manager.handshake_address(
    "192.0.2.1", "example.test", 443, 100
):
    case Ok(_): fail("hybrid browser path accepted TLS 1.2")
    case Err(error):
        expect(error.message).to_equal(
            "Pure-Simple browser HTTPS requires a TLS 1.3 minimum")
```

</details>

#### should NFR-018 rejects an empty trust store before transport

- Reject browser TLS without a trust anchor
- logger,  browser tls config


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject browser TLS without a trust anchor")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, true, []))
match manager.handshake_address(
    "192.0.2.1", "example.test", 443, 100
):
    case Ok(_): fail("browser connected without a trust anchor")
    case Err(error):
        expect(error.message).to_equal(
            "Pure-Simple browser TLS trust store is empty")
```

</details>

#### should NFR-018 preserve one absolute deadline through TCP and TLS

- Bind the HTTP deadline to deadline-aware TLS record I/O
- "val handshake budget ms = deadline ms - browser monotonic ms
- "tls13 connect host stream with config deadline
- " host stream io deadline
- "io host stream set read timeout
- "io host stream set write timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind the HTTP deadline to deadline-aware TLS record I/O")
val h1 = file_read(
    "src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl")
val browser_tls = file_read(
    "src/lib/gc_async_mut/gpu/browser_engine/net/tls.spl")
val tls_io = file_read("src/os/tls13/_Tls13/context_io.spl")
val tls_connect = file_read("src/os/tls13/_Tls13/psk_connect.spl")

expect(h1).to_contain("self.tls.handshake_address_deadline(")
expect(h1).to_contain("request_deadline_ms")
expect(browser_tls).to_contain(
    "val handshake_budget_ms = deadline_ms - browser_monotonic_ms()")
expect(browser_tls).to_contain(
    "tls13_connect_host_stream_with_config_deadline(")
expect(tls_connect).to_contain(
    "_host_stream_io_deadline(stream, deadline_ms)")
expect(tls_io).to_contain("if _io_deadline_expired(io):")
expect(tls_io).to_contain(
    "io.host_stream.set_read_timeout(Some(remaining_ms))")
expect(tls_io).to_contain(
    "io.host_stream.set_write_timeout(Some(remaining_ms))")
expect(tls_io).to_contain("if io.kind == \"host_stream\":\n                return result")
```

</details>

#### should NFR-018 keep server read and write timeout owners distinct

- Use the configured write timeout on the hybrid accept path
- "client fd, Some
- "client fd, Some
- "time now micros
- "tls13 accept x25519 mlkem768 with deadline
- "if  tls13 server deadline expired
- " recv record
- "tcp backend set read timeout
- "tcp backend set write timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the configured write timeout on the hybrid accept path")
val worker = file_read(
    "src/lib/nogc_async_mut/http_server/worker.spl")
val tls_server = file_read("src/os/tls13/server.spl")
val accept_start = worker.index_of("me handle_tls13_pqc_accept")
val accept_end = worker.index_of("me handle_tls_accept")
val accept_path = worker.slice(accept_start, accept_end)

expect(accept_path).to_contain(
    "client_fd, Some(self.config.read_timeout_ms)")
expect(accept_path).to_contain(
    "client_fd, Some(self.config.write_timeout_ms)")
expect(accept_path).to_contain(
    "time_now_micros() / 1000 + handshake_budget_ms")
expect(accept_path).to_contain(
    "tls13_accept_x25519_mlkem768_with_deadline(")
expect(tls_server).to_contain(
    "if _tls13_server_deadline_expired(deadline_ms):")
expect(tls_server).to_contain(
    "_recv_record(socket_fd, deadline_ms)")
expect(tls_server).to_contain(
    "tcp_backend_set_read_timeout(\n                socket_fd, Some(remaining_ms))")
expect(tls_server).to_contain(
    "tcp_backend_set_write_timeout(\n                socket_fd, Some(remaining_ms))")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 browser TLS fail-closed policy.
- X25519MLKEM768 browser TLS fail-closed policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
