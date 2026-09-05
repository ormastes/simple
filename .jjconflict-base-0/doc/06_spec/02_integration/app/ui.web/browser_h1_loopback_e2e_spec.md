# Browser network module over a REAL loopback socket

> A separate OS process runs `test/fixture/net/simple_http_server.spl`, a web

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser network module over a REAL loopback socket

A separate OS process runs `test/fixture/net/simple_http_server.spl`, a web

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NET-BROWSER-H1-LOOPBACK |
| Category | Integration |
| Status | Implemented |
| Source | `test/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## What is actually exercised

A separate OS process runs `test/fixture/net/simple_http_server.spl`, a web
server written in Simple, spawned by this spec on an ephemeral loopback port.
It binds a real socket:

    TcpListener.bind (tcp.spl:43)
      -> rt_io_tcp_bind (extern, tcp.spl:491)
      -> runtime/src/value/net_tcp.rs:390 native_tcp_bind
      -> std::net::TcpListener::bind

Clients then reach it two ways, both over that socket:

* `socket_http_get` — a real Simple client socket (`TcpStream.connect` ->
  `rt_io_tcp_connect`) doing a full HTTP/1.1 GET.
* `browser_h1_get` — the browser engine's real HTTP/1.1 client,
  `std.gc_async_mut.gpu.browser_engine.net.h1_client.H1Client`, whose
  plain-HTTP path calls `rt_io_tcp_connect_timeout` (h1_client.spl:344),
  `rt_io_tcp_write_text` (:377) and `rt_io_tcp_read` (:501) directly. No entry
  is registered in `MockResponseRegistry`, so `h1_mock_response_until` returns
  nil and the socket is the only path a response could come from.

## Evidence that this is not an in-process shim

The same server was driven by a **non-Simple** client — bash's `/dev/tcp` — so
no Simple code ran on the client side at all:

    ss -ltnp
      LISTEN 0 128 127.0.0.1:42145 0.0.0.0:*  users:(("simple",pid=3105948,fd=4))

    $ exec 3<>/dev/tcp/127.0.0.1/42145
    $ printf 'GET /external HTTP/1.1\r\nHost: ...\r\nConnection: close\r\n\r\n' >&3
    $ cat <&3
      HTTP/1.1 200 OK
      Content-Type: text/plain
      X-Simple-Server: loopback
      Content-Length: 28
      Connection: close

      PONG-FROM-SIMPLE-SERVER-4242

    server side: SERVER_PEER 127.0.0.1:42294
                 SERVER_GOT_REQUEST_LINE GET /external HTTP/1.1
                 SERVER_GOT_HEADER User-Agent: bash-dev-tcp

`ss` also showed the matched ESTAB pair from both directions:
`bash 127.0.0.1:47868 -> 127.0.0.1:42087` and
`simple 127.0.0.1:42087 -> 127.0.0.1:47868`, with the server logging
`SERVER_PEER 127.0.0.1:47868`.

## Negative controls

The last two examples assert that a client **fails** when no peer is listening.
A network spec that passes whether or not the peer exists measures nothing, so
those examples are load-bearing, not decoration.

## Formerly known gap, now fixed (T-07, x25519mlkem768 campaign, 2026-08-05)

`H1Client` used to be unable to complete a request on either engine the repo
runs: `Url.request_target()` -> `_request_target_component()` calls
`i64.to_char()` (`net/entity/url_types.spl:44-48`), and that method was
matched only by the LLVM native-codegen backend
(`codegen/llvm/{emitter,functions,functions/calls}.rs`) — the tree-walk
interpreter's builtin int-method dispatch
(`compiler/src/interpreter_method/primitives.rs`, shared by `bin/simple test`
and by the Cranelift JIT's unresolved-method runtime fallback used by
`bin/simple run`) matched only `"chr"`, not `"to_char"`, so both raised
`semantic: method 'to_char' not found on type 'i64' (receiver value: 47)`,
where 47 is `/`. Fixed by adding `"to_char"` as an alias for `"chr"` in that
one `match` arm — see
`doc/08_tracking/bug/i64_to_char_missing_outside_llvm_backend_2026-08-05.md`.
The pre-existing
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl`
went from `11 total, 6 passed, 5 failed` to `11 total, 11 passed, 0 failed`.

The `browser H1 module` describe block below now includes a full
status/body/header round trip through `browser_h1_get`, matching the
`socket_http_get` examples.

## Scope

The wire here is plaintext HTTP/1.1. TLS on this stack is real and
rustls-backed (`rt_tls_client_connect`) but needs certificates, so it is out of
scope for this spec.

## Scenarios

### Simple web server serves real HTTP/1.1 over a loopback socket

#### returns 200 and the server's body to a real client socket

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns 200 and the server's body to a real client socket


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns 200 and the server's body to a real client socket")
"""A client reaches a real server and gets its bytes back."""
var server = start_loopback_server("sock_ok", 1)
assert_true(server.started)
assert_true(server.port > 0)
assert_contains(server.addr, "127.0.0.1:")

val probe = socket_http_get(server.addr, "/round-trip")
server.stop()

assert_equal(probe.error, "")
assert_true(probe.ok)
assert_equal(probe.status, 200)
assert_contains(probe.body, LOOPBACK_SERVER_BODY)
```

</details>

#### returns the response headers the server wrote on the wire

- returns the response headers the server wrote on the wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns the response headers the server wrote on the wire")
"""Headers written by the server arrive at the client."""
var server = start_loopback_server("sock_hdr", 1)
assert_true(server.started)

val probe = socket_http_get(server.addr, "/headers")
server.stop()

assert_true(probe.ok)
assert_contains(probe.headers.to_lower(), "x-simple-server")
assert_contains(probe.headers.to_lower(), "content-length")
```

</details>

#### records at the server the exact request line the client sent

- records at the server the exact request line the client sent


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records at the server the exact request line the client sent")
"""The server's own log proves the client's bytes reached the peer."""
var server = start_loopback_server("sock_req", 1)
assert_true(server.started)

val probe = socket_http_get(server.addr, "/observed-path")
val server_log = server.server_log()
server.stop()

assert_true(probe.ok)
# Written only after the server's read_line() returned real bytes.
assert_contains(server_log, "SERVER_GOT_REQUEST_LINE GET /observed-path")
assert_contains(server_log, "SERVER_GOT_HEADER User-Agent: simple-tcp-client")
assert_contains(server_log, "SERVER_SERVED 0")
```

</details>

#### agrees with the server on the ephemeral port the kernel assigned

- agrees with the server on the ephemeral port the kernel assigned


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("agrees with the server on the ephemeral port the kernel assigned")
"""Client local address equals the peer address the server saw."""
var server = start_loopback_server("sock_peer", 1)
assert_true(server.started)

val probe = socket_http_get(server.addr, "/peer")
val server_log = server.server_log()
server.stop()

assert_true(probe.ok)
assert_true(probe.local_addr.len() > 0)
# Only the kernel could have made these two agree.
assert_contains(server_log, "SERVER_PEER {probe.local_addr}")
assert_contains(server_log, "SERVER_CONN_LOCAL {server.addr}")
```

</details>

#### serves two sequential requests on one listening socket

- serves two sequential requests on one listening socket


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serves two sequential requests on one listening socket")
"""A second navigation reuses the same listener."""
var server = start_loopback_server("sock_two", 2)
assert_true(server.started)

val first = socket_http_get(server.addr, "/one")
val second = socket_http_get(server.addr, "/two")
val server_log = server.server_log()
server.stop()

assert_true(first.ok)
assert_true(second.ok)
assert_equal(first.status, 200)
assert_equal(second.status, 200)
assert_contains(server_log, "SERVER_GOT_REQUEST_LINE GET /one")
assert_contains(server_log, "SERVER_GOT_REQUEST_LINE GET /two")
assert_contains(server_log, "SERVER_SERVED 1")
```

</details>

### browser H1 module opens a real TCP connection to the server

#### reaches the Simple server, which observes the browser's connection

- reaches the Simple server, which observes the browser's connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reaches the Simple server, which observes the browser's connection")
"""The browser's own network stack opens a socket the server accepts.

This drives H1Client.get_connection -> rt_io_tcp_connect_timeout. The
proof is on the SERVER side: it logs a peer address and the accepted
connection's local address only after accept() returned a real fd.
"""
var server = start_loopback_server("h1_conn", 1)
assert_true(server.started)

val probe = browser_h1_connect("127.0.0.1", server.port, 15000)
# connect() can return before the server has returned from accept().
val saw_peer = server.wait_for_log("SERVER_PEER 127.0.0.1:", 10000)
val server_log = server.server_log()
server.stop()

assert_equal(probe.error, "")
assert_true(probe.ok)
assert_true(probe.fd >= 0)
assert_true(saw_peer)
# The browser engine's client, not this spec, opened this connection.
assert_contains(server_log, "SERVER_PEER 127.0.0.1:")
assert_contains(server_log, "SERVER_CONN_LOCAL {server.addr}")
```

</details>

<details>
<summary>Advanced: resolves a literal loopback address through the browser DNS resolver</summary>

#### resolves a literal loopback address through the browser DNS resolver

- resolves a literal loopback address through the browser DNS resolver


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves a literal loopback address through the browser DNS resolver")
"""DnsResolver hands H1Client an address it can actually connect to."""
var server = start_loopback_server("h1_dns", 1)
assert_true(server.started)

val probe = browser_h1_connect("127.0.0.1", server.port, 15000)
val saw_peer = server.wait_for_log("SERVER_PEER 127.0.0.1:", 10000)
val server_log = server.server_log()
server.stop()

# A failed resolve would mean no connection at all reached the server.
assert_true(probe.ok)
assert_true(saw_peer)
assert_contains(server_log, "SERVER_PEER 127.0.0.1:")
```

</details>


</details>

#### fails to connect through the browser client when no peer is listening

- fails to connect through the browser client when no peer is listening


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails to connect through the browser client when no peer is listening")
"""NEGATIVE CONTROL for the browser socket path specifically."""
val probe = browser_h1_connect("127.0.0.1", 1, 4000)
assert_false(probe.ok)
assert_true(probe.error.len() > 0)
```

</details>

#### completes a full request through the browser's own H1Client

- completes a full request through the browser's own H1Client


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("completes a full request through the browser's own H1Client")
"""The browser engine's real HTTP/1.1 client does a full round trip.

`browser_h1_get` drives `H1Client.request`, which serializes the
request line via `Url.request_target()` -> `i64.to_char()` (now fixed,
see the spec header), writes it over a real socket
(`rt_io_tcp_write_text`), and parses the response read back
(`rt_io_tcp_read`). This matches the `socket_http_get` examples above,
but through the browser's own client instead of a bare test socket.
"""
var server = start_loopback_server("h1_full", 1)
assert_true(server.started)

val probe = browser_h1_get(server.addr, "/round-trip", 15000)
val server_log = server.server_log()
server.stop()

assert_equal(probe.error, "")
assert_true(probe.ok)
assert_equal(probe.status, 200)
assert_contains(probe.body, LOOPBACK_SERVER_BODY)
assert_contains(server_log, "SERVER_GOT_REQUEST_LINE GET /round-trip")
```

</details>

### negative controls (no peer on the socket)

#### fails when nothing is listening on a previously bound port

- fails when nothing is listening on a previously bound port


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails when nothing is listening on a previously bound port")
"""NEGATIVE CONTROL. Without this the spec could pass with no server."""
# Take a real ephemeral port, then stop the server so the port is dead.
var server = start_loopback_server("neg_dead", 1)
assert_true(server.started)
val dead_addr = server.addr
server.stop()

val probe = socket_http_get(dead_addr, "/dead")
assert_false(probe.ok)
assert_equal(probe.status, -1)
assert_true(probe.error.len() > 0)
```

</details>

#### fails when pointed at a port no server ever bound

- fails when pointed at a port no server ever bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails when pointed at a port no server ever bound")
"""NEGATIVE CONTROL. A wrong port must not produce a 200."""
val probe = socket_http_get("127.0.0.1:1", "/never-bound")
assert_false(probe.ok)
assert_equal(probe.status, -1)
assert_true(probe.error.len() > 0)
```

</details>

#### fails the browser H1 client too when no peer is listening

- fails the browser H1 client too when no peer is listening


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails the browser H1 client too when no peer is listening")
"""NEGATIVE CONTROL for the browser path specifically."""
val probe = browser_h1_get("127.0.0.1:1", "/never-bound", 4000)
assert_false(probe.ok)
assert_equal(probe.status, -1)
assert_true(probe.error.len() > 0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `becc0599c22ab5a6342a025c7a1d0b3cc5a835cecf3a8c6310f83f4e7ed1ef96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `becc0599c22ab5a6342a025c7a1d0b3cc5a835cecf3a8c6310f83f4e7ed1ef96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `becc0599c22ab5a6342a025c7a1d0b3cc5a835cecf3a8c6310f83f4e7ed1ef96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.spl
mirror: doc/06_spec/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 200 and the server's body to a real client socket' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the response headers the server wrote on the wire' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records at the server the exact request line the client sent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
