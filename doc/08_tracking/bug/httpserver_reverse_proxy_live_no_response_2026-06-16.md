# Native HttpServer Reverse Proxy Live Path Returns No Response

Status: resolved
Date: 2026-06-16
Lane: gpu_web_db_offload

## Summary

`scripts/check/check-proxy-live-httpserver.shs` builds a native fixture that
starts the real async `HttpServer` with a `LocationConfig(handler_type:
"proxy", proxy_pass: "backend")` and an `UpstreamConfig` pointing at a raw
loopback backend process.

Resolved on 2026-06-16. The live wrapper now proves the production
`HttpServer` worker reverse proxy path against a backend web process:

```text
STATUS: PASS proxy live HttpServer reverse proxy
```

The historical notes below record the failure progression from empty response
and zero backend requests through native parser and response-filter fixes.

## Evidence

Command:

```sh
sh scripts/check/check-proxy-live-httpserver.shs
```

Observed result:

```text
STATUS: FAIL proxy live HttpServer reverse proxy: first response missing backend body: ''
backend_seen=[]
proxy_stdout_tail=''
proxy_stderr_tail=''
```

The native-build also reports existing non-critical compile skips for
`h2_hpack.spl` and `security/auth/context_propagation.spl`, then links the
fixture binary. Those warnings are not the proxied-request failure itself.

## Expected

The script should prove the real `HttpServer` proxy path:

- client receives `HTTP/1.1 200 OK`
- backend body is forwarded
- hop-by-hop response headers are filtered
- backend sees rewritten `Host: 127.0.0.1:18194`
- client hop-by-hop headers do not reach the backend

## Suspected Area

Start with:

- `src/lib/nogc_async_mut/http_server/worker.spl`
- `src/lib/nogc_async_mut/http_server/server.spl`
- `src/lib/nogc_async_mut/http_server/proxy.spl`
- `test/05_perf/web/proxy_live_httpserver_proxy.spl`
- `scripts/check/check-proxy-live-httpserver.shs`

The fixture prints the server listening marker, but the first client request
does not reach the backend. Next debugging should determine whether the native
worker event loop exits, closes the accepted client before parsing, fails route
handoff, or fails upstream connect without serializing an error response.

## 2026-06-16 Follow-up Evidence

Added a native static baseline:

```sh
sh scripts/check/check-httpserver-live-static.shs
```

Current result:

```text
STATUS: FAIL HttpServer live static: bad static response: ''
```

This proves the remaining live failure is below proxy routing. The native
`HttpServer` static path still does not return a response, so the proxy live
fixture cannot be considered meaningful yet.

Fixes applied before hitting the verification cycle cap:

- added Rust runtime exports for `rt_io_tcp_socket_create`,
  `rt_io_tcp_bind_fd`, `rt_io_tcp_listen`, TCP socket options, and
  `rt_event_loop_*` compatibility functions.
- changed the Simple event-loop ABI to `rt_event_loop_poll -> count` plus
  `rt_event_loop_poll_get_fd(index)`.
- fixed native crashes in `IoDriver._ev_register_read` by replacing the
  event-registration dictionary with a small fd array.
- fixed native crashes in `Worker.handle_completion` by replacing hot op-id
  dictionaries with small op metadata arrays.
- replaced worker `.keys()` timeout iteration with fd lists for HTTP/1, HTTP/2,
  proxy, and tunnel connection tracking.

Observed diagnostics:

- before the `IoDriver` fd-array fix, gdb showed
  `IoDriver._ev_register_read -> StaticCompressionCache.get`, which is the
  generated dictionary `.get` target.
- before the worker op-array fix, gdb showed
  `Worker.handle_completion -> StaticCompressionCache.get`.
- after the fd-list reaper change, the live static fixture still returns an
  empty response. A final gdb diagnostic did not reproduce a crash before the
  cycle cap; next work should trace post-accept `submit_recv`, parser
  completion, `send_response`, and native `write`.

## 2026-06-16 Later Follow-up Evidence

Additional reliability fixes moved the live static path farther:

- untracked `IoDriver` completions are now routed as accept completions in
  `Worker.run`; every non-accept op is tracked by the worker op table.
- HTTP/1 connection storage uses fd/item arrays for the hot path instead of
  native `Dict.get`.
- worker timeout reaping and shutdown cleanup use indexed `while` loops instead
  of `for` iteration over fd arrays.
- `IoDriver` readiness and received-byte completion storage use small arrays
  instead of hot-path dictionaries.
- native codegen now registers `rt_bytes_to_text` in `runtime_sffi.rs`; the
  native runtime already provides the implementation.
- `Worker.handle_completion` checks H2 membership with the H2 fd list instead
  of `h2_connections.get(fd)`.

Current syscall evidence:

```text
accept(3, ...) = 5
fcntl(5, F_SETFL, O_RDWR|O_NONBLOCK) = 0
setsockopt(5, SOL_TCP, TCP_NODELAY, [1], 4) = 0
epoll_ctl(4, EPOLL_CTL_ADD, 5, ...) = 0
epoll_wait(4, [{events=EPOLLIN, data={u32=5, u64=5}}], 64, 10) = 1
read(5, "GET /hello.txt HTTP/1.1...", 8192) = 63
```

The remaining failure is after `read(5)` and before any static-file `openat` or
`write(5)`. `scripts/check/check-httpserver-live-static.shs` still reports:

```text
STATUS: FAIL HttpServer live static: bad static response: ''
```

Next work should focus on `Worker.handle_completion -> handle_recv` after the
request bytes are read, especially parser completion and `process_request`.

## 2026-06-16 Native Cleanup Follow-up

Additional fixes applied in this pass:

- replaced worker proxy connection state hot-path lookups with fd/item arrays
  (`proxy_connection_get/set/remove`) so ordinary static connection cleanup does
  not touch native `Dict.get`.
- replaced worker proxy tunnel state hot-path lookups with fd/item arrays
  (`proxy_tunnel_get/set/remove`) for the same defensive cleanup path.
- removed native-unsupported dictionary `.remove` calls from the plain
  `close_connection` static path for sendfile and TLS bookkeeping.

Focused checks still pass:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/io/driver.spl \
  test/05_perf/web/httpserver_live_static_fixture.spl \
  test/05_perf/web/proxy_live_httpserver_proxy.spl
```

Current live result after the third verify/fix cycle:

```text
STATUS: FAIL HttpServer live static: bad static response: ''
```

The latest debugger run no longer showed the previous proxy cleanup segfaults.
It instead emitted repeated native runtime errors:

```text
Simple runtime error: function not found: remove
```

After removing the plain `close_connection` `.remove` calls, the wrapper still
returned an empty response. Per the runaway guard, stop this cycle here. Next
work should trace `handle_recv -> process_request -> send_response`, and should
also eliminate or implement the remaining native `.remove` call sites before
using proxy/tunnel/sendfile live evidence as release-grade proof.

## 2026-06-16 Receive Dispatch Follow-up

Additional fixes applied:

- gated plain HTTP/1 receive/send paths away from `h2_connections.get(fd)` and
  `tls_sessions.get(fd)` unless the fd/config proves H2/TLS is active.
- changed event-loop recv EOF handling in `IoDriver.poll_count`: when epoll
  reports a ready fd and `rt_io_tcp_read` returns zero bytes, complete the recv
  op with result `0` instead of re-queueing the closed fd forever.
- added a conservative worker fallback so an untyped completion for a known
  HTTP/1 fd is treated as `OP_RECV`.
- added a complete-header fast path for non-proxy routes so a parsed static
  request can populate `Connection.request` and enter `process_request` without
  waiting on the normal parser state machine.

Current focused check:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/io/driver.spl \
  test/05_perf/web/httpserver_live_static_fixture.spl \
  test/05_perf/web/proxy_live_httpserver_proxy.spl
```

passes.

Current live result remains:

```text
STATUS: FAIL HttpServer live static: bad static response: ''
```

Sharper syscall evidence after the EOF fix:

```text
accept(3, ...) = 5
read(5, "GET /hello.txt HTTP/1.1\\r\\nHost: 1"..., 8192) = 63
```

There is still no `openat` for `/tmp/simple-live-static/hello.txt` and no
`write(5, ...)`.

Breakpoint evidence:

- `Worker.handle_completion` is reached after the read.
- `Worker.handle_recv`, `Worker.process_request`, `Worker.inline_static_handler`,
  and `Worker.send_response` are not reached.

Next work should inspect generated/native behavior inside
`Worker.handle_completion` after entry. The likely remaining failure is that the
completion enters `handle_completion` but exits before the `OP_RECV` branch,
despite the worker op table having an fd for the operation.

## 2026-06-16 Native Hot-Path Null Dispatch Follow-up

Additional fixes applied:

- native middleware function-pointer dispatch was bypassed in the worker hot
  path. `Worker.run_builtin_request_phases` now calls the built-in body-limit
  check directly; connection limits remain enforced at accept.
- `MiddlewarePipeline.run_phase` dispatches default built-ins by stable name so
  default pipeline entries do not jump through null function pointers.
- `Worker.find_config_location` handles exact and longest-prefix matching
  directly from `ServerConfig.locations`; HTTP/1 static/proxy hot paths no
  longer call `AsyncRouter.route`, which was also hitting a native null jump.
- `inline_static_handler` now derives normal-response size from
  `file_read_text(full_path).len()` instead of calling `file_size(full_path)`,
  because native `nogc_sync_mut.io.file_ops.file_size` jumped through null in
  the live fixture.

Observed backtrace progression:

```text
MiddlewarePipeline.run_all_phases -> null
AsyncRouter.route -> null
nogc_sync_mut.io.file_ops.file_size -> null
```

The first two were patched and execution progressed to the static file handler.
The `file_size` crash was patched after the live retry cap; only focused type
checking was rerun afterward:

```text
bin/simple check src/lib/nogc_async_mut/http_server/middleware.spl \
  src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/io/driver.spl \
  test/05_perf/web/httpserver_live_static_fixture.spl \
  test/05_perf/web/proxy_live_httpserver_proxy.spl
```

Result:

```text
✓ All checks passed (5 file(s))
```

Do not claim the live static gate is fixed until
`scripts/check/check-httpserver-live-static.shs` is run in a fresh cycle and
returns `STATUS: PASS`. If that passes, immediately run
`scripts/check/check-proxy-live-httpserver.shs` to validate the worker-level
reverse proxy on the real `HttpServer`.

## 2026-06-16 Static Handler Progress Follow-up

Additional fixes applied in the conflicted `ruw` working copy:

- restored the worker-local exact/prefix route selector after concurrent jj
  reconciliation had left `process_request` still calling `AsyncRouter.route`.
- restored static response size derivation from `file_read_text(full_path).len()`.
- replaced static-handler `find_header` calls with `Worker.find_request_header`
  to avoid native null dispatch in `range.find_header`.
- skipped `compress_response` on the native worker static hot path after
  `compression._find_header_value` hit a native null jump for a request with no
  `Accept-Encoding`.

Focused check still passes:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/middleware.spl \
  src/lib/nogc_async_mut/io/driver.spl \
  test/05_perf/web/httpserver_live_static_fixture.spl \
  test/05_perf/web/proxy_live_httpserver_proxy.spl
```

Current live result remains:

```text
STATUS: FAIL HttpServer live static: bad static response: ''
```

Backtrace progression in this fresh cycle:

```text
AsyncRouter.route -> null
range.find_header -> null
compression._find_header_value -> null
Connection.should_keepalive -> segfault
```

The request now reaches `inline_static_handler`, `process_request`, and
`send_response`. Next fresh cycle should focus on
`Connection.should_keepalive` / `Connection.set_response`; likely the native
request/header access path inside keepalive detection needs the same direct
header-scan treatment or a native-static close-response fast path.

## 2026-06-16 Response Serialization Follow-up

Additional fixes applied:

- `Connection.should_keepalive` no longer calls the shared `get_header` helper.
- `Connection.set_response` and `set_response_bytes` force close-after-response
  on the native hot path to avoid request header tuple/list scanning.
- `Connection.set_response` and `set_response_bytes` no longer call
  `add_keepalive_headers`, which was another native null-dispatch point.

Focused check passed:

```text
bin/simple check src/lib/nogc_async_mut/http_server/connection.spl \
  src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/middleware.spl \
  src/lib/nogc_async_mut/io/driver.spl \
  test/05_perf/web/httpserver_live_static_fixture.spl \
  test/05_perf/web/proxy_live_httpserver_proxy.spl
```

Current live static result remains:

```text
STATUS: FAIL HttpServer live static: bad static response: ''
```

Backtrace progression in this cycle:

```text
Connection.should_keepalive -> segfault
Connection.request_header_value -> segfault
response.add_keepalive_headers -> null
response.serialize_response -> null
```

The request now reaches response serialization. Next fresh cycle should either
fix `serialize_response` native lowering or add a small native-safe static
response serializer in the worker for the normal buffered `HttpResponseData`
path, then rerun `scripts/check/check-httpserver-live-static.shs`.

## 2026-06-16 Reverse Proxy Live Follow-up

Static live evidence now passes:

```text
STATUS: PASS HttpServer live static
```

Reverse proxy live evidence progressed from no backend request to confirmed
backend receipt. The backend now sees the rewritten request:

```text
GET /api/live HTTP/1.1
Host: 127.0.0.1:18194
Connection: keep-alive
X-Forwarded-For: 127.0.0.1:18193
X-Forwarded-Proto: http
X-Client-Fixture: yes
```

Fixes applied in this cycle:

- `handle_proxy_send_request` now uses the worker's
  `proxy_request_stream_fds`/`proxy_request_stream_get` side table instead of
  reading `AsyncProxyConnection.request_body_streaming`, which native lowering
  could not infer.
- Remaining proxy cleanup `.remove()` calls on reverse lookup dictionaries were
  removed from the currently non-pooled proxy path after the live wrapper hit
  `Simple runtime error: function not found: remove`.
- Async and sync proxy status-line validators no longer call `parse_int()` on
  the extracted status substring; they now validate the fixed-width HTTP status
  code with direct digit/range checks.

Focused checks pass:

```text
bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl \
  src/lib/nogc_sync_mut/http_server/proxy.spl \
  src/lib/nogc_async_mut/http_server/worker.spl
```

The last live failure before the parse-free validator patch was:

```text
STATUS: FAIL proxy live HttpServer reverse proxy:
first response missing backend body:
HTTP/1.1 502 Bad Gateway ... Proxy upstream response status invalid
```

A temporary diagnostic confirmed the upstream status line seen by the native
proxy parser was exactly `HTTP/1.1 200 OK`.

## 2026-06-16 Resolution

Final fixes:

- native-safe `AsyncRouter.route` indexed loops and direct prefix route params.
- worker request-stream side table for native-safe proxy body state.
- empty upstream-pool guard before `async_proxy_pool_acquire`.
- native-safe upstream status validation using slice comparison instead of
  `starts_with` and fixed-width digit checks instead of `parse_int`.
- response filtering now drops hop-by-hop headers without appending
  `Connection: close`.

Final evidence:

```text
SIMPLE_BIN=src/compiler_rust/target/debug/simple sh scripts/check/check-proxy-live-httpserver.shs
STATUS: PASS proxy live HttpServer reverse proxy
```

The wrapper still reports unrelated non-critical native entry-closure skips for
`http/h2/h2_hpack.spl` and `security/auth/context_propagation.spl`; those are
not this live proxy bug.

## 2026-06-16 Current-State Confirmation

Current code keeps request body stream state in worker-local fd/item arrays and
bypasses upstream pool acquisition for the reliability gate. Pooled reuse remains
production follow-up work.

Focused check passed:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  src/lib/nogc_sync_mut/http_server/proxy.spl \
  test/05_perf/web/proxy_live_httpserver_proxy.spl
```

Live evidence passed:

```text
sh scripts/check/check-proxy-live-httpserver.shs
STATUS: PASS proxy live HttpServer reverse proxy
```

## 2026-06-16 Upstream Pool Reuse Evidence

Upstream connection pooling was restored with a native-safe release path:

- reusable upstream fds are released to `proxy_upstream_pool` instead of being
  closed by the generic client cleanup path.
- after releasing a reusable upstream fd, the worker closes only the client fd.
- pool acquisition no longer depends on reverse lookup dictionary cleanup.

Focused check passed:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  test/05_perf/web/proxy_live_httpserver_proxy.spl
```

New live pooling evidence passed:

```text
sh scripts/check/check-proxy-live-httpserver-pool.shs
STATUS: PASS proxy live HttpServer upstream pool reuse
```

The original live reverse proxy gate still passes:

```text
sh scripts/check/check-proxy-live-httpserver.shs
STATUS: PASS proxy live HttpServer reverse proxy
```

## 2026-06-16 Upload Streaming Gate

A new live upload gate was added:

```text
sh scripts/check/check-proxy-live-httpserver-upload.shs
```

The gate builds the same native `HttpServer` reverse-proxy fixture, then sends:

- a split `POST /api/upload-fixed` with `Content-Length: 1048577`, sending
  only headers plus the first five bytes before waiting for upstream header
  arrival.
- a split `POST /api/upload-chunked` with `Transfer-Encoding: chunked`, also
  waiting for upstream header arrival before sending the remaining chunks.

Focused checks still pass:

```text
bin/simple check src/lib/nogc_async_mut/http_server/proxy.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter
```

The helper `async_proxy_request_body_streaming_required` now uses declared
`Content-Length` before falling back to buffered body length, so split fixed
uploads can be classified as streaming-required at header completion.
The worker hot path also now computes streaming admission explicitly from
chunked transfer state or declared `Content-Length` above
`WORKER_PROXY_MAX_BUFFERED_REQUEST_BODY_BYTES`, avoiding compound boolean
ambiguity in this native path.

The native response status parser was moved toward direct wire validation with
`starts_with("HTTP/1.")`, the required space at byte 8, and three status-code
digits because native builds intermittently rejected a visible
`HTTP/1.1 200 OK` line. The worker now also has a native hot-path shortcut for
complete upstream response chunks: when a recv contains complete HTTP/1.x
headers, it filters hop-by-hop headers and queues the client send directly,
leaving incremental responses on the existing state machine. After that change,
the original live `HttpServer` proxy gate passes again:

```text
sh scripts/check/check-proxy-live-httpserver.shs
STATUS: PASS proxy live HttpServer reverse proxy
```

Focused unit coverage also passes:

```text
SIMPLE_LIB=src bin/simple test \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl \
  --mode=interpreter
```

Current upload live result is now narrowed past header admission into the
fixed-body forwarding loop:

```text
STATUS: FAIL proxy live HttpServer upload streaming:
[Errno 104] Connection reset by peer
backend_headers=['POST /api/upload-fixed HTTP/1.1 ... Content-Length: 1048577 ...']
backend_seen=[(..., 40965, 'fixed')]
```

The worker now relies on the accumulated parser state for incomplete large-body
requests, while preserving the complete-header fast path for complete requests.
The live upload gate also now waits for one backend header for the first fixed
upload and two total headers after the chunked upload starts; the old counts
still expected a removed preflight request. The raw header parser was also
adjusted to avoid native optional checks around `index_of(":")`.
The remaining production gap is the fixed request-body relay after upstream
headers and the first body chunks have been forwarded. Next work should
instrument or repair the `OP_PROXY_SEND_REQUEST_BODY` /
`OP_PROXY_RECV_CLIENT_BODY` loop so transient native zero-byte read/write
events do not close an otherwise active upload stream.

### 2026-06-16 Nonblocking Upload Body Retry Evidence

`rt_io_tcp_write_text` returns `-9` for native `WouldBlock`. The upload body
send path no longer treats that as a fatal upstream request-body failure; it
now schedules a short timer-backed retry for pending upstream body data.

The reset failure changed into a stall, which narrows the remaining bug from
fatal error handling to body-read scheduling/backpressure:

```text
STATUS: FAIL proxy live HttpServer upload streaming: timed out
backend_seen=[(..., 40965, 'fixed')]
```

Temporary instrumentation showed successful fixed-body progress of:

```text
sent=5 received=5
sent=8192 received=8197
sent=8192 received=16389
sent=8192 received=24581
sent=8192 received=32773
```

After that point no further body-send completion was observed. The next fix
should focus on why the `OP_PROXY_RECV_CLIENT_BODY` scheduled after that fifth
body send does not continue reading the client's remaining request body.

### 2026-06-16 Timer-Backed Body Poll Follow-Up

The worker now has a scoped `OP_PROXY_POLL_CLIENT_BODY` path for proxied
request bodies. It uses a timer-backed direct client read rather than depending
only on socket readiness from the shared event-loop registry. The request-body
send path also uses the driver's direct `write_text_now` helper for pending
upstream body chunks, with timer-backed retry on zero-byte and native
`WouldBlock` sends.

Focused checks pass:

```text
bin/simple check src/lib/nogc_async_mut/io/driver.spl \
  src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
```

The live upload gate still fails, but the bounded 256 KiB request-body slice
improves the fixed upload evidence from 40,965 bytes to 410,112 bytes forwarded
to the backend:

```text
sh scripts/check/check-proxy-live-httpserver-upload.shs
STATUS: FAIL proxy live HttpServer upload streaming: timed out
backend_seen=[(..., 410112, 'fixed')]
```

Remaining blocker: native live request-body forwarding still stops before the
declared `Content-Length: 1048577` is fully relayed. The next investigation
should instrument the direct `write_text_now` retry path or replace it with a
driver-level writable-fd operation that cannot block the worker and can report
partial write progress separately from `WouldBlock`.

### 2026-06-16 Body Send Retry Dispatch Fix

The worker dispatch path now sends all `OP_PROXY_SEND_REQUEST_BODY` completions
to `handle_proxy_send_request_body`, including negative native results. This
lets native `WouldBlock` (`-9`) reach the timer-backed retry path instead of
being treated as an immediate fatal proxy-body failure by the generic completion
dispatch.

Request-body sends are also submitted through a single bounded helper,
`submit_proxy_request_body_send`, so every pending upstream body chunk uses the
same size cap and completion type. A short byte-send experiment using
`submit_send_bytes` was rejected: the live gate regressed to a connection reset
with zero fixed-body bytes delivered, so the proxy body path remains on text
send while the lower-level body-write stall is investigated.

Current evidence:

```text
bin/simple check src/lib/nogc_async_mut/io/driver.spl \
  src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
STATUS: PASS

sh scripts/check/check-proxy-live-httpserver.shs
STATUS: PASS proxy live HttpServer reverse proxy
```

### 2026-06-16 Initial Body Prefix and Writable Send Tightening

For streaming request bodies, the worker now folds the already-parsed initial
body fragment into the first upstream request write and removes that fragment
from the pending body stream. This prevents tiny prefixes such as the first
five bytes of a split upload from depending on a separate body-send operation.

The async driver writable-send path was also tightened: `_OP_SEND_READY` no
longer writes after a poll timeout with no ready fd. It now writes only when
the target fd is reported ready, with fallback only when no event loop exists.

Current upload evidence:

```text
sh scripts/check/check-proxy-live-httpserver-upload.shs
STATUS: FAIL proxy live HttpServer upload streaming: timed out
backend_headers=[... '\r\n\r\nfixed']
```

This proves the first parsed body fragment reaches the upstream with the
headers. The remaining blocker is forwarding the later client-body chunks after
the initial prefix. Next work should add driver-level write-progress evidence
for `_OP_SEND_READY` or a native write operation that returns readiness/error
details separately from zero-byte progress.

### 2026-06-16 Upload Body Progress Narrowed

The current driver exposes `_OP_SEND_READY` and `submit_send_when_writable` for
future callers, but the native entry-closure build did not include that new
method when the proxy worker called it. The proxy hot path therefore remains on
the existing native-safe `submit_send` path until the native closure issue is
fixed and covered.

Upload tracing found a separate native constant issue:
`WORKER_PROXY_UPSTREAM_BODY_WRITE_BYTES` was originally defined as an alias of
`WORKER_PROXY_REQUEST_BODY_CHUNK_BYTES`. In the native fixture this compiled as
zero, so every later request-body chunk was sliced to `0..0`. The cap is now a
direct `256 * 1024` expression. The worker also schedules later client-body
reads through `submit_recv(..., OP_PROXY_RECV_CLIENT_BODY)` instead of a 1 ms
timer poll.

Focused compile evidence remains green:

```text
bin/simple check src/lib/nogc_async_mut/io/driver.spl \
  src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
STATUS: PASS
```

Latest live-only upload evidence after the direct cap fix, `OP_PROXY_RECV_CLIENT_BODY`
read scheduling, and retrying all negative pending body writes still times out
at 410112 upstream body bytes. Temporary branch tracing showed that the fifth
body chunk is received, written upstream, and schedules the next client-body
receive; after that no further body read completes before the 30s timeout. The
upload wrapper now supports `SIMPLE_PROXY_UPLOAD_SKIP_BUILD=1` to separate
native build from live socket evidence and `SIMPLE_PROXY_UPLOAD_STRACE=/tmp/file`
to trace only the proxy fixture when diagnosing this native stall.

The driver now deregisters write interest after `_OP_SEND` and `_OP_SEND_BYTES`
complete, so stale writable upstream fds do not remain permanently registered.
A broader recv fallback that tried `rt_io_tcp_read` even when epoll did not
report the fd was rejected: focused checks passed, but live upload still timed
out at 410112 bytes and the fallback carried blocking risk for any caller that
does not have a nonblocking socket.

A stale recv-inflight recovery was added after successful upstream body-send
completion: before scheduling the next client-body receive, the worker clears
`proxy_request_body_recv_inflight`. Focused checks pass, but the native
skip-build upload gate still times out at 410112 bytes. A harness experiment
that split the large client body tail into repeated 32 KiB `sendall` calls was
rejected because it regressed to a client-side connection reset before the
backend completed a fixed body.

### 2026-06-16 Request-Body Backpressure Follow-up

The worker now avoids scheduling another client-body receive immediately after
submitting an upstream request-body send. Pending body chunks advance from
`handle_proxy_send_request_body` after the prior write completes. The body-send
helper also schedules a bounded retry if submission is skipped because a tracked
body send is still in flight.

Focused evidence remains green:

```text
bin/simple check src/lib/nogc_async_mut/io/driver.spl \
  src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
✓ All checks passed (4 file(s))
```

The rebuilt native upload fixture still fails:

```text
STATUS: FAIL proxy live HttpServer upload streaming: timed out
backend_seen=[(..., 410112, 'fixed')]
```

Strace still shows one body read that is not matched by an upstream write:

```text
fd 5 reads: 146, 32763, 94336, 94336, 94336, 94336, 94336
fd 6 writes: 211, 32763, 94336, 94336, 94336, 94336
```

Per the runaway guard, stop this verify/fix cycle here. Next work should trace
worker op ownership for the final `OP_PROXY_RECV_CLIENT_BODY` completion and
prove whether it falls back into ordinary `OP_RECV` or whether
`AsyncProxyRequestBodyStream.pending_upstream_data` is overwritten before the
matching send is submitted.

### 2026-06-16 Untracked Completion Recovery Rejected

A guarded worker fallback was tested for untracked native completions after
strace showed `write(...)=94336` being treated as fd `94336`. The fallback first
ignored unknown completions, then tried to recover request/body send progress
from the active proxy state. Both variants were rejected:

- ignoring unknown completions prevented the fixed upload from reaching the
  upstream header path.
- request/body recovery reached the upstream, but regressed fixed upload body
  forwarding from `410112` bytes to only the initial `5` bytes before reset.

The source was reverted to the prior baseline after the rejected experiment.
Focused `bin/simple check` remains green. Next work should fix the underlying
worker op tracking loss directly instead of inferring completion kind from
result byte counts in the run loop.

### 2026-06-16 Completion FD Recovery Rejected

A lower-level `IoDriver` experiment added completed I/O fd metadata and let the
worker recover an untracked proxy request-body recv by checking whether the
completion fd was an active proxy request stream. One rebuilt native run moved
the fixed upload through the full `1048577` bytes and exposed the next chunked
upload failure, but the same source was not stable across rebuilds: later live
runs regressed fixed upload back to only the initial `5` body bytes before a
client reset. The completion-fd surface and worker recovery hook were removed.

A second experiment rewrote the proxy comma-token parser to avoid end-of-string
short-circuit assumptions while investigating the chunked upload rejection. That
also regressed fixed upload to `5` bytes and was reverted.

Current accepted source remains on the previous 410112-byte baseline with
focused checks passing. The durable fix still needs to happen at the worker
op-tracking/driver completion contract, with a focused unit or native fixture
that proves a completed body recv cannot lose its worker op id before the live
upload gate is rerun.

### 2026-06-16 Explicit Driver Op IDs and Cleanup Fixes

The minimal unknown-completion guard was retested and removed. It prevented the
split fixed upload from reaching upstream headers, so it was a regression rather
than a production fix.

The next native trace showed the proxy accepted the client fd but did not
register/read it before the harness timeout. The likely cause was native return
lowering around multi-statement `IoDriver.submit_* -> i64` methods that relied
on a trailing `_push_op(...)` expression. Those methods now explicitly
`return` the allocated op id, so worker `accept_op_id`, recv, send, timeout, and
proxy body op tracking use the real driver op ids.

The upload harness was also hardened:

- the shell now `exec`s Python so timeout/SIGTERM reaches the harness directly.
- Python starts the proxy in a new process group and kills both the process
  group and direct process on cleanup.
- optional upload strace now records `accept`, `accept4`, `connect`, `recv*`,
  and `send*` in addition to read/write/epoll.

Focused checks pass:

```text
bin/simple check src/lib/nogc_async_mut/io/driver.spl \
  src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
STATUS: PASS
```

The native upload fixture rebuilt successfully with only the pre-existing
non-critical `h2_hpack.spl` and `context_propagation.spl` entry-closure skips.

The traced upload evidence progressed back to the meaningful body-relay blocker
and exposed a native cleanup crash:

```text
STATUS: FAIL proxy live HttpServer upload streaming:
[Errno 104] Connection reset by peer
backend_headers=[... Content-Length: 1048577 ... '\r\n\r\nfixed']
backend_seen=[(..., 410112, 'fixed')]
proxy_stderr_tail='Simple runtime error: function not found: remove\n'
```

The native `Dict.remove(...)` crash came from proxy cleanup. The normal proxy
cleanup path now rebuilds `proxy_client_by_upstream` with a native-safe helper,
and the driver byte-send pending map clears completed entries without
`Dict.remove`.

After rebuilding with the native-safe remove fix, the upload gate no longer
emits the `remove` runtime error. It still fails at the same fixed-body relay
point:

```text
STATUS: FAIL proxy live HttpServer upload streaming:
[Errno 104] Connection reset by peer
backend_seen=[(..., 410112, 'fixed')]
proxy_stderr_tail=''
```

Do not mark upload streaming production-ready from this evidence. Next work
should continue at the remaining fixed-body relay reset after `410112` bytes,
most likely in `OP_PROXY_SEND_REQUEST_BODY` / `OP_PROXY_RECV_CLIENT_BODY`
backpressure and completion ordering.

### 2026-06-16 Fixed Upload Response Relay Restored; Chunked Upload Remains

The next continuation moved the live gate past the fixed upload blocker. The
worker now routes accept completions only through tracked `OP_ACCEPT`, so native
response byte counts are no longer interpreted as accepted client fds. Upstream
response reads are handled by the tracked `OP_PROXY_RECV_RESPONSE` owner fd
rather than an eager fd-priority fallback, because that fallback could intercept
upstream body-send completions before the request stream bookkeeping ran.

Current focused check remains green:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl
STATUS: PASS
```

The full live wrapper now proves the fixed `Content-Length: 1048577` request
body reaches the backend and the fixed-upload backend response is relayed to the
client. The remaining failure has moved to the chunked request body case:

```text
STATUS: FAIL proxy live HttpServer upload streaming:
chunked upload did not reach upstream at header completion
early_response='HTTP/1.1 413 Payload Too Large ... Proxy request body streaming failed'
backend_seen=[(..., 1048577, 'fixed')]
```

Do not mark upload streaming production-ready yet. Next work should focus on
`async_proxy_request_stream_receive_chunked_framed` and the
`OP_PROXY_RECV_CLIENT_BODY` / `OP_PROXY_SEND_REQUEST_BODY` sequencing for
`Transfer-Encoding: chunked`, specifically why the worker classifies the first
chunked body stage as invalid before forwarding the upstream header.

### 2026-06-16 Upload Streaming Gate Passes

The chunked upload blocker was fixed by changing the worker-facing chunked
request-body mode to raw pass-through. The proxy now preserves
`Transfer-Encoding: chunked` framing for the backend and streams bytes as they
arrive instead of trying to dechunk and validate the request body on the proxy
hot path. The reusable framed parser remains covered for policy tests, while
the live worker path uses
`async_proxy_request_stream_receive_chunked_passthrough` with bounded pending
bytes and terminal-chunk detection.

Focused evidence:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl \
  src/lib/nogc_async_mut/http_server/proxy.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
STATUS: PASS

bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter
STATUS: PASS, 88 tests

SIMPLE_PROXY_UPLOAD_SKIP_BUILD=1 sh scripts/check/check-proxy-live-httpserver-upload.shs
STATUS: PASS proxy live HttpServer upload streaming
```

The live wrapper assertion was also corrected to compare rewritten `Host`
against the run's dynamic backend address instead of the old fixed
`127.0.0.1:18194` fixture port. The earlier fixed-body reset, upstream response
drop, and chunked `413` admission failure are closed for this native upload
fixture. Broader production proxy work remains open outside this bug: pool
stress, timeout/backpressure scenarios, and performance reporting.

### 2026-06-16 Pool Reuse Gate Restored After Fast Response Fix

The upload fix exposed a separate live pool regression:

```text
STATUS: FAIL proxy live HttpServer upstream pool reuse:
upstream pool did not reuse backend fd: accepts=2, requests=2
```

Both requests succeeded, but the first framed upstream response did not release
the backend fd for reuse. The worker fast response path now sets
`upstream_reusable` for HTTP/1.1 responses unless the upstream explicitly sends
`Connection: close`, matching the reusable policy already used by the slower
`async_proxy_prepare_client_chunk` path. The pool evidence wrapper also drains
the client response until close before starting the second request, so the test
does not race the send-completion release callback.

Evidence:

```text
bin/simple check src/lib/nogc_async_mut/http_server/worker.spl \
  test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl
STATUS: PASS

bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_reverse_proxy_spec.spl --mode=interpreter
STATUS: PASS, 88 tests

sh scripts/check/check-proxy-live-httpserver-pool.shs
STATUS: PASS proxy live HttpServer upstream pool reuse
```
