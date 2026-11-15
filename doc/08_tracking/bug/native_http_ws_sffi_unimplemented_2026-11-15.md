# Native bridge_worker: rt_http_server_* / rt_ws_* / rt_http_upload have no runtime implementation

Status: open (rt_http_* open; rt_ws_* verification-pending)
Date: 2026-11-15
Area: runtime / SFFI (`src/lib/nogc_sync_mut/io/http_sffi.spl`)

## Symptom
A native build of `src/app/llm_caret/messaging/bridge_worker.spl` with the
seed `seed-vtable.exe` succeeds (`182 compiled, 0 failed`), but the link stubs 12
unresolved symbols, and each stub aborts if it is called:
rt_http_client_set_header rt_http_server_create rt_http_server_destroy
rt_http_server_route rt_http_server_start rt_http_server_static
rt_http_server_stop rt_http_upload rt_ws_close rt_ws_connect rt_ws_receive
rt_ws_send

## Finding
This is not a link-set omission. None of the 12 symbols is defined in
`src/runtime/**` (C, vendor excluded), in `src/compiler_rust/runtime/src/**`, or
in the seed interpreter. The only references are the extern declarations and
call sites in `http_sffi.spl`. The SFFI surface was declared but never
implemented.

## Needed
Implement these symbols, either in the C runtime with a Simple twin or in pure
Simple over the existing socket SFFI. Then add a native `bridge_worker --once`
spec. No such spec exists yet, because any code path that reaches these
symbols aborts.

## Update 2026-11-15 — bridge_worker symptom removed (externs still unbacked)
bridge_worker never called the 12 externs. They were pulled in because
`adapter/chat/http_delivery.spl` imported `app.io.http_ffi`, a facade that
re-exports all of `std.nogc_sync_mut.io.http_sffi`. That import now points at
`std.nogc_sync_mut.io.http_client_core`, which is the actual owner of
`http_request`. Native build with seed-vtable: before `stubbed 12 unresolved
symbol(s)`, after there is no stub line, `Build complete: 180 compiled, 0 cached, 0 failed`.
`bridge_worker --once` runs and prints `{"handled":0,"failed":0,"delivered":0,"delivery_failed":0}`.

The bug stays open because the 12 externs are still declared with no backing.
Follow-up plan, which needs an owner decision because it removes public API:
delete the 12 externs and their wrappers (`http_upload`, `http_client_set_header`,
`http_server_*`, `ws_*`, `HttpServer`, `WebSocket`) from `nogc_sync_mut/io/http_sffi.spl`,
the 5 facades and `io/__init__.spl`. Fix `llm_diagnostics/exporters/ws_exporter.spl`,
which passes a port as a ws handle. Regenerate `unbacked_extern_baseline.txt`
after review. Servers should use the pure-Simple `gc_sync_mut/http_server`;
a WS client would sit on `nogc_sync_mut/http/ws/*`.

## Update 2026-11-15 — rt_ws_* implemented in pure Simple (verification-pending for ws)
The four WebSocket externs are no longer externs. `rt_ws_connect`, `rt_ws_send`,
`rt_ws_receive` and `rt_ws_close` are pure-Simple functions in
`src/lib/nogc_sync_mut/io/ws_client_core.spl`, re-exported from `http_sffi.spl`
with the same signatures. They run over the sync `TcpStream` and reuse
`nogc_sync_mut/http/ws/ws_handshake.spl` (SHA-1 + base64 accept key) for the
RFC 6455 opening handshake. Covered: `ws://` URLs, masked client frames,
7/16/64-bit lengths, text/binary, continuation reassembly, ping -> pong, and
the close handshake. The handle is the TCP descriptor, so no state table is
needed. Not covered: `wss://` (TLS), extensions, subprotocols.
`llm_diagnostics/exporters/ws_exporter.spl` now connects in `ws_set_port` and
sends on the handle it gets back, not on the port number.
Spec: `test/01_unit/lib/nogc_sync_mut/io/ws_client_loopback_spec.spl` runs a
loopback echo server written in Simple on a worker thread.

WebSocket part: Status verification-pending. The 8 `rt_http_*` externs are
owned by a separate lane and remain open here.

Native evidence (seed-vtable, llvm-mingw, Windows): a native build of the same
fixture + client (`native-build`, `35 compiled, 0 failed`) now stubs 8 symbols,
all `rt_http_*`; no `rt_ws_*` stub remains. The binary prints
`case1 sent=true echo_ok=true closed=true`, `case2 ... echo_ok=true closed=true`
(ping answered, 300-byte 16-bit-length frame) and `case3 valid=false`.
Side observation, not a WS defect: in that native binary `thread.join()` on the
fixture worker printed `Option::Some(8)` where the worker returned `1` (looks
like a tagged-int join payload); the interpreter returns `1`. Needs its own bug.
`test --mode=native` with the seed ran the spec on the interpreter (runner says
so), so the native evidence above is from the standalone build.

HTTP reuse (owner directive 2026-11-15: the Upgrade handshake uses the std HTTP code, and only the framing is new):
the client builds the request with `http/ws/ws_handshake.ws_build_client_request`. It parses the 101 reply with
`nogc_sync_mut/http/response.parse_response` plus `http/headers.get_header`, and checks
`ws_compute_accept_key` (std `crypto/sha1` + base64). The spec's echo server parses the upgrade request with
`http/request.parse_request` + `get_header` and replies with `ws_build_server_response`.
For this, `request.spl`/`response.spl` moved from the dead `import x from "std/http/..."`
form to `use std.nogc_sync_mut.http.*`, which had failed with `function from not found`. Also `parse_request`, `parse_response`
and `get_header` are now `pub`. Re-verified: interpreted `3 passed`, native 17 compiled / 25 cached, same output.
## Update 2026-11-15 — 8 non-ws symbols backed in pure Simple (verification-pending)
Status for `rt_http_server_create/_route/_static/_start/_stop/_destroy`,
`rt_http_upload`, `rt_http_client_set_header`: verification-pending.
They are now plain Simple functions in
`src/lib/nogc_sync_mut/io/http_server_core.spl`, a handle table over the std sync server (`nogc_sync_mut/http_server`: `SimpleHttpServer.handle_connection` parser + `Router` dispatch + response writer, new shared `router.static_dir_response`) and `http_client_core.http_request_raw`
re-exported by `http_sffi.spl` (externs removed).
Semantics chosen (the old "handler is a function name" contract cannot be
built natively): a route's `handler` is the literal response body; the reserved
handler `@echo` (`HTTP_SERVER_ECHO_HANDLER`) answers with the raw request head
and body. `start` binds 127.0.0.1:<port> and blocks serving one connection at a
time (owner-thread accept loop) until `stop`/`destroy`. Static mounts serve text files,
refusing unsafe paths (`path_is_safe`). `set_header` records default headers per client handle that
`http_client_request` prepends; `http_client_destroy` forgets them.
Spec: `test/01_unit/lib/nogc_sync_mut/io/http_sffi_server_loopback_spec.spl`
(probe `fixtures/http_sffi_loopback_probe.shs interp|native`).
Still open: `rt_ws_*` (separate lane); `rt_http_client_create/_request` have no
interpreter backing, so the configured-client header path is exercised natively
only (interpreted lane checks the recorded headers on the wire via `http_request`).
Verified 2026-11-15: interpreted spec `Results: 4 total, 4 passed, 0 failed`; native probe (seed-vtable native-build of both fixtures, real configured client) all lines 200 incl. `X-Lane-Probe: probe-42` and the multipart payload.
`unbacked_extern_baseline.txt` still lists the 8 names: the census cannot run on this Windows host (seed exe has no COFF symbol table), so the reviewed regeneration is pending on a Linux host.
