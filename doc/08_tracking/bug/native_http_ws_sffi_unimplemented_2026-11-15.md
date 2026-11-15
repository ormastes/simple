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
