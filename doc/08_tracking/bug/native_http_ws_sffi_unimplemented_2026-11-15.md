# Native bridge_worker: rt_http_server_* / rt_ws_* / rt_http_upload have no runtime implementation

Status: open
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
