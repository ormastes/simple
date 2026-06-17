# Bug: pure-Simple async HTTP server crashes on the first event-loop poll

- **ID:** httpserver_static_serve_zeroed_cache_segfault_2026-06-17
- **Severity:** P1 (the `nogc_async_mut` HTTP server could not serve a single request)
- **Area:** compiler interpreter extern (`rt_event_loop_*`) + lib/nogc_async_mut io/driver
- **Status:** INTERPRETER crash **FIXED + verified**. NATIVE crash is a **separate
  native-codegen bug, still open** (see below).

## Live evidence
Recurring kernel segfaults Jun 16→17 in the natively-built perf fixtures
(`httpserver_live_static_fixture`, `proxy_live_httpserver_proxy`,
`simple_static_server`): `segfault at 8 ip 0x46fb4f` etc. The owning checks
(`check-httpserver-live-static.shs`, `check-proxy-live-httpserver*.shs`) report
`STATUS: PASS` while the binary segfaults — worker crashes don't fail the harness.

## Root cause (interpreter) — FIXED
The server dies on the **first event-loop poll, before any request is accepted**.
Located by print-bisecting the live worker flow: the crash is in
`IoDriver.poll_count` (`src/lib/nogc_async_mut/io/driver.spl`) at the event-loop
poll, NOT in the static/cache path (the gdb symbol `StaticCompressionCache.get`
is an unreliable-AOT-symbol misattribution; the hot path is
`inline_static_handler`, which never touches the cache).

`rt_event_loop_poll` has a **count + indexed-get contract** (matching the native
runtime `runtime_native.c`):
- `rt_event_loop_poll(loop, max, timeout) -> i64` returns the COUNT of ready fds
  and stashes them; `rt_event_loop_poll_get_fd(index) -> i64` returns each fd.
The driver uses exactly this: `raw_count = rt_event_loop_poll(...)`, then
`while ri < raw_count: rt_event_loop_poll_get_fd(ri)`.

But the **interpreter impl violated the contract**:
`rt_event_loop_poll_interp` returned `Value::array(platform::poll(...))` (the fd
array) instead of the count, and there was **no `rt_event_loop_poll_get_fd_interp`
registered at all**. So `while ri < raw_count` compared an int to an array →
`error: semantic: type mismatch: cannot convert array to int`, killing the server
on poll #1. (Confirmed: `accept_res` was a proper `-1`; the crash was the next
poll branch, not the accept compare.)

### Fix (landed in source + bootstrap seed)
- `src/compiler_rust/compiler/src/interpreter_event_loop.rs`:
  `rt_event_loop_poll_interp` now stashes the ready-fd `Vec<Value>` in a
  thread-local and returns `Value::Int(count)`; added
  `rt_event_loop_poll_get_fd_interp(index) -> Value::Int(fd)` (mirrors the native
  `poll_results[]` contract).
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`: registered
  `rt_event_loop_poll_get_fd`.
- `src/lib/nogc_async_mut/io/driver.spl`: `cancel`, `close`, `poll_recv_bytes`
  changed `fn(self)` → `me` (they mutate self; the compiler rejected them for JIT
  with "use `me` instead of `fn`", forcing a degraded fallback).

### Verification
Rebuilt the seed (`cargo build --profile bootstrap -p simple-driver`) and ran the
fixture under the interpreter + a real client:
```
listening: 1
RESPONSE_HEAD: HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 10\r\n...
HAS_BODY: True        # served the "static-ok" file body
RESULT: SERVER ALIVE  # no crash, no "cannot convert array to int"
```
(Deployment to `bin/release/<triple>/simple` is a separate `--deploy` step.)

## Remaining: NATIVE crash — separate, still open
With the interpreter fix, the IDENTICAL source serves correctly end-to-end —
proving the Simple logic is sound. The natively-built fixture still SIGSEGVs
(`rsi=nil`, `mov 0x8(%rsi)`), backtrace `Worker.run → handle_completion →
worker_sendfile_open_path_for_pending → <nil .get>` (the OP_SEND-completion /
`sendfile_pending.get(fd)` path; the `StaticCompressionCache.get` symbol is again
a misattribution of `Dict.get`). The native C `rt_event_loop_poll` returns a
correct count, so this is a **distinct native-codegen bug** (a nil-receiver `.get`
in the send-completion path), not the event-loop contract bug. The AOT symbol
table is unreliable for this build (it also fails to compile 2 files —
`h2_hpack.spl`, `context_propagation.spl`: "cannot infer field type: struct 'ANY'"
— and stubs 33 symbols), which should be cleaned up to debug it reliably.

## Ruled out
- Private-symbol collision (no `warn_duplicate_private_signatures` warning).
- Stale binary (fresh rebuilds reproduce).
- Bare→Option payload loss in `set_static_handler` (no effect; reverted).
- Threading (fixture `worker_count=1` runs inline, no thread spawn).

## Secondary bug (separate)
`static_file.spl:716` `_static_text_to_bytes` calls `s.byte_at(i)` on `text`, but
`byte_at` is not a `text` method (only standalone `byte_at([i64],i64)` in
`cbor/types.spl`). Reached only via `StaticFileHandler.handle` + `Accept-Encoding`.
