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

## Remaining: NATIVE crash — separate, ROOT-CAUSED, fix deferred
With the interpreter fix, the IDENTICAL source serves correctly end-to-end —
proving the Simple logic is sound. The natively-built fixture still SIGSEGVs
(`rsi=nil`, `mov 0x8(%rsi)`), backtrace `Worker.run → handle_completion →
worker_sendfile_open_path_for_pending → StaticCompressionCache.get`.

**Root cause (precise, symbols ARE correct here):** `worker_sendfile_open_path_for_pending`
calls `pending.get(fd)` where `pending: Dict<i64,(text,i64,i64)>`. `Dict<K,V>`
resolves to `TypeId::ANY` (type_resolver.rs:421), so the receiver type is lost and
HIR emits `MethodCall{method:"get", dispatch:Dynamic}`. In MIR
(`lowering_expr_method.rs`) the Dynamic-dispatch fallback (not a trait method)
emits `MethodCallStatic{func_name:"get"}` (bare). Codegen
(`closures_structs.rs::compile_method_call_static`) resolves the bare name `get`
to a user method by name (`func_ids` last-write-wins) → it bound
`pending.get(fd)` to **`StaticCompressionCache.get`**, which reads the Dict as a
cache (`self.entries` at offset 0x10 → nil) → NULL+8 deref. Disasm proof:
`worker_sendfile_open_path_for_pending+12: lea StaticCompressionCache.get; call`.
This is the documented **bare-name method-collision** class — the same one the
`has`/`len` guards in `compile_method_call_static` already work around (their
comments describe identical segfaults); `get` simply lacks a guard.

**Why the fix is deferred (not landed):** the natural fix — a bare-`get` guard
routing to the generic `rt_index_get` — is fragile in ways two attempts proved:
- routing via `try_compile_builtin_method_call` does NOT box the key (it assumes
  MIR pre-boxed args), so populated `dict.get(k)` / `array.get(i)` returned WRONG
  values (key never matched);
- routing via `compile_builtin_method` (which `wrap_value`s the key) panics
  unless `rt_index_get` is pre-registered (`runtime_funcs` is an immutable ref;
  the used-fn pass in `common_backend.rs` only adds it for `MirInst::IndexGet`),
  and after registering it the server served req#1 then crashed on req#2 and a
  populated-dict probe SIGSEGV'd — the key/result tagging differs between the
  array-index and dict-key paths.
A correct fix needs the receiver's collection identity preserved (don't erase
`Dict<K,V>` to `ANY`) OR a runtime-tag-dispatched get that boxes the key exactly
once. That is a deliberately-scoped, high-blast-radius codegen change (every
`.get` call) and was reverted rather than shipped broken.

Also note the AOT build is degraded (fails to compile `h2_hpack.spl` /
`context_propagation.spl` — "cannot infer field type: struct 'ANY'" — and stubs
33 symbols); cleaning those would aid further native debugging.

## Ruled out
- Private-symbol collision (no `warn_duplicate_private_signatures` warning).
- Stale binary (fresh rebuilds reproduce).
- Bare→Option payload loss in `set_static_handler` (no effect; reverted).
- Threading (fixture `worker_count=1` runs inline, no thread spawn).

## Secondary bug (separate)
`static_file.spl:716` `_static_text_to_bytes` calls `s.byte_at(i)` on `text`, but
`byte_at` is not a `text` method (only standalone `byte_at([i64],i64)` in
`cbor/types.spl`). Reached only via `StaticFileHandler.handle` + `Accept-Encoding`.
