# Interpreter extern dispatch gap: rt_serial_*, tcp_listener_*/tcp_stream_*, rt_io_file_*

**ID:** interpreter_serial_net_sffi_dispatch_gap
**Severity:** P2
**Status:** Open
**Found:** 2026-06-13 (KV260 telnet-over-serial system test bring-up)

## Symptom

`bin/simple run` (and `simple_seed run`) fail with
`error: semantic: unknown extern function: <name>` for whole SFFI families
that exist in the native runtime but were never wired into the interpreter
extern dispatch table
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`):

- `rt_serial_open/close/read/write/set_timeout/flush/relay`
  (impl: `src/compiler_rust/runtime/src/value/serial.rs`, listed in
  `runtime_symbols.rs` and JIT `runtime_symbol_entries.rs`)
- `tcp_listener_bind/accept/...`, `tcp_stream_connect/read/write/...`,
  `bytes_to_string` (declared in `src/lib/nogc_sync_mut/net/sffi.spl`)
- `rt_io_file_open` (used by `FileHandle` in
  `src/lib/nogc_sync_mut/io/file.spl`; `rt_file_open` is a stub returning -1)
- `native_tcp_listener_close` (listener handles must be released with
  `native_tcp_close` instead)

## Impact

- `src/lib/nogc_sync_mut/io/serial_proxy.spl`, `io/ssh_serial.spl`, and
  `net/telnet.spl` (client) cannot run in interpreter mode at all.
- Any spec or script importing these modules false-fails with a semantic
  error before reaching test logic.
- JIT does not rescue scripts that also touch extern types: HIR lowering
  fails on opaque extern types (`Unknown type: TcpListener`) and falls back
  to the interpreter, which then hits the dispatch gap. Worse, a failed JIT
  attempt can partially execute `main` before falling back, doubling side
  effects (observed: double TCP bind + double file append). Pin
  `SIMPLE_EXECUTION_MODE=interpreter` for daemon-style scripts until fixed.

## Working interpreter-mode alternatives (verified 2026-06-13)

- TCP: `native_tcp_bind` (returns `(handle, err)` tuple),
  `native_tcp_connect` (`(handle, local_addr, err)`), `native_tcp_accept`
  (`Result<[handle, peer]>`), `native_tcp_read` (`Result<[len, [bytes]]>`,
  `Err` on timeout, `Ok len=0` on EOF), `native_tcp_write`,
  `native_tcp_set_read_timeout`, `native_tcp_close`.
- Files: `rt_file_read_bytes` (`[i64]?`), `rt_file_append_text`,
  `rt_bytes_to_text`, `rt_sleep_ms`.
- `std.nogc_sync_mut.io.telnet_serial_bridge` is built on exactly this set.

## Proposed fix

Wire the missing families into `interpreter_extern` (delegating to the same
implementations the native runtime uses), or invert the lib wrappers
(`net/sffi.spl`, `io/serial_sffi.spl`) to call the `native_*`/dispatched
names so both modes share one path (pattern: invert rather than
dual-maintain). Requires seed rebuild + bootstrap redeploy per
`.claude/memory` extern-rebuild rule.
