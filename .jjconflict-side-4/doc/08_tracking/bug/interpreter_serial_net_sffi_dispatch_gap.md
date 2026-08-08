# Interpreter extern dispatch gap: rt_serial_*, tcp_listener_*/tcp_stream_*, rt_io_file_*

**ID:** interpreter_serial_net_sffi_dispatch_gap
**Severity:** P2
**Status:** Partially source fixed 2026-07-15; serial and `bytes_to_string`
execution proof pending, TCP/file ABI-owner lanes remain open
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

## Resolution status

The interpreter now delegates all seven `rt_serial_*` calls to the existing
runtime owner through the shared value bridge, with typed argument checks and
invalid-handle regressions. `bytes_to_string` is registered as an alias of the
existing `rt_bytes_to_text` converter. Focused execution remains pending a
runnable compiler test artifact.

The legacy `tcp_listener_*`/`tcp_stream_*` declarations cannot safely alias the
current `native_tcp_*` family because their handle and result ABIs differ. The
`rt_io_file_*` handle family likewise has no shared production implementation;
`rt_file_open` remains a stub. These require real shared owners and behavioral
tests, not interpreter-only dispatch entries. The obsolete
`native_tcp_listener_close` warning survives only in legacy mirrored source.

## Remaining fix direction

Invert the live library TCP wrappers onto a single canonical `native_tcp_*` or
`rt_io_tcp_*` ABI with explicit handle/result conversion. Implement one shared
file-handle registry for the complete `rt_io_file_*` family. Both lanes need
loopback/tempfile lifecycle tests before registration. Seed rebuild and
bootstrap redeploy remain required for executable proof.
