# TcpListener.accept_timeout returns a non-blocking stream on Windows

Status: fix implemented, verification pending (2026-11-03). Found 2026-10-31
while building the DevHub loopback emulator. No admitted runtime execution is
claimed by this source repair.

`rt_io_tcp_accept_timeout` (`src/compiler_rust/runtime/src/value/net_tcp.rs:426-428`)
sets the listener non-blocking, accepts, then restores the listener. The accepted
stream is never set back to blocking. On Windows an accepted socket inherits the
listener's non-blocking mode, so the first read fails at once with WSAEWOULDBLOCK
unless the peer's bytes already arrived. `read_line_bounded`
(`src/lib/nogc_sync_mut/io/tcp.spl:328`) reports that as a connection reset.

## Reproduction

Server: `listener.accept_timeout(20000)`, then `stream.read_line_bounded(65536)`.
Client: an HTTP request.

Observed on Windows 11 with the Phase 1 seed: the first request was dropped and the
client saw `curl: (56) Recv failure: Connection was reset`. A later request succeeded
when its bytes were already queued. Replacing the call with blocking `accept()`
fixed it, with nothing else changed.

## Implemented shared synchronous boundary repair

The pure-Simple `std.nogc_sync_mut.sffi.net.io_tcp_accept_timeout` wrapper now
normalizes the newly accepted stream to blocking before returning it through
SOSIX/TcpListener (including scalar timeout-accept helpers). Negative runtime
results pass through unchanged. Normalization failure closes only the new stream
and returns failure; it never closes the listener. Raw close failures retain
their existing provider semantics. No public half-configured stream is returned.

The pure-Simple Win64 provider in `io/windows_tcp.spl` applies the same rule to
its own generation-checked logical handles. Its close path preserves its slot
when `closesocket` fails. The default POSIX C provider already polls then accepts;
the normalization wrapper makes its synchronous contract explicit. No C or Rust
implementation changes were required. The original Rust raw ABI and direct
asynchronous raw-ABI consumers are not claimed repaired by this synchronous
facade change.

The DevHub emulator now relies on the shared owner, removing its local mode
workaround. Its idle timeout remains unchanged. The real loopback scenario in
`test/02_integration/lib/sosix/hosted_tcp_boundary_spec.spl` accepts without queued
client bytes, configures a 200ms receive timeout, requires at least 50ms elapsed
before the empty read fails, then transfers a newline-terminated request. It
also proves reuse after an idle accept timeout and closes owned sockets before
asserting. `test/fixtures/compiler_entrypoint/windows_tcp_owner/main.spl`
exercises the direct pure-Simple Win64 provider with a nonblocking listener and
the same deadline check before its existing payload/ownership checks.

Required verification: execute the hosted regression and direct Win64 native
fixture with source-matched admitted producers/providers, then run the DevHub
emulator request/idle-exit regression. These checks are unrun; keep the bug in
`waiting_verify`, not fixed/done. A source review or authored test is not Windows
execution evidence.

## Fix (2026-11-13) — hosted regression spec misused `listen` (lane n3)

`hosted_tcp_boundary_spec.spl` was 2/3 on the Windows seed: the accept-timeout
example (this bug's regression) PASSED; "exchanges loopback text" failed with
`force unwrap failed ... Option::None` at line 85 (`address!`). Cause: it called
`sosix_tcp_listen` on the handle returned by `sosix_tcp_bind`, which is already
a listening socket (canonical provider contract, see `rt_io_tcp_bind` in
`runtime_native.c`). The seed's Rust provider answers `false` for `listen` on a
non-RawSocket entry, so the spec closed its own listener and `local_addr` was
None. Not Windows-specific and not a runtime defect. The example now uses the
documented pre-listen path `sosix_tcp_socket_create(0)` + `sosix_tcp_bind_fd` +
`sosix_tcp_listen`. Result on the Windows seed:
`bin/simple test test/02_integration/lib/sosix/hosted_tcp_boundary_spec.spl`
-> `passed=3 failed=0`. The direct Win64 native fixture and the DevHub emulator
regression are still unrun (they need a native build).
