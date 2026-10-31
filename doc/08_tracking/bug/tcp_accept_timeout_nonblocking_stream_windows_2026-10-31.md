# TcpListener.accept_timeout returns a non-blocking stream on Windows

Status: open. Found 2026-10-31 while building the DevHub loopback emulator.

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

## Fix direction

Call `stream.set_nonblocking(false)` on the accepted stream in
`rt_io_tcp_accept_timeout` before registering it. This needs a seed rebuild, so it
was not done in the emulator lane; `test/fixtures/devhub/emulated/emu_http_server.spl`
uses `accept()` instead. Any server using `accept_timeout` on Windows is affected,
including `test/fixture/net/simple_http_server.spl:133`.
