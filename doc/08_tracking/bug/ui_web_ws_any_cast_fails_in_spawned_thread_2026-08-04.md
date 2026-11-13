# Web server dies on first WebSocket upgrade: `as TcpStream` cast fails in spawned reader thread

- **ID:** ui_web_ws_any_cast_fails_in_spawned_thread_2026-08-04
- **Status:** FIXED (closed 2026-11-13; failing cast removed, regression spec added)
- **Severity:** high (kills `run_web_wm` / `run_async_web` on the first real client)
- **Found by:** Kimi GUI-check lane, 2026-08-04

## Evidence

Launch the Web WM:

```bash
SIMPLE_LIB=src SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_UI_WEB_ALLOW_INSECURE_DEV_SECRET=1 \
  <gui-driver> run examples/06_io/ui/web_wm.spl
```

The first HTTP request succeeds (the WM page is served; a browser renders the
full desktop). The moment the page opens the `/ui/ws` WebSocket, the server
process dies:

```
error: semantic: type mismatch: cannot cast object to TcpStream
```

The failing statement is `val tcp = stream as TcpStream` in
`src/app/ui.web/async_ws.spl:30` (`start_ws_reader`), executed in the
per-client reader thread spawned at `src/app/ui.web/async_server.spl:292-294`
via `thread_spawn_with_args`.

## Why it is interesting

The identical `as TcpStream` pattern in
`src/app/ui.web/tls_serve_loop.spl:102-206` (`ConnStream.from_tcp` /
read/write paths) succeeds — on the main accept thread. The cast fails only
after the `Any` crosses the `thread_spawn_with_args` boundary. This isolates
the defect to thread-context type registration (or `Any` payload transport)
in the rust-seed interpreter: the spawned thread cannot resolve the
`TcpStream` class identity that the main thread registered.

## Repro

1. Start the server as above.
2. `curl -s http://localhost:3333/ >/dev/null` (works, 200).
3. Open `http://localhost:3333/` in any browser (or `websocat ws://localhost:3333/ui/ws`).
4. Server exits with the cast error.

## Fix direction

Two lanes:

- **Runtime (root):** in the seed interpreter's thread spawn, make the
  class/enum registration environment visible to the child thread (or carry
  the owner module identity with `Any` so `as` re-resolves by name). Gated
  probe: print the class-table size inside a spawned thread.
- **Server (workaround, if the runtime fix is far out):** avoid `Any` for the
  reader args — e.g. register the accepted `TcpStream` in a shared typed
  registry and pass only the `i64` key to the thread, re-acquiring the stream
  inside the thread through the same typed API used by the accept loop.

## 2026-11-13 closure (UI batch B, Linux aarch64, release/1.0.0 @ 35144b7f5e93)

Stale on current release/1.0.0, closed with a regression spec.

- The failing statement is gone. `start_ws_reader` now takes a typed
  `stream: TcpStream` (`src/app/ui.web/async_ws.spl:24`) and
  `thread_spawn_with_args<A, B, R>` is generic
  (`src/lib/nogc_sync_mut/concurrent/thread.spl:173`), so no `Any` crosses the
  thread boundary and there is no `as TcpStream` cast left to fail.
- New spec `test/01_unit/lib/nogc_async_mut/thread_tcp_stream_worker_spec.spl`
  pins the behaviour the reader thread depends on, with a real loopback socket
  pair and no mock: (1) an accepted `TcpStream` object passed through
  `thread_spawn_with_args` is read and written by the worker, and the client
  reads the worker's reply; (2) the same through the scalar-descriptor route
  (`accept_fd_timeout` + `TcpStream.from_accepted_fd`), which is the
  "workaround" lane this doc proposed. Result on the Rust seed:
  `outcome=OK declared>=2 executed=2 passed=2 failed=0`, rc=0.

No red state could be produced on this base, so the spec is a regression pin,
not a red-to-green fix. Not run: the end-to-end `web_wm.spl` + browser
WebSocket upgrade, which needs a WebSocket client this host does not have.
One stale comment remains at `src/app/ui.web/server.spl:276-279` saying a
worker's writes "don't deliver in the interpreter"; scenario (1) shows they
do on this seed. The synchronous handling there is a separate design choice
and was left alone.
