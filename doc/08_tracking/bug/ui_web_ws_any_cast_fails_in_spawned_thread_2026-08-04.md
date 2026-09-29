# Web server dies on first WebSocket upgrade: `as TcpStream` cast fails in spawned reader thread

- **ID:** ui_web_ws_any_cast_fails_in_spawned_thread_2026-08-04
- **Status:** OPEN
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
