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


## Triage 2026-11-13 (lane p3-async-20261113, base 80a8116e5e2) — reproduced live; defect is now seed-level, one layer deeper than the cast

The written-`Any` symptom this record filed is gone: commit 28df8ceac42
("feat(types): written Any policy and Any-free compiled sources") retyped
`start_ws_reader(stream: TcpStream, event_channel: BoundedChannel<UIEvent>)`
and the `as TcpStream` cast no longer exists in `src/app/ui.web/`. Fresh
reproduction on this base shows the WebSocket reader-thread architecture is
still unbuildable on the seed — the failure moved from the cast error to a
silent child-thread never-run / event-drop:

**Evidence (all seed `bin/simple.exe` on this base; probes in
`build/p3-probe/` of the lane worktree):**

1. `thread_spawn_with_args` transport matrix under `bin/simple run` (hybrid
   engine): `(i64, i64)` args — child runs; `(text, i64)`, `(class, i64)`,
   `(i64, class)` — **the spawned child never executes a single statement**
   (marker-file verified). The original repro shape
   `(TcpStream, BoundedChannel<UIEvent>)` dies the same way. Compare
   `test/03_system/web/server/http_serve_loop_live_socket_spec.spl`, which
   passes the same `(text, class)` shape only because the spec runner's
   interpreter path transports Values directly.
2. Scalar handoff works end-to-end: passing the accepted fd as `i64`
   (`raw_fd`) + `TcpStream.from_accepted_fd(fd)` reconstruction in the child,
   the child **reads real request bytes off the parent-accepted socket**
   (`s5_read16 len=16`, `s7_read16b len=16` in `build/p3-probe/v3`).
3. Module-level globals are shared across the thread boundary in both
   directions (child read the parent's mutation; parent observed the child's
   write — `main_global=child_value` in `build/p3-probe/v3`).
4. Runtime `Channel` delivery is broken in `run` context (both hybrid and
   `--mode=interpreter`): same-thread `send<i64>`/`try_recv<i64>` round-trips
   (`build/p3-probe/v5` → `got=41`), but same-thread **text values are
   silently dropped** (`build/p3-probe/v4` self-round-trip → NONE), and
   cross-thread sends from a spawned child are either rejected outright
   (`try_send<text>` → false) or accepted and lost (`try_send<i64>` → true,
   parent recv → nil).

**Consequence for this bug:** the record's suggested server-side workaround
(shared typed registry + i64 key, fd re-acquire in the child) is validated as
necessary-but-NOT-sufficient — the reader can be handed the socket (2) and
can share globals (3), but it has **no working channel to deliver parsed
UIEvents to the server thread** (4), and passing the channel object directly
kills the child (1). Any pure-Simple rework of `async_server.spl` /
`async_ws.spl` on this seed would still hang on the first upgrade; the
GUI-driver end-to-end verification this lane would need is impossible without
the seed fixes.

**Seed-level fix surface (`src/compiler_rust/**`):**
- `rt_thread_spawn_isolated_with_args` arg marshalling under the hybrid
  native splice: non-scalar `Value`s never reach the child's first
  statement (no error, no handle failure — silent).
- `rt_channel_send`/`rt_channel_try_recv` value transport: text values lost
  same-thread; cross-thread delivery lost for scalar values too.
- Gated probes shipped with this lane's evidence:
  `build/p3-probe/iso.spl` (arg matrix), `v2.spl`/`v3.spl` (fd+global
  handoff, bisected hang), `v4.spl`/`v5.spl` (channel characterization).

Also affected by (1): `file_watcher_loop` (`async_server.spl:118-127`) — its
`(text, BoundedChannel<UIEvent>)` args meet the same transport failure.
Verdict: seed-blocked; no pure-Simple source change landed in this lane.
