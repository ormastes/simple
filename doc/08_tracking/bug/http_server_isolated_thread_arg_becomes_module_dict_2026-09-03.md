# SimpleHttpServer dies on the first connection — an isolated-thread arg arrives as the module dict

Filed 2026-09-03. Status: OPEN. Severity: HIGH — this breaks **every** in-repo
`SimpleHttpServer` user, not one lane.

## Symptom

The server binds and listens. The first accepted connection kills the process,
and the client sees `Connection reset by peer`.

```
SimpleHttpServer listening on 127.0.0.1:8721
error: semantic: method `handle_connection` not found on type `dict`
  (receiver value: {AtomicBool: <constructor:AtomicBool>,
   AtomicBool__compare_exchange: <fn:...>, AtomicBool__fetch_and: <fn:...>, ...})
```

The `dict` in that receiver is the **module namespace** — constructors and
functions of the imported module — not a `SimpleHttpServer`.

## Reproduction (independently reproduced end to end, 2026-09-03)

```
# terminal 1
src/compiler_rust/target/release/simple run src/app/slang_server/main.spl --plaintext-development
# terminal 2 — any HTTP GET against it
```
A Simple client using `http_get("http://127.0.0.1:8721/v1/models")` reports
`Network Error: ... Connection reset by peer (os error 54)` and the server
process is gone, having printed the error above.

Any `SimpleHttpServer` reproduces it; `slang_server` is merely the first thing
that tried to accept a connection today.

## Root cause

`src/lib/nogc_sync_mut/http_server/server.spl` `serve_loop` (~line 198):

```simple
val handler = thread_spawn_with_args(stream, self, \conn_stream, server:
    val srv: SimpleHttpServer = server
    SimpleHttpServer.handle_connection_admitted(srv, conn_stream)
)
```

`thread_spawn_with_args` (`src/lib/nogc_sync_mut/concurrent/thread.spl:149`)
forwards to **`rt_thread_spawn_isolated_with_args`**. The worker therefore runs
in an *isolated* environment. `data1` (the `TcpStream`) survives; `data2` (the
`SimpleHttpServer` class instance) does not — it arrives as the module
namespace dict, so the `val srv: SimpleHttpServer = server` annotation does not
convert it and the first method call fails.

The annotation is the trap: it reads like a checked cast and is not one.

## Why it is not caught by the existing fallback

`serve_loop` does have a synchronous fallback:
```simple
if handler.handle < 0:
    SimpleHttpServer.handle_connection_admitted(self, stream)
```
but that fires only when the **spawn fails**. Here the spawn SUCCEEDS and the
worker then dies on the mis-bound argument, so the fallback is never reached
and the failure is fatal rather than degraded.

## Scope

Everything that constructs a `SimpleHttpServer` and accepts a connection. The
unit specs of dependent lanes pass because they exercise the request
dispatcher directly and never open a socket — this defect lives strictly in the
accept path, which is exactly why it stayed invisible.

## What "fixed" looks like

Either the isolated-thread boundary carries a class instance intact, or
`serve_loop` stops sending one across it (pass the fields the worker needs, or
handle the connection on the accept thread). A fix must be verified by a real
socket round-trip, not by a dispatcher-level unit spec — a spec that never
opens a socket cannot see this.

## Not claimed here

That `rt_thread_spawn_isolated_with_args` is wrong to isolate. Isolation may be
the intended contract, in which case the defect is `serve_loop` passing an
instance through it, and the fix belongs in `server.spl`. Deciding that is the
http_server owner's call; this record does not preempt it.

## Related

- Blocks the live lane of `src/app/slang_server/main.spl`. That server's
  request dispatcher is separately spec-verified (18 examples) — the contract
  is proven, the socket path is not.
