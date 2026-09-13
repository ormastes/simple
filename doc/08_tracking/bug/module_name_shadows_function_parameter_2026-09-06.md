# An imported module name shadows a function's own parameter

Date: 2026-09-06
Status: OPEN (four call sites worked around; resolver unfixed)
Area: Rust seed name resolution

## Summary

A bare identifier that names both an imported MODULE and a local binding
(function parameter, lambda parameter) resolves to the **module**. The
function's own parameter loses.

This is the same defect family as
`enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06.md`
— bare names resolved against a global registry instead of by scope — but it is
strictly worse, because the shadowed binding is a *parameter of the very
function doing the lookup*.

## How it presented

`src/lib/nogc_sync_mut/http_server/server.spl` had a lambda parameter named
`server`:

```spl
val handler = thread_spawn_with_args(stream, self, \conn_stream, server:
    val srv: SimpleHttpServer = server        # <- resolves to the MODULE
    SimpleHttpServer.handle_connection_admitted(srv, conn_stream)
)
```

Any application doing `use <pkg>.server.{...}` — `src/app/llm_caret/main.spl:70`
does exactly that — binds the bare name `server` to that module. So `srv` became
the module's namespace dict, and the next line died:

```
error: semantic: method `handle_connection` not found on type `dict`
  (receiver value: {ProcessResult: <constructor:ProcessResult>, _LB: <fn:_LB>,
   _Q: <fn:_Q>, _RB: <fn:_RB>, _build_chat_completion_chunk: <fn:...>, ...})
```

The receiver dump is the giveaway: those are `src/app/llm_caret/server.spl`'s
top-level functions. The server bound its port, accepted one connection, then
died — every later connection got ECONNREFUSED.

`static fn handle_connection_admitted(server: SimpleHttpServer, ...)` had the
same latent flaw one frame down.

## Workaround applied

Both were renamed to `srv`/`owner` — already the convention used at the adjacent
call site — with comments pointing here. That is a rename around a resolver bug,
not a fix.

## Why this matters beyond one file

`server`, `config`, `types`, `main`, `provider`, `tools` are all common module
names in this tree AND natural parameter names. Any collision silently binds the
module. Nothing warns.

## The real fix

Scope resolution must prefer, in order: local bindings (parameters, `val`/`var`)
→ enclosing scopes → imported module names. A parameter must always win over a
module of the same name. Ideally a same-name collision emits a warning even when
resolution is correct.

## Discovery chain (all one root cause)

Getting the caret demo server to actually serve required peeling four layers,
each hidden behind the previous:

1. `HttpMethod.Get` unresolvable — colliding `enum HttpMethod` definitions.
2. `handle_connection` on a `dict` — **this bug**.
3. `with_header` not found on `HttpResponse` — a colliding `HttpResponse`, where
   the winner was `io/http_sffi`'s plain `struct` (no methods).
4. `missing return in ... http_status_code`, then
   `unknown variant 'OK' on enum HttpStatus` — a colliding `HttpStatus`.

Layer 4 also exposed a **real latent typo the collision had been masking**:
`main.spl:490` and `messaging/adapter/server/http_server.spl:18` wrote
`HttpStatus.OK`, but `http_server`'s enum spells it `Ok`. Every neighbouring arm
in those same functions (`BadRequest`, `NotFound`, `Created`) used
`http_server`'s CamelCase, so the intent is unambiguous — the code only ever
worked because the *other* `HttpStatus` (uppercase `OK`) was winning the global
lookup. A scope-correct resolver would have rejected this on day one.

## Verification that the chain is now clear

With the four workarounds in place the server serves for real over a socket —
`GET /v1/health` 200, `POST /v1/chat/completions` 200 with a full OpenAI
envelope, and `stream:true` returning `Content-Type: text/event-stream` with
three `chat.completion.chunk` frames and a terminal `data: [DONE]` — and stays
up across all three requests.

Binary measured: `bin/release/aarch64-unknown-linux-gnu/simple`,
`Simple Language v1.0.0-rc.1` (Rust bootstrap seed).

## Triage 2026-09-12 — still OPEN, but the two simple shapes now resolve correctly

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).
Identical results on the default (JIT) and `SIMPLE_EXECUTION_MODE=interpreter`.

Three probe shapes, all of which the summary above predicts should bind the
MODULE and lose the local binding:

**1. Named import, function parameter.** `use std.nogc_sync_mut.io.file.{read_file_text}`
(so the bare name `file` names an imported module) plus
`fn takes_file(file: i64) -> i64: return file + 1`:

```
param=42        # correct — the parameter won, not the module
```

**2. Named import, lambda parameter.** `val f = \file: file + 2` in the same file:

```
lambda=12       # correct
```

**3. Sibling module by relative import, struct-typed parameter, with the
`val srv: Srv = server` re-binding line from the original report.** A local
`server.spl` exporting `mod_marker()`, imported as `use .server.{mod_marker}`,
and `fn takes(server: Srv) -> str: val srv: Srv = server; …`:

```
id=7            # correct — srv is the struct, not the module namespace dict
MODULE          # and the module's own function is still reachable
```

### What this does and does not establish

It does **not** close the bug. The original failure was in
`src/lib/nogc_sync_mut/http_server/server.spl` inside a
`thread_spawn_with_args(stream, self, \conn_stream, server: …)` lambda — a
lambda parameter captured across a thread-spawn boundary — and that shape was
**not** reproduced here. The three shapes above are the ones a reader would try
first from the summary, so recording that they are clean saves the next person
the same 20 minutes, and narrows the suspect surface to the capture/spawn path
rather than plain name resolution.

Left OPEN. The workarounds in `server.spl` (`srv`/`owner`) should stay until
the thread-spawn shape is probed directly; removing them on the strength of
these three probes would be unjustified.

Seed-side in any case: this is Rust name resolution, out of scope for a
pure-Simple bugfix lane.
