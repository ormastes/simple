# Enum variants resolve globally by bare name: colliding `HttpMethod` stops every HTTP server

Date: 2026-09-06
Status: OPEN
Area: Rust seed — `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ident.rs`

## Symptom

No HTTP server in this repo can start under `bin/simple run`:

```
bin/simple run src/app/llm_caret/main.spl --provider dummy --server --port 18317
  -> error: semantic: unknown variant or method 'Get' on enum HttpMethod
```

The process dies before binding; `ss -ltn` shows nothing listening. This is why
the caret demo server's envelopes could only be validated in-process rather than
over a socket.

## The code is correct — the resolver is not

- `src/std/nogc_sync_mut/http_server/router.spl:41` uses `HttpMethod.Get`.
- The enum is defined at `src/std/nogc_sync_mut/http_server/types.spl:11-18`
  with the variant spelled `Get`, matching exactly, and is correctly imported at
  `router.spl:8`. The `src/lib/...` copy is byte-identical — no std/lib
  divergence.

So it is neither a name/case mismatch nor a missing import.

## Root cause

The tree contains **four separate `enum HttpMethod` definitions**, and two of
them use UPPERCASE variants:

| definition | variants |
|---|---|
| `src/std/nogc_sync_mut/http_server/types.spl:11` | `Get, Post, ...` |
| `src/std/nogc_sync_mut/net/http.spl:32` | `GET, POST, ...` |
| `src/std/nogc_sync_mut/io/http_sffi.spl:122` | `GET, POST, ...` |

`src/app/llm_caret/openai_compat.spl:8` imports
`std.nogc_sync_mut.io.http_sffi.{http_request_raw}`, which pulls that module's
uppercase `HttpMethod` into the same compilation unit as `http_server`'s
capitalized one.

The seed's variant check — `enum_declares_variant` in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ident.rs:31-66` —
resolves the bare type name `HttpMethod` against a **global-by-name** registry
rather than per-import scope. In a large cross-module unit it therefore selects
the wrong same-named enum, and `Get` correctly appears undeclared on it.

## Confirmed by minimal reproducer

- Importing only `http_server.types.{HttpMethod}` and using `HttpMethod.Get`
  → **ok**.
- Adding a second import of `io.http_sffi.{http_request_raw}` to the same file
  → **identical failure**, `unknown variant or method 'Get' on enum HttpMethod`.

## It is general, not `HttpMethod`-specific

`HttpStatus` is also duplicated between `types.spl` and `io/http_sffi.spl`, but
both definitions happen to share the variant `BadRequest` used at
`router.spl:80`, so it resolves "correctly" **by coincidence**. Any two
same-named enums whose variant sets differ will hit this.

## Why no test caught it

`find test -path '*http_server*' -name '*_spec.spl'` returns ~20 specs, but
`grep -rl "Router" test/01_unit/lib/http_server/ test/unit/lib/http_server/`
returns nothing — no spec instantiates a `Router` or calls `.get()`/`.post()`.
The failing path has zero coverage.

## Two independent fixes, both worth doing

1. **Seed (real fix):** scope enum-variant resolution by module/import instead
   of by bare name. Until then any same-named enum pair is a latent trap.
2. **Repo hygiene (available now, pure Simple):** de-duplicate or rename the
   colliding `HttpMethod` definitions in `io/http_sffi.spl` and `net/http.spl`.
   Four definitions of one protocol enum is itself the smell that made the
   resolver bug reachable.

Additionally: add a spec that actually mounts a `Router` and serves a request,
so this path stops being uncovered.

Binary measured: `bin/release/aarch64-unknown-linux-gnu/simple`,
`Simple Language v1.0.0-rc.1` (Rust bootstrap seed).
