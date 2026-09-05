# `SimpleHttpServer` accepts a connection and then dies: `handle_connection` not found on type `dict`

- **Filed:** 2026-09-04
- **Status:** Open
- **Severity:** every in-repo HTTP server is unusable on the bootstrap seed.
  The listener binds, the client connects, and the first request kills the
  server process.
- **Binary under test:** `src/compiler_rust/target/bootstrap/simple`
  (154,560,904 bytes, mtime 2026-09-04 09:47). `bin/simple` did not exist during
  this session -- `bin/release/aarch64-unknown-linux-gnu/` was emptied at 11:35
  by an in-flight bootstrap owned by another session.

## Symptom

Server side, on the first accepted connection:

```
SimpleHttpServer listening on 127.0.0.1:8721
error: semantic: method `handle_connection` not found on type `dict`
  (receiver value: {AtomicBool: <constructor:AtomicBool>,
   AtomicBool__compare_exchange: <fn:AtomicBool__compare_exchange>,
   AtomicBool__fetch_and: <fn:AtomicBool__fetch_and>, ...})
```

Client side, at the same moment:

```
ERROR: HTTP error: rt_http_request error:
  http://localhost:8721/v1/chat/completions:
  Network Error: Error encountered in the status line: Connection reset by peer (os error 104)
```

## Reading the receiver value

The receiver is not a `SimpleHttpServer`. It is the **flattened module
namespace** -- a dict whose keys are the module's own top-level names
(`AtomicBool`, `AtomicBool__compare_exchange`, ...). So `self` inside the
server's accept loop is bound to the module dict rather than to the server
instance, and the method lookup then correctly reports that a dict has no
`handle_connection`. The bug is the binding, not the lookup.

That shape -- `Name` and `Name__method` side by side in one dict -- is the
co-compiled/flattened unit the compiler builds when several modules are
compiled together. This is very likely the same family as the co-compilation
warnings the seed emits on every run of this code, e.g.

```
warning: public function `atomic_bool_new` has 2 co-compiled definitions with
2 differing signatures ((bool)->AtomicBool vs (bool)->bool); JIT call sites
resolve by exact arg-type match ... falling back to the last definition when
types are ambiguous
```

`atomic_bool_new` collides in exactly the namespace that shows up as the bad
receiver. That is a lead, not a conclusion.

## Reproduction

```bash
# terminal 1
src/compiler_rust/target/bootstrap/simple run src/app/slang_server/main.spl -- \
    --plaintext-development --models=/home/yoon/dev/model --port=8721
# waits, prints "SimpleHttpServer listening on 127.0.0.1:8721"

# terminal 2 -- any client will do; this is the one that found it
src/compiler_rust/target/bootstrap/simple run src/app/llm_caret/main.spl \
    --provider slang --model Qwen3-Coder-Next-Q4_K_M --prompt "hi"
```

Nothing here is slang-specific: `slang_server` contributes a router and two
handlers and owns no socket code. Any user of
`std.nogc_sync_mut.http_server.server.SimpleHttpServer` should reproduce it.

## Impact on the caret/slang work

This is the second seed defect blocking caret's HTTP hop to slang; the first is
`doc/08_tracking/bug/seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md`,
which would have killed the same request slightly earlier for a different
reason. Both are in the seed, neither is in slang or caret.

Worked around, not hidden: slang gained its offline entrypoint
(`src/lib/gc_async_mut/slang/entrypoints/llm.spl`, mirroring
`vllm/entrypoints/llm.py`) and caret gained a `slang_local` provider that uses
it in-process. The `slang` HTTP provider is untouched and still the right path
once a pure-Simple binary is deployed -- the two providers differ in transport,
not in engine, and both report which one answered.

## What would close this

A run of the reproduction above on a deployed pure-Simple `bin/simple` that
serves the request instead of dying. If it reproduces there too, the defect is
in `http_server`, not in the seed, and this record should be re-scoped
accordingly.
