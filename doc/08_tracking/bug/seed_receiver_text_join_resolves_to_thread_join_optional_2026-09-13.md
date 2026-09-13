# Seed HIR: `"sep".join(xs)` is typed as `Thread.join() -> i64?`, dropping the whole module to the interpreter

- Date: 2026-09-13
- Lane: Rust seed (`bin/simple.exe`, Windows x86_64-pc-windows-msvc), `run` JIT path
- Severity: P2 (silent 100-1000x slowdown; hard error under `SIMPLE_JIT_STRICT=1`)

## Symptom

`bin/caret --help` (= `simple run src/app/llm_caret/main.spl --help`) printed:

```
[jit-fallback] HIR lowering error: Unsupported feature: cannot apply `Add` to an optional
value that has not been unwrapped; `if x != nil:` does not narrow `T?` to `T` ...
[in src/app/llm_caret/main.spl]: whole module dropped to the interpreter
```

The error names only the entry file, not the offending expression.

## Root cause

`src/lib/common/net/http_core.spl` `normalize_path` ended with `"/" + "/".join(segments)`
(Python-style receiver-string join). The seed has no `text.join` typing, so method return
typing falls back to a by-name lookup and picks `Thread.join() -> i64?`
(`src/lib/nogc_sync_mut/concurrent/thread.spl:113`) whenever `std.concurrent.thread` is in
the co-compiled closure. The binop guard in
`src/compiler_rust/compiler/src/hir/lower/expr/operators.rs:50-75` then sees `text + i64?`
and rejects the module. Minimal closure that reproduces: `use std.concurrent.thread.*` plus
`use std.nogc_sync_mut.http_server.router.*` (re-exports http_core). Each alone lowers fine.

## Workaround landed

`normalize_path` now uses the canonical `segments.join("/")`; caret JITs under
`SIMPLE_JIT_STRICT=1`.

## Remaining seed defects (not fixed)

1. Method return typing must not resolve an unknown-receiver method by bare name to an
   unrelated class method (`Thread.join`).
2. The lowering error should carry the source file:line of the failing expression, not
   the entry module — locating this took a leave-one-out import bisect.
