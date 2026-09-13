# Seed HIR: `"sep".join(xs)` is typed as `Thread.join() -> i64?`, dropping the whole module to the interpreter

- Date: 2026-09-13
- Lane: Rust seed (`bin/simple.exe`, Windows x86_64-pc-windows-msvc), `run` JIT path
- Severity: P2 (silent 100-1000x slowdown; hard error under `SIMPLE_JIT_STRICT=1`)
- Status: FIXED IN SEED SOURCE. Needs a seed redeploy: the deployed Windows
  `simple.exe` still has the bug, and the `http_core` workaround below covers it until then.

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
(Python-style receiver-string join). The seed's string-receiver builtin table
(`hir/lower/expr/mod.rs`, `if is_string`) had no `join` entry. Only the array table typed it.
So method return typing fell back to a by-name `.join` suffix lookup and picks `Thread.join() -> i64?`
(`src/lib/nogc_sync_mut/concurrent/thread.spl:113`) whenever `std.concurrent.thread` is in
the co-compiled closure. The binop guard in
`src/compiler_rust/compiler/src/hir/lower/expr/operators.rs:50-75` then sees `text + i64?`
and rejects the module. Minimal closure that reproduces: `use std.concurrent.thread.*` plus
`use std.nogc_sync_mut.http_server.router.*` (re-exports http_core). Each alone lowers fine.

## Workaround landed

`normalize_path` now uses the canonical `segments.join("/")`; caret JITs under
`SIMPLE_JIT_STRICT=1`.

## Seed fix

Added `"join" => Some(TypeId::STRING)` to the string-receiver builtin table in
`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`. Regression test:
`text_receiver_join_is_not_typed_as_unrelated_user_join_method` in
`hir/lower/tests/expression_tests.rs`. It declares `class Thread` with `fn join() -> i64?`
and lowers `"/" + "/".join(parts)`.

## Remaining seed defects (not fixed)

1. The generic `.method` suffix fallback is still receiver-blind for methods missing from
   the builtin tables. Any other text or array builtin that is absent there can still be
   typed from an unrelated user class.
2. The lowering error should carry the source file:line of the failing expression, not
   the entry module — locating this took a leave-one-out import bisect.
