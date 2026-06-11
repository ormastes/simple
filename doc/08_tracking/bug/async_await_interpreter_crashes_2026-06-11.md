# Async/Await Interpreter Crashes - 2026-06-11

Status: partially-fixed (2026-06-11) — await value corruption FIXED; generator/actor desugar scope + deep Promise/FutureValue reconcile still open

**Fixed 2026-06-11:** the SIGSEGV had already become silent corruption
(`await f()` always yielded 3 = NIL bit pattern in JIT mode; a semantic error
in interpreter mode). Root causes fixed:
- `rt_future_await` (runtime/src/value/async_gen.rs): non-Future input now
  returns the value itself (eager-async identity), not NIL.
- Interpreter `Expr::Await` (compiler/src/interpreter/expr.rs): non-Future/
  non-Actor values route through `await_value` (Promise extract + passthrough)
  instead of erroring.
`await f()` now returns the body value in BOTH default-JIT and forced
interpreter modes. Regression spec:
`test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl` (3/3).

**Still open:** yield/generator + actor desugar HIR scope visibility; the
deeper Promise-vs-FutureValue representation reconcile; real `Future<T>` inner
type propagation (HIR still hardcodes I64 for await — masked by eager
semantics, wrong once futures become lazy).

## Summary

End-to-end `async fn` + `await` crashes the Rust-seed interpreter instead of
producing a value or a typed error. Found during the 2026-06-11 async audit
(plan: `doc/03_plan/language/concurrency/async_green_process_hardening.md`).

## Symptoms (probe programs, interpreter mode)

- `async fn f() -> i64: 42` + `val x = await f()` → SIGSEGV (exit 139).
- `yield` in a generator fn → "yield called outside of generator" +
  "Unknown variable: gen" (desugared class not visible to HIR scope).
- `actor` definition → same desugar/HIR scope visibility failure.
- `spawn fn()` runs, but the spawned closure SIGABRTs (exit 132) at cleanup.

## Root Cause (diagnosed)

- `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:193` hard-codes
  `TypeId::I64` as the `await` result type.
- The MIR executor calls `rt_future_await` on a Simple `Promise` object
  (`wrap_in_promise`) while the runtime expects a Rust `FutureValue` —
  two unreconciled async value representations
  (`src/compiler_rust/compiler/src/value_async.rs`).
- Desugar output (generator/actor classes) is registered after HIR scope is
  built, so generated symbols are unresolvable at call sites.

## Required Fix

1. Guard `rt_future_await` against non-`FutureValue` input → typed error
   (removes the SIGSEGV class).
2. Reconcile Promise vs FutureValue in the interpreter dispatch path.
3. Re-inject desugared declarations into HIR scope before lowering bodies.
4. Propagate the real `Future<T>` inner type for `await`.

## Coverage Gap

`test/01_unit/compiler/async/*` is placeholder-grade (9/11 specs are single
skips; remaining tests assert literals). De-hollowing is tracked in the same
plan; real semantics tests must land with the fix, not before (they would
SIGSEGV the runner today).
