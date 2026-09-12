# Placeholder-lambda callback passed to a free-function parameter is never invoked (returns `<lambda>`)

**Date:** 2026-07-20
**Found by:** whole-suite `test/unit/` triage campaign, cluster
`test/unit/lib/{gc_async_immut,gc_sync_immut}`
**Status:** open — genuine interpreter/compiler defect, reproduces under both
`bin/simple run` and `bin/simple test`

## Summary

A short-grammar placeholder lambda (`_1 + 1`, `_1 * 3`, `_1 > 2`, ...) passed
as an argument into a **user-defined free function** that later calls that
parameter as `f(x)` is never invoked. The call silently returns the
(unevaluated) lambda object itself instead of the computed value, and
`print`/`expect(...).to_equal(...)` shows `<lambda>` instead of the result.

The equivalent explicit lambda forms — a named function, `fn(x): x + 1`, or
`\x: x + 1` — work correctly in the exact same position. Built-in
higher-order methods (`[1,2,3].map(_1 + 1)`) and direct invocation
(`val g = _1 + 1; g(5)`) also work correctly. The bug is specific to
threading a placeholder lambda through a *user-defined* function parameter
and invoking it there.

## Minimal repro (reproduces under `bin/simple run`, no test harness needed)

```simple
fn call_once(f):
    return f(10)

fn main():
    print(call_once(_1 + 1))          # prints "<lambda>" -- BUG (expected 11)
    print(call_once(fn(x): x + 1))    # prints "11" -- correct
```

A second repro through a loop (matches the real `pmap` combinator shape):

```simple
fn my_pmap(items, f):
    var result = []
    var i = 0
    while i < len(items):
        result.push(f(items[i]))
        i = i + 1
    return result

fn main():
    print(my_pmap([1,2,3], add1))            # [2, 3, 4] -- named fn, correct
    print(my_pmap([1,2,3], fn(x): x + 1))     # [2, 3, 4] -- explicit lambda, correct
    print(my_pmap([1,2,3], _1 + 1))           # <lambda>  -- BUG
```

## Affected specs (fixed in this pass via value-preserving rewrite to `fn(x): ...`)

- `test/unit/lib/gc_async_immut/facade_resolution_spec.spl` — `pmap([1,2,3], _1 + 1)`
- `test/unit/lib/gc_async_immut/native_combinators_spec.spl` — `pmap([1,2,3], _1 * 3)`
- `test/unit/lib/gc_sync_immut/facade_resolution_spec.spl` — `pfilter([1,2,3,4], _1 > 2)`
- `test/unit/lib/gc_sync_immut/native_combinators_spec.spl` — `pmap([2,4], _1 + 5)`

All four now pass (`PASS ... 0 failures`) after rewriting the placeholder
lambda to `fn(x): <expr>`. The underlying `pmap`/`pfilter` implementations in
`src/lib/nogc_async_immut/combinators/__init__.spl` were not touched — they
were always correct; only the placeholder-lambda argument was broken.

## Relation to prior (STALE) docs

Two older docs cover adjacent but distinct territory and were marked STALE
2026-05-29 as "fixed" — this is either a regression of the same underlying
placeholder-lambda-in-callback-position defect, or those STALE dispositions
were never actually verified against the specific "threaded through a
user-defined function param" shape:

- `short_grammar_gc_async_pfilter_interpreter_2026-05-27.md` (pfilter
  placeholder predicate)
- `short_grammar_placeholder_value_binding_interpreter_2026-05-27.md`
  (placeholder bound to a `val` then passed as a predicate)

This doc's minimal repro is closer to those older reports' shape than to the
"unknown static method" test-vs-run landmine family — it is NOT that landmine
(reproduces identically under `run`, not just `test`).

## Root-cause hypothesis

Placeholder lambdas (`_1 + 1`) likely lower to a distinct "curried/callable"
representation from `fn(x): ...` closures. When threaded through a plain
(untyped) function-typed parameter and invoked via `param(...)` inside the
callee, the interpreter appears to treat the call expression as *constructing*
another placeholder-lambda value rather than *applying* the captured callable
— consistent with placeholder-call desugaring keying off the lexical call
site rather than the runtime value's actual callable-ness. Not root-caused
further (would require reading the placeholder-lambda desugaring/lowering
code, out of scope for this triage pass — no Rust seed source fix per the
fix-guide's scope).

## Triage 2026-09-12 — still reproduces; root cause is in the Rust seed, not pure Simple

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` sha256 `3d120a6f`

Repro (the record's own minimal case, unchanged):

```simple
fn call_once(f):
    return f(10)

fn main():
    print(call_once(_1 + 1))
    print(call_once(fn(x): x + 1))
```

```
$ SIMPLE_RUST_SEED_WARNING=0 bin/simple run /tmp/a_placeholder.spl
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
       Module error: function 'main' creates a lambda/closure the JIT closure ABI
       cannot compile (the closure handle is scalar-boxed (an `any`-typed slot),
       which shifts the pointer and corrupts it); JIT would return wrong values or
       crash; deferring to interpreter
<lambda>
11
```

Two findings the record did not have:

1. The JIT **refuses** this shape outright and says why — the placeholder lambda's
   handle lands in an `any`-typed (scalar-boxed) slot. So the wrong answer is
   produced by the interpreter fallback, not by the JIT.
2. The same `any`-boxing is almost certainly why the interpreter returns the lambda
   object instead of calling it: the untyped parameter `f` holds a boxed closure
   handle, and the call path does not unbox-and-invoke for the placeholder form
   while it does for `fn(x):` (which prints `11` in the next line of the same run).

Fix direction: the untyped-parameter call path must invoke a boxed closure handle
the same way it invokes an explicit lambda — i.e. unbox `any` before the
callable check, rather than treating a boxed handle as a plain value.

Not fixable from pure Simple: `bin/simple` is the Rust bootstrap seed
(`--version` says so), so this executes the seed's interpreter
(`src/compiler_rust/compiler/src/interpreter*`), which is out of scope for this
pure-Simple bug-fix lane.

- Status: OPEN (2026-09-12) — reproduced on 3d120a6f, diagnosed, needs a Rust-seed change
