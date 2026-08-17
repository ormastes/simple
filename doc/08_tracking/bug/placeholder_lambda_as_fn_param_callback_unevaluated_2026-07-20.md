# Placeholder-lambda callback passed to a free-function parameter is never invoked (returns `<lambda>`)

**Date:** 2026-07-20
**Found by:** whole-suite `test/unit/` triage campaign, cluster
`test/unit/lib/{gc_async_immut,gc_sync_immut}`
**Status:** open — STILL LIVE, re-verified by content 2026-08-17. Genuine
compiler (parser/desugar) defect. **BLOCKED — OUT OF SCOPE for stdlib lanes:**
root cause is in the placeholder-lambda desugaring in the frontend, not in
`src/lib/**`.

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

## Re-verification 2026-08-17 (still live) + root cause NARROWED

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (the Rust seed —
`bin/simple --version` prints the bootstrap-seed warning). Engine is the
tree-walk interpreter: the JIT declines the module with
`function 'main' creates a lambda/closure; the JIT closure ABI does not
tag-box lambda arguments or results ... deferring to interpreter`.

Probe A (`bin/simple run`, exit 0) — the doc's own two repros verbatim:

```
<lambda>          # call_once(_1 + 1)      BUG (expected 11)
11                # call_once(fn(x): x+1)  correct
[2, 3, 4]         # my_pmap(..., add1)     correct
[2, 3, 4]         # my_pmap(..., fn(x):..) correct
<lambda>          # my_pmap(..., _1 + 1)   BUG
```

Probe B is the new information and **falsifies the doc's original hypothesis**
("threading a placeholder lambda through a user-defined function parameter is
broken"). Binding the placeholder to a `val` FIRST and passing that same value
into the same user function works:

```
6                 # val g = _1 + 1 ; g(5)          correct
11                # call_once(g)                    CORRECT — threading is fine
[2, 3, 4]         # [1,2,3].map(_1 + 1)             correct
11                # call_once(\x: x + 1)            correct
```

So the parameter-threading path is NOT broken. The defect is purely
**syntactic/parse-time**: a placeholder written INLINE in a call-argument
position is captured by the WRONG enclosing expression. `call_once(_1 + 1)`
does not build a lambda and pass it — it desugars the whole enclosing call into
a lambda, roughly `\a: call_once(a + 1)`. That is exactly why `print` shows
`<lambda>` and why `[1,2,3].map(_1 + 1)` still works (method-call arguments get
their own per-argument transform; a plain free-function call argument does
not). Confirming detail: `val r = call_once(_1 + 1)` followed by `r(7)` does
not even resolve — `error[E1002]: function \`r\` not found` — the produced
value is not an ordinary callable binding.

**Root cause location (do not edit from a stdlib lane):**
`src/compiler/10.frontend/desugar/placeholder_lambda.spl` — the
`parse_call_arg` / `transform_placeholder_call_args_after_interpolation`
per-argument transform (see that file's own header comment at lines 45-70
describing the parser's distinction between "real call arguments" and nested
sub-parsed regions, and the argument-scoping walk at lines 275-350). The
free-function call-argument case is the one that hoists to the enclosing call
instead of wrapping the argument.

**Correct workaround until fixed** (better than the doc's original advice of
rewriting to `fn(x): ...`, because it preserves the short grammar): bind the
placeholder to a `val` on the previous line and pass the binding.

## Root-cause hypothesis (superseded by the section above)

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
