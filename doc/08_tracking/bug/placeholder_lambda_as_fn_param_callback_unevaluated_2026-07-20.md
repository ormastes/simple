# Placeholder-lambda callback passed to a free-function parameter is never invoked (returns `<lambda>`)
## Open 2026-09-21 — AST argument shape passes; callback-value proof unavailable

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Revalidated from exact `origin/main` revision
`e0dd873da1b7828389db4eb60e82972cc8245313` on 2026-09-21:

- The deployed `bin/simple.exe` is a Rust bootstrap seed (SHA-256
  `E2A42543D62F794A8DF8389DE70C4200FF95675B5C48B60F0103B1F47A77E78C`).
  It still reproduces the report: named and explicit lambda controls pass,
  while the free-function, multi-hop, `pmap`-shaped loop, and numbered
  placeholder cases nested inside SSpec expectations return `<lambda>`. This
  is diagnostic seed evidence only.
- A separate seed `run` probe that first bound each callback result to a `val`
  produced the expected values for direct invocation, built-in `map`,
  free-function, multi-hop, `pmap`, and numbered forms. The broad historical
  framing "never invoked" is therefore not established for current source;
  the retained red requires an outer consumer expression around the callback
  call, consistent with a placeholder scope/ownership defect.
- The working-copy pure-Simple frontend AST probe passes
  `test/01_unit/compiler/frontend/placeholder_lambda_callback_param_spec.spl`:
  four examples find matching ordinary-call and method-call nodes whose
  callback argument is `EXPR_LAMBDA` with the expected arity. The named
  function control is `EXPR_IDENT`; the explicit lambda control is also
  `EXPR_LAMBDA`. The probe scans the expression arena and does not prove that
  the matching node is the reachable executable root or that evaluation
  returns the required value.
- `src/compiler/10.frontend/core/parser_expr.spl::parse_call_arg` is the
  candidate parser boundary. It applies `transform_placeholder_lambda` to the
  raw argument before the enclosing call is built. Source inspection shows
  explicit and placeholder lambdas share `eval_lambda` and `eval_call`, but
  execution through those paths remains unverified.
- Runtime revalidation through `core_interpret` is blocked: the seed-hosted
  source probe terminates with Windows status `0xC000001D` (illegal
  instruction) before producing a result, and no admitted Stage 2/3/4 or
  deployed pure-Simple Windows binary with matching provenance exists in this
  worktree. Native proof with `SIMPLE_NO_STUB_FALLBACK=1` is therefore absent.
  `test/01_unit/compiler/frontend/fixtures/placeholder_lambda_callback_value_probe.spl`
  retains the value-based interpreter/native regression for that future run.

Keep this row **open** until an admitted pure-Simple interpreter and native
candidate both pass the callback-value regression. The AST evidence alone is
insufficient to close it or justify a parser/evaluator source change.

**Date:** 2026-07-20
**Found by:** whole-suite `test/unit/` triage campaign, cluster
`test/unit/lib/{gc_async_immut,gc_sync_immut}`
**Status:** open — historical interpreter/compiler defect; current admitted
interpreter/native behavior is unverified

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

## Historical minimal repro

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
