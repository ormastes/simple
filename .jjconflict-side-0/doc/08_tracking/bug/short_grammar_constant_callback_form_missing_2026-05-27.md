# Constant callbacks use wildcard lambda short grammar

Status: Status: RESOLVED (verified 2026-05-29)

Date: 2026-05-27

## Symptom

After migrating safe single-expression lambdas to placeholder grammar, the
remaining simple callback hits are mostly already-minimized wildcard callbacks:

```simple
items.map(\_: 0)
headers.map(\_: "---")
future.then(\_: HostFuture.pending())
pipeline.filter(\_: true)
```

The supported compact form for this case is the wildcard lambda `\_:`. It means
"ignore the callback argument and return this expression" while still passing a
function to `map`, `filter`, `then`, and related higher-order APIs.

## Impact

The short-grammar fixer can safely convert `\x: constant` to `\_: constant`.
It must not rewrite existing `\_:` callbacks to a non-lambda expression. Doing
so would pass the constant value itself rather than a callback.

## Resolution

**Status: RESOLVED** (verified 2026-05-29)

The `\_:` wildcard lambda form is fully supported end-to-end:

- Parser produces `EXPR_LAMBDA` with `_` as parameter name for `\_: expr`.
- `placeholder_lambda.spl` (`replace_placeholders`) returns `EXPR_LAMBDA`
  unchanged — correct scoping boundary behaviour.
- `apply_fn(\_: 0, 42)` → 0; `apply_fn(\_: "---", x)` → `"---"` (runtime
  verified via working non-map paths).
- Fixer (`lint_short_grammar.spl`) emits `\_: expr` for `\x: constant` where
  `x` does not appear in the body (guard at line 397 prevents double-applying).
- Test "does not rewrite already-wildcard constant callbacks" confirms
  `\_: "---"` and `\_: true` are left unchanged (spec line 230-233).

Documented `\_:` as the canonical compact callback form for ignored callback
arguments. Remaining `\_:` hits in short-grammar migration scans are intentional.

## Related open issue

Resolved 2026-05-30: `[].map(\f: ...)` and `[].map(\_: 0)` no longer crash in
the interpreter or native runner. Added
`test/01_unit/compiler/empty_array_map_lambda_spec.spl` to lock the empty literal
array callback path for both wildcard and named lambdas.

Verification:

- `SIMPLE_LIB=src bin/simple test test/01_unit/compiler/empty_array_map_lambda_spec.spl --mode=interpreter --clean --fail-fast`
- `SIMPLE_LIB=src bin/simple test test/01_unit/compiler/empty_array_map_lambda_spec.spl --mode=native --clean --force-rebuild --fail-fast`
