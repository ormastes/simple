# Native MIR: lambdas / enum == / close,is_open block llm_caret cs_main

Status: FIXED-ON-ORIGIN (verified 2026-11-05, mirp2-B); bug_db row still `open` pending a hand-merged row update + .csm reseal.

## Original symptom (2026-10-19)
`native-build --entry src/app/llm_caret/cs_main.spl` hit E-MIR-EXPR-Lambda x21
(`nogc_async_mut/io/buffer.spl`), missing `__eq__` for enum-like `==`, and
unresolved `close`/`is_open`.

## Premise check 2026-11-05 (origin/release/1.0.0)
- `expr_dispatch.spl` `case Lambda` now runs `lower_lambda_value` (lift to
  `__lambda_lift_<n>` + `rt_closure_new` env) in every value position; only an
  unliftable capture shape keeps the loud E-MIR-EXPR-Lambda.
- `buffer.spl` no longer contains the lambdas (rewritten in 515f96e824e /
  290304c37e0) and now defines `close()`/`is_open()` via `closer`.
- Native repro with a copy of `s3_fable44.exe` (s3sanity recipe, LLVM, win-gnu):
  `test/s3sanity/mirp2b_lam.spl` (captured lambda local, lambda arg, fn-ref arg,
  lambda returned from fn, lambda in struct field, fn ref local, unit enum ==/!=)
  -> `rc=0 stdout=[a=6|b=11|c=8|d=101|e=15|f=42|g=eq|h=ne]`, all correct.
- Regression lock: `test/01_unit/language/closure_value_positions_spec.spl` (7/7).

## Remaining
Full `cs_main` native build not re-run this session (277 s / 3.4 GB); do that
before flipping the bug_db row to closed.
