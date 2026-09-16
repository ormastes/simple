# Bootstrap dynamic receiver free-function theft (2026-08-15)

## Symptom

The fixed Rust seed reduced the `bootstrap_main.spl` diagnostic shard from
five callable-ABI failures to one. `HirVisitor.visit_expr` contains the valid
method-shaped expression `self.backend.eval_expr(expr, self.ctx)`, but the
cross-module fallback selected the unrelated free function
`compiler.frontend.core.interpreter.eval.eval_expr(eid)`.

## Root cause and fix

The local suffix candidate route rejected free functions, while the later
cross-module `use_map`/`import_map` route accepted them for explicit-receiver
syntax. The latter route now applies the same receiver-kind and receiver-aware
arity gate. It accepts only instance targets with space for `self` plus every
explicit argument and otherwise continues to the existing method-not-found
fallback. It never strips the receiver to make an unrelated free function fit.

Focused Rust coverage locks the exact two-argument `eval_expr` theft, a valid
dynamic instance method, and an undersized instance-method negative boundary.

The exact library filter ran one test and passed. Retained evidence:
`build/native_probe/stage4-dynamic-receiver-free-theft-focused-lib.log` and
`.status` (exit 0). Earlier package-wide exact-filter attempts that selected
zero tests are diagnostic-only and are not counted as verification.
