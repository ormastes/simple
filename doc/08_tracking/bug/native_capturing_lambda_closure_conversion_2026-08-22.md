# Native path: capturing lambdas fail closure conversion (2026-08-22)

**Status:** FIXED (same day). **Lane:** `native-build` (pure-Simple MIR lowering).

## Symptom

```
val k = 5
val add_k = \v: v + k
add_k(10)            # MIR lowering error: undefined variable v
apply(\v: v + k, 10) # E-MIR-EXPR-Lambda: lambda expression (closure conversion has not run)
```

Both compile and run on the interpreter lane; both died on `native-build`.

## Root cause

The closure-conversion pass already existed in `50.mir/_MirLoweringExpr/switch_operators_calls.spl`
(`lower_lambda_value`: lift to `__lambda_lift_<n>`, captures copied BY VALUE into an
`rt_closure_new` env via `rt_closure_set_capture`, read back in the lifted body with
`rt_closure_get_capture`, called through the `rt_closure_func_ptr` diamond — the seed's
ABI from `closure_boxed_entry.rs`). But identifier resolution had moved to
`bind_local`/`find_local` (`local_symbol_ids`, commit 033d79338a1) while the whole lambda
machinery — capture snapshot, beta-reduced inline call, lift — still read/wrote the dead
`local_map`. Every capture lookup missed: the lift declined (nil → `E-MIR-EXPR-Lambda`),
and the inline path bound its params into a map nobody read (→ `undefined variable v`).

Two adjacent gaps surfaced by the fixture:
- a lambda literal in a non-Let, non-call-arg position (returned from a fn, struct field
  initializer, nested body) hit the unconditional `E-MIR-EXPR-Lambda` arm in `expr_dispatch.spl`;
- `h.f(4)` where `f` is a fn-typed struct FIELD fell to `unresolved method call: f`.

## Fix

- `switch_operators_calls.spl`: new `lambda_binding_local(sym)` (find_local first, legacy
  `local_map` fallback); snapshot, inline-call, and lift capture lookups use it; the
  inline/snapshot paths save/overlay/restore the `local_symbol_ids`/`local_symbol_values`
  pair instead of swapping `local_map`; lifted params bound via `bind_local`.
- `expr_dispatch.spl`: `Lambda` arm runs `lower_lambda_value` and only keeps the loud
  failure when the lift declines.
- `method_calls_literals.spl`: method-call on a known struct's fn-typed field re-dispatches
  as a call of the field value.

Capture semantics: BY VALUE at creation, matching the seed
(`var n = 5; val f = \x: x + n; n = 100; f(3)` → 8 on both lanes).

## Evidence

Fixture (6 shapes: capture val, var mutated after creation, lambda as arg, lambda returned,
nested capture, closure in struct field + `(h.f)(5)`): interpreter and native both print
`15 8 15 8 13 20 25` (native `print` drops newlines — separate bug
`native_build_print_drops_newline_2026-08-17`). Spec:
`test/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.spl`
(5 in-process MIR examples + 1 native dual-run example, `--threads 8`).

## Remainder

- `make_adder` (closure returned from fn) still falls back to the interpreter on the
  Cranelift JIT lane ("return slot boxes the handle") — JIT-only, not native-build.
- Linter cannot parse `describe "...", tag: [...]:` (PARSE001) — pre-existing, affects
  every spec using that form.
