# Pure core interpreter: `??` on Option values and `if x.?` presence diverge from the `.?` contract

- **Date**: 2026-11-06
- **Status**: fixed (work/interp-p2-dotq; pure side verified, source-run)
- **Area**: src/compiler/10.frontend/core/interpreter (pure-Simple core interpreter)

## Repro (`core_interpret` with `enum Option<T>` / `enum Result<T, E>` declared)
- `Option.None ?? 7` returns the `Option::None(...)` struct, not 7 (`eval_null_coalesce` only tests `val_is_nil`
  / a `__tag` field; constructed variants carry a struct name `Option::None`).
- `if Option.Some(0).?:` takes the else branch: the if condition re-reads payload truthiness (`val_is_truthy(0)`),
  while the guide says `if x.?` is presence.
- `Result.Ok(1).?` returns the Ok struct (`eval_option_binding_value` unwraps only `Option::*`).
- builtin `Some(x)` / `Ok(x)` are `undefined function` (no prelude); only the qualified forms resolve.

Found while building test/01_unit/compiler/interpreter/dotq_cross_engine_parity_spec.spl, which therefore compares
only the `.?` value renderings the core interpreter implements.

## Fix (work/interp-p2-dotq, 2026-11-06)
- `eval.spl` `eval_option_binding_value`: `Result::Ok(x)` unwraps to x, `Result::Err(_)` is absent (nil).
- `eval.spl` `eval_control_condition`: a bare `.?` condition is presence (`not val_is_nil`), so `if Option.Some(0).?:` is taken.
- `eval_null_coalesce` in BOTH `eval_access.spl` and `_EvalOps/access_literal_assign_eval.spl` (the latter wins the
  co-compiled name collision): constructed `Option::*` / `Result::*` structs unwrap via `eval_option_binding_value`;
  None/Err/nil payload take the fallback.
- Spec: new describe block in `test/01_unit/compiler/interpreter/dotq_cross_engine_parity_spec.spl` (pure side green on
  the deployed seed; the seed-side `Some(nil) ?? 7` cases need the #7140 seed fix deployed).
- Not changed: builtin unqualified `Some(x)` / `Ok(x)` in the core interpreter (no prelude) — out of scope.
