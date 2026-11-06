# Pure core interpreter: `??` on Option values and `if x.?` presence diverge from the `.?` contract

- **Date**: 2026-11-06
- **Status**: open
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
