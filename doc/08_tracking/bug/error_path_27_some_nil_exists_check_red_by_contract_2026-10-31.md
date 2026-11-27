# error_path scenario 27 (`Some(nil).?`) is RED in all 100 error_path specs

Status: fixed 2026-11-06 (owner decision; see Resolution)
**Found:** 2026-10-31 (relfix-errpath lane)

## Symptom
Every `test/03_system/core/error_path/error_path_<N>_system_spec.spl` (N=1..100) fails exactly one of 30 examples: "error path 27 - option chain breaks" (`val opt = Some(nil); verify(opt.?)` -> "expected false to equal true"). The other 29 pass on the Rust seed. Before: 0/100 specs green; after: unchanged (no fix applied).

## Cause
Not a spec staleness. The spec header declares scenario 27 RED by contract: `Some(nil).?` is falsy on the runtime. Seed repro: `val a = Some(nil); print "{a.?}"` prints `nil` (`Some(1).?` prints `1`, `Some(false).?` prints `false`), i.e. `.?` returns the payload per the ratified `T?` contract (see exists_check_on_optional_i64_returns_payload_2026-08-01.md), so a nil payload is indistinguishable from absence.

## Why not fixed here
Fixing needs a semantic decision (presence vs payload for `.?` on a wrapped Some) in the interpreter, which lives in src/compiler_rust (off limits). Weakening or removing the scenario is forbidden. Resolve by either changing `.?` semantics for `Some(nil)` or ratifying the contract and rewriting the oracle in all 100 specs (owner decision).

## Owner decision (2026-11-06)
Owner decision, 2026-11-06: "`.?` in the Rust seed interpreter must behave exactly like pure Simple."

## Root cause (2026-11-06, work/seed-try-op-parity)
`.?` itself was never divergent. Both engines evaluate `Some(nil).?` to nil:
- pure Simple core interpreter: `src/compiler/10.frontend/core/interpreter/eval.spl` `EXPR_EXISTS_CHECK`
  (`eval_option_binding_value` unwraps `Option::Some` to its payload, `val_exists(nil)` is false -> nil);
- pure Simple MIR: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` `case ExistsCheck` (payload-or-nil word;
  a nil payload is the nil word itself);
- seed: `src/compiler_rust/compiler/src/interpreter/expr.rs` `Expr::ExistsCheck` (payload, nil payload -> `Value::Nil`).

Since nil is only ever `T?` absence, `Some(nil)` is absence. Scenario 27's oracle `verify(opt.?)` asserted the opposite
of what both engines (and the contract) do. The real seed gap was its neighbour `??`: the seed interpreter's
`Expr::Coalesce` yielded the nil payload of `Some(nil)` / `Ok(nil)` instead of the default, while pure Simple takes the
default exactly when `.?` is absent.

## Resolution
- Seed `Expr::Coalesce` falls back to the default for a nil payload (`Some(nil) ?? 7 == 7`, `Ok(nil) ?? 7 == 7`).
- Scenario 27 oracle rewritten to the ratified contract in all 100 specs: `verify(opt.? == nil)` ("option chain breaks").
- Cross-engine parity spec: `test/01_unit/compiler/interpreter/dotq_cross_engine_parity_spec.spl` runs each `.?` case
  on the seed interpreter and on the pure-Simple core interpreter and requires identical renderings; it also pins
  `??`/`.?` agreement. RED before the fix (4 of 15 failed: the `Some(nil)`/`Ok(nil)` `??` cases), GREEN after.

## Not fixed here (filed)
- Seed JIT (default `run` engine for programs with `main`): `Some(nil) ?? 7` prints `3` (raw nil sentinel),
  `if Err("e").?` is true, `not Some(0).?` is `true`. Filed as `seed_jit_dotq_coalesce_parity_2026-11-06`.
- Pure core interpreter: `Option.None ?? 7` returns the `Option::None` struct, `if Option.Some(0).?` is false (reads
  payload truthiness, guide says presence), `Result.Ok(1).?` does not unwrap. Filed as
  `core_interp_option_coalesce_and_presence_gaps_2026-11-06`.
