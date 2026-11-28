# mir::lower: three unit tests red on release/1.0.0 (HIR changes outran MIR code/tests)

Status: verification-pending
Date: 2026-11-28
Branch: work/mir-lower-tests-20261128

All three failed on the base `1159f031628` (`cargo test -p simple-compiler --lib mir::lower`: 662 passed, 3 failed).

## 1. annotated_f64_binding_from_int_literal_is_float_const — CODE bug (fixed)

Introduced by e0767613532 (P3 sweep waves 6-7): HIR now wraps an explicitly annotated
numeric `val` whose initializer type differs in `Cast { target: declared }`, so
`val y: f64 = 3` reaches MIR as `Cast(Integer 3)`. `float_slot_from_int_literal`
(c74e9904595) only recognised a bare `Integer`/`-Integer`, so it lowered `ConstInt 3`
plus a runtime `Cast` instead of `ConstFloat 3.0`. Fix: `float_slot_from_int_literal`
sees through a `Cast` to the declared type. Tests added: `-3` into f64, `5` into f32.

## 2. generic_fn_result_into_i64_param_is_unboxed — TEST stale (fixed)

a30fee1a6db / 2cca2ea9b06 made HIR decode a generic call result (`double_it(id(7))`)
with `any -> i64` cast, lowered to `Call rt_any_cast_int` (+ identity `Cast`), not an
`UnboxInt` instruction. The behaviour is correct (tagged word is decoded before the
i64 param); the helper `call_arg_is_unboxed_int` only looked for `UnboxInt`. Helper now
accepts `rt_any_cast_int` results (and identity casts of them).

## 3. bdd_skip_count::skip_statement_counts_and_keeps_call — TEST wrong (fixed)

The fixture declared `fn skip` itself. Since seed_same_name_fn_binding_2026-11-27
(form 2) a DSL name the module declares is that module's own function and is
deliberately NOT counted via `rt_bdd_note_skip`. The fixture now supplies `skip` via
`extern fn` (stand-in for the std.spec import); a second test pins that a
module-declared `skip` is an ordinary, uncounted call.

## Prevention
Tests 2 and 3 pinned an implementation detail instead of the contract; both now assert
the contract (tagged value decoded; framework skip counted, own skip not).
