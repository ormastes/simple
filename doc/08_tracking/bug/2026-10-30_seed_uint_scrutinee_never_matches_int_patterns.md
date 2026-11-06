# Seed: a UInt value never matches integer literal or range patterns

- Status: FIXED 2026-11-06 (branch `work/seed-interp-correctness-20261106`) — see "Resolution" below
- Component: Rust seed interpreter, `src/compiler_rust/compiler/src/interpreter_patterns.rs` (~200-205, ~549-551)
- Found by: Fable review of PR #5370 (`to_u64()` now yields `Value::UInt`)

## Symptom

Integer literal and range pattern arms return `false` unless the scrutinee is
`Value::Int`. With PR #5370 an untyped `val u = x.to_u64()` is `Value::UInt`, so

```
match u:
    case 0: ...
    case 1..=9: ...
    case _: ...
```

silently takes `_`. A typed `val u: u64` binding was already `UInt` and already
had this gap. No `match <expr>.to_u64()` site exists in `src/` today.

Related gaps from the same review:
- A `UInt` argument bound to an `i64` parameter stays `UInt`
  (`interpreter_call/core/arg_binding.rs` ~250-275 only coerces toward u*).
- `to_u64()` on Float/Float32 receivers still returns `Value::Int`
  (`method_dispatch.rs` Float arms, `primitives.rs` ~281), while HIR types the
  result as U64 for any receiver.

## Unblock / fix

Compare literal and range patterns numerically for `UInt` (value fits i64, or
pattern literal is non-negative), and return `UInt { width: 64 }` from the
Float `to_u64` arms.

## Resolution (2026-11-06)

- `interpreter_patterns.rs` `Pattern::Range` accepted only `Value::Int`; it now
  compares an `Int` or `UInt` scrutinee against the bounds in i128, so
  `u: u64` takes `case 1..=9`. The literal arm (partially fixed in
  `06c37c33347` by a bit-pattern compare, which made `case -1` match
  `u64::MAX`) now compares a `UInt` by numeric value: a negative literal never
  matches, and a `u64`-suffixed literal above i64::MAX (lexed as its bit
  pattern) is read back as unsigned (`int_pattern_bound`). `Int` scrutinees
  keep the historical i64 comparison.
- `to_u64()` on `Float`/`Float32` receivers now returns `UInt { width: 64 }`
  (`interpreter_helpers/method_dispatch.rs`, `interpreter_method/primitives.rs`).
- Not addressed here: the `UInt` argument bound to an `i64` parameter
  (`arg_binding.rs`) — still open as a related gap.

Evidence:
- Repro `test/fixtures/seed_interp/uint_scrutinee_int_pattern_repro.spl`,
  interpreter mode. Before (seed `bin/simple.exe`, v1.0.0-beta.11, 2026-10-05):
  `uint_match other other other other`. After (seed built from this branch):
  `uint_match zero digit small other` — identical to JIT mode.
- Rust tests `interpreter_patterns::tests::uint_scrutinee_matches_int_range_patterns_by_value`,
  `uint_scrutinee_never_matches_a_negative_int_literal`,
  `uint_match_end_to_end_takes_the_right_arm`: FAILED before (e.g. end-to-end
  `left: 4441, right: 4321`), ok after.

## Follow-up resolved (2026-11-06): UInt argument bound to an `i64` parameter

`interpreter/node_exec.rs` `coerce_to_declared_signed` (called from
`coerce_to_declared_type`, which both `arg_binding.rs` binders and typed
`val`/`var` bindings use) converts a `Value::UInt` bound to a declared
`i64` to `Value::Int` (bit pattern, as native stores it).

Evidence: `test/fixtures/seed_interp/uint_arg_to_i64_param_repro.spl`,
interpreter mode. Before (seed built from `ecb705896a4`):
`uint_to_i64 18446744073709551611 false`. After: `uint_to_i64 -5 true`,
identical to JIT. Rust test
`interpreter::node_exec::declared_signed_binding_tests::uint_argument_bound_to_i64_param_is_signed`:
FAILED before (`left: 0, right: 1`), ok after.

## Amended (2026-11-06): 64-bit scrutinee vs over-i64::MAX literals

"A negative literal never matches" made `case 0x8000000000000000` dead for a
`u64` (the lexer stores it as i64::MIN, indistinguishable from `case -N`).
For a 64-bit `UInt` scrutinee an unsuffixed negative literal now compares by
bit pattern, like JIT/native; narrower widths keep the rule. See
`seed_interp_u64_high_bit_literal_pattern_2026-11-06.md`.
