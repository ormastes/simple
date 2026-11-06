# Seed interpreter: `case 0x8000000000000000` never matches a `u64`

- **Status:** FIXED 2026-11-06 (branch `work/seed-interp-batch2-20261106`)
- **Found:** 2026-11-06 by the seed JIT lane (JIT is correct).
- **Engine:** Rust seed tree-walk interpreter, `interpreter_patterns.rs`.

## Symptom

```
fn classify(u: u64) -> text:
    match u:
        case 0x8000000000000000: "sign"
        case _: "other"
```

`classify(0x8000000000000000)` returns `"other"` under
`SIMPLE_EXECUTION_MODE=interpret`, `"sign"` under JIT.

## Root cause

The lexer stores an unsuffixed integer literal above i64::MAX as its i64 bit
pattern (`parser/src/lexer/numbers.rs` `parse_integer_digits`), so the arm
is `Expr::Integer(i64::MIN)`. The 2026-10-30 fix
(`2026-10-30_seed_uint_scrutinee_never_matches_int_patterns.md`) compared a
`Value::UInt` against literals by numeric value so that `case -1` would not
match `u64::MAX`; that made every over-i64::MAX unsuffixed literal a
"negative" that can never match. In the AST the two spellings are the same
`Expr::Integer(-n)`.

## Resolution

`interpreter_patterns.rs` `Pattern::Literal`: against a 64-bit `Value::UInt`
scrutinee, a negative unsuffixed literal compares by 64-bit pattern, as
JIT/native do. Narrower unsigned scrutinees (`u8`/`u16`/`u32`) still never
match a negative literal; `u64`-suffixed literals and range patterns are
unchanged. Consequence, stated: `case -1` against a `u64` now matches
`u64::MAX`, which is also what the compiled lanes do.

Evidence: `test/fixtures/seed_interp/u64_high_bit_literal_pattern_repro.spl`,
interpreter mode. Before (this branch before the fix, and base
`ecb705896a4`): `u64_high_bit other other`. After: `u64_high_bit sign other`
(JIT: `sign other`). Rust test
`interpreter_patterns::tests::u64_scrutinee_matches_an_over_i64_max_unsuffixed_literal`:
FAILED before, ok after; `uint_scrutinee_never_matches_a_negative_int_literal`
now pins the negative-never-matches rule on a `u8` scrutinee.
