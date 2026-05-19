# Hex Literal Precision — State

**Status:** VERIFIED RESOLVED (no code change needed)
**Date:** 2026-05-19

## Summary

Bug `parser_64bit_hex_literal_precision_loss_2026-05-03.md` was already fixed in commit
`b72dc2aeaa` (2026-05-03). This task verified the fix is complete end-to-end.

## Fix Location

`src/compiler_rust/parser/src/lexer/numbers.rs` — `parse_integer_digits()`

When `NumericSuffix::U64` is present, the lexer now calls `u64::from_str_radix` directly
instead of going through the signed `i64` path first. The result is stored as `value as i64`
(bit-pattern preserved) tagged with `NumericSuffix::U64`.

## Downstream Paths Verified

| Path | File | Status |
|------|------|--------|
| Interpreter | `compiler/src/interpreter/expr/literals.rs` | Correct: `Value::UInt { value: *value as u64, width: 64 }` |
| HIR lowering | `compiler/src/hir/lower/expr/literals.rs` | Correct: emits `HirExprKind::Integer(*n)` with `TypeId::U64` |
| VHDL codegen | `compiler/src/pipeline/codegen.rs:526` | Not a precision path — `vhdl_generic_from_arg` only used for VHDL `natural` decorator defaults, not integer literals |

## Test Coverage

`test/unit/compiler/u64_hex_literal_precision_spec.spl` — 5 cases, all pass (exit 0):
- `0x8000000000000000u64` → bit 63 only
- `0xFFFFFFFFFFFFFFFFu64` → all-ones (max u64)
- `0xCAFEBABEDEADBEEFu64` → arbitrary 64-bit pattern
- SHA-512 IV (`0x6a09e667f3bcc908u64`)
- SHA-384 IV5 (`0xdb0c2e0d64f98fa7u64`, bit 63 set)

## No Code Change Made

The fix was already in place. A cosmetic commit is created per task requirements to record
this verification pass and create the state tracking file.
