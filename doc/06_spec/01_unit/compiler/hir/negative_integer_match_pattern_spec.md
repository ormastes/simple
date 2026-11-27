# Negative integer match patterns fold to integer literals

Requirement: none standalone — regression for
`negative_integer_match_arms_native_2026-09-30`.
Executable source: test/01_unit/compiler/hir/negative_integer_match_pattern_spec.spl.
Five scenarios, zero placeholders.

| Scenario | Fixture | Expected result |
|---|---|---|
| Unary minus over literal | `Unary(Neg, IntLit(n))` for several n | folds to `IntLit(-n)`, type retained |
| Type preservation | folded `-7` arm | keeps `Int(64, signed)` type |
| i64 minimum | `-(-9223372036854775808)` | left unfolded (no positive counterpart) |
| Non-literal operand | `Unary(Neg, BoolLit(true))` | left unfolded |
| Cast parity | `Cast(IntLit(255), Int(8, signed))` | still normalizes to `IntLit(-1)` |

`case -1:` / `case -2:` over an integer scrutinee parse as a unary-minus
expression in pattern position; the flat bridge (convert_nodes.spl
`EXPR_UNARY` arm) preserves it as `PatternKind.Literal(Unary(Neg, IntLit))`.
Before this fold, MIR scalar match dispatch saw a `Literal(non-IntLit)` and
rejected the entire match, so no native code was ever produced for programs
with negative integer arms. `hir_normalize_integer_pattern_literal` now folds
`Unary(Neg, IntLit(n))` into `IntLit(-n)` with the operand type, so the
existing IntLit dispatch path accepts the arm. The i64 minimum is left
unfolded and fails at the ordinary unsupported-pattern diagnostic rather than
overflowing. Non-literal negation and the pre-existing integer-cast
normalization are unchanged.

Reproduce with the admitted self-hosted runtime once deployed:

```bash
bin/simple test test/01_unit/compiler/hir/negative_integer_match_pattern_spec.spl --mode=interpreter
```

Current-session evidence (Rust seed interpreter, aarch64 Linux host):
`outcome=OK declared>=5 executed=5 passed=5 failed=0 skipped=0 dropped=0`.
Neighbor `suffixed_integer_pattern_spec.spl` re-run: 5/5 (unchanged).
