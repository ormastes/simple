# MIR: `if val v = f64_opt` numerically casts the raw payload word and folds `v != nil` (2026-11-06)

**Status:** fix-implemented-verification-pending (closes when a Stage 2 `compiler_cli_build` row passes)

## Symptom
`build/probe/p3.spl` (`fn parse_opt(s) -> f64?: return parse_plain(s)` where parse_plain
returns 2.25; `if val v = parse_opt("x"): print(v)`) printed `4612248968380809216.0` — the
IEEE-754 bits of 2.25 converted as an integer — on the run-11 Stage 2.

## Root cause
`if val v = e` desugars to `val v = e.?` + `v != nil`. The ExistsCheck arm
(`_MirLoweringExpr/expr_dispatch.spl` ~7060) deliberately yields a raw payload-or-nil word in
an i64 slot with HIR type Float, and `lower_if` decodes it by bitcast on the present edge
(`has_if_val_scalar_binding`, `mir_lowering_stmts.spl` ~3780). When the binder had a typed
`let_type` (f64, because the callee's return type is known), the Let lowering
(`mir_lowering_stmts.spl` ~1411, `annotated_float`) emitted a numeric `Cast(word -> F64)` and
typed the binder F64; `nil_compare_operand_is_plain_scalar` then folded `v != nil` to true and
the present-edge decode never fired.

## Fix
- Let lowering: an ExistsCheck initializer whose I64 word carries HIR Float/Bool skips the
  annotated cast and keeps the binding I64.
- `nil_compare_operand_is_plain_scalar`: a Float/Bool HIR value in an I64/U64 slot is a raw
  word that may be nil, so the compare is not folded.

## Evidence
Spec case "if-val f64 binder": red (1 float Cast, 0 Bitcast) -> green (0 Cast, 1 Bitcast; MIR
shows `Ne word, 3` then `Bitcast F64` on the present edge). p3 native on run-11 (7daae128…): `4612248968380809216.0`; see green below.

Fixed Stage 2 built from commit 46f26dec9d6 (sha256 773a9ee4f2f6af44…, seed native-build of bootstrap_main.spl): chart.spl compiles with 0 AOT errors (link stops only on `__simple_main`, chart.spl has no main); p1 prints `2.5`; p3 prints `2.25`; pb prints `2.5`.
Review follow-up a9b2178923b (nil-compare fold keyed on ExistsCheck provenance), Stage 2 8fd94bdcb4c53977…: chart.spl, p1 `2.5`, p3 `2.25`, pb `2.5`, p4 nil-returning `f64?` prints `f64 none` (run-11 printed `f64 present 3.0`); parser_cli.spl and simple_ring.spl show the same output as run-11 (no new MIR/verifier/ABI errors). Spec 10/10.
