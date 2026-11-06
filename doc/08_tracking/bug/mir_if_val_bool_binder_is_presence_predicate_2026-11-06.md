# MIR: `if val v = bool_opt` binds the presence predicate, not the payload (2026-11-06)

**Status:** open (found by review of the f64 if-val fix; pre-existing, not fixed)

## Symptom
`build/probe/p4.spl`, both on run-11 Stage 2 (7daae128…) and on the fixed Stage 2
(8fd94bdc…, commit a9b2178923b):

    fn flag_opt(b: bool) -> bool?:  if b: return false  /  nil
    if val w = flag_opt(true): print("bool present {w}")   -> "bool present true"  (payload is false)
    if val x = flag_opt(false): ... else: print("bool none") -> "bool wrongly present false"

## Mechanism (from MIR dump)
`if val v = e` desugars to `val v = e.?` + `v != nil`. The binder's inferred let type is `bool`,
and `lower_expr_for_slot` (`src/compiler/50.mir/mir_lowering_stmts.spl` ~2700) lowers
`.?` into a declared `bool` slot as the PRESENCE predicate (`rt_is_some`), the rule added by
stage2_dotq_presence_value_is_nil_sentinel_2026-11-03 for `val hm: bool = mp.?`. The binder is
then a plain bool, `v != nil` folds to `true`, and the branch is always taken with v = presence.
HIR does not distinguish an explicit `: bool` annotation from the inferred binder type, so the
two cases need a desugar marker (e.g. on the parser's if-val Let) to separate.
