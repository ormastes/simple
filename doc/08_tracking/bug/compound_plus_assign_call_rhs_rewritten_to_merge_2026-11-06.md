# `t += f()` is rewritten to `t.merge(f())` before compiler lowering

- **Found:** 2026-11-06 while pinning assignment evaluation order (data plan W2a).
- **Where:** `src/compiler/10.frontend/desugar/collection_desugar.spl`, `try_rewrite_compound_assign`.
- **Symptom:** In the compiler path, the desugar treats every `+=` whose right-hand side is not a definite scalar addend as array concatenation. It rewrites `arr[i] += w2a_rhs(2)` into the method call `arr[i].merge(w2a_rhs(2))`. The pass has no type information, so an integer element is also given a `merge` call. Lowered MIR therefore evaluates the receiver index before the right-hand side (`i,rhs`), not RHS first as owner decision 2026-11-06 (option b) requires.
- **Not affected:**
  - `-=`, `*=`, `/=`, `%=`; `test/01_unit/compiler/mir/assign_eval_order_lowering_spec.spl` uses those.
  - The seed and pure-Simple interpreters, which never run this desugar.
- **Fix direction:** Rewrite to `merge` only when the target is known to be an array. That needs typed HIR, so the right fix is to move the rewrite after type resolution. Until then, restrict it to identifier targets whose declaration is an array literal.
- **Repro:** Lower `fn main(): var arr = [0, 0]; arr[w2a_i(0)] += w2a_rhs(2)`. The order spec's `lowered_order` helper does this, and `main`'s MIR shows a `merge` call.

## Resolution (2026-11-06)

- **Root cause:** `try_rewrite_compound_assign` in `src/compiler/10.frontend/desugar/collection_desugar.spl` rewrote every `t += <non-literal>` into `t.merge(...)` with no type information. A second defect sat behind it: MIR lowered compound `+=` on locals and globals (`lower_assign_var`, `mir_lowering_stmts.spl`) and on fields/indices (`lower_compound_combine`) as an integer `add` for every type. `s += "b"` (a literal right-hand side, never rewritten) compiled to `add nsw i64` on two string handles. The merge rewrite had hidden this for non-literal right-hand sides.
- **Fix:** the desugar no longer rewrites `+=` to `merge`. The one-element `x += [item]` push rewrite stays, but only on places with no side effects. `lower_compound_combine` now classifies `+=` by operand type. A text operand uses `rt_strcat_tagged`. An array operand, or a right-hand side that is not a plain numeric, extends in place with `rt_array_extend_i64`; that is the rule the merge arm used, so `buf += more_bytes()` keeps working. A numeric right-hand side uses arithmetic, widened to f64 when either side is a float. The local and global compound paths now go through it.
- **Evidence:** `test/01_unit/compiler/mir/compound_plus_assign_call_rhs_spec.spl` went from RED (2 of 5 failed: rewrite count 1, and `add nsw i64` for text `+=`) to GREEN (5 of 5). `assign_eval_order_lowering_spec.spl` `+=` cases went from RED (`i,rhs`, `r,i,rhs`, `r,rhs`) to GREEN (`rhs,i`, `rhs,r,i`, `rhs,r`).
