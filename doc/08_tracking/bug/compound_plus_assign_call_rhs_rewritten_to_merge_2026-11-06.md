# `t += f()` is rewritten to `t.merge(f())` before compiler lowering

- **Found:** 2026-11-06 while pinning assignment evaluation order (data plan W2a).
- **Where:** `src/compiler/10.frontend/desugar/collection_desugar.spl`, `try_rewrite_compound_assign`.
- **Symptom:** In the compiler path, the desugar treats every `+=` whose right-hand side is not a definite scalar addend as array concatenation. It rewrites `arr[i] += w2a_rhs(2)` into the method call `arr[i].merge(w2a_rhs(2))`. The pass has no type information, so an integer element is also given a `merge` call. Lowered MIR therefore evaluates the receiver index before the right-hand side (`i,rhs`), not RHS first as owner decision 2026-11-06 (option b) requires.
- **Not affected:**
  - `-=`, `*=`, `/=`, `%=`; `test/01_unit/compiler/mir/assign_eval_order_lowering_spec.spl` uses those.
  - The seed and pure-Simple interpreters, which never run this desugar.
- **Fix direction:** Rewrite to `merge` only when the target is known to be an array. That needs typed HIR, so the right fix is to move the rewrite after type resolution. Until then, restrict it to identifier targets whose declaration is an array literal.
- **Repro:** Lower `fn main(): var arr = [0, 0]; arr[w2a_i(0)] += w2a_rhs(2)`. The order spec's `lowered_order` helper does this, and `main`'s MIR shows a `merge` call.
