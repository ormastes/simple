# Specs blocked on a compiler deploy

These specs encode fixes that are correct in SOURCE but cannot pass with the
currently deployed `bin/simple` (which IS the Rust seed; bootstrap Stage 3 is
blocked, so no rebuilt compiler can be deployed). Each was proven to pass
against a locally-built binary carrying its fix.

They are **committed on purpose**, with a `BLOCKED ON DEPLOY` header as line 1:
- The rule "never skip a failing test without approval" forbids weakening them.
- Untracked is not safe here — an untracked spec vanished from this shared
  worktree on 2026-08-18 (concurrent-session cleanup). Committed evidence
  survives; untracked evidence does not.
- A visible red is the honest signal that deploy debt exists.

| spec | fix commit | proves |
|---|---|---|
| `test/01_unit/lib/common/interpreter_float_division_by_zero_ieee_spec.spl` | `2860e458cee` | float `0.0/0.0`→NaN, `x/0.0`→±inf (IEEE-754); integer div-by-zero still raises |
| `test/01_unit/app/cli/jit_bare_assign_local_minting_spec.spl` | `a606976737f` | bare assignment to an unbound identifier mints a mutable local |

## On deploy

When a compiler carrying these fixes is finally deployed:
1. Run both specs; each must go green with no edit. If one still fails, the fix
   did not survive — treat as a regression, do not adjust the spec.
2. Delete the `BLOCKED ON DEPLOY` headers and this row.
3. Simplify `src/lib/common/numeric_round.spl`'s NaN-construction workaround
   back to `0.0/0.0` (noted in
   `interpreter_float_division_by_zero_raises_instead_of_nan_2026-08-18.md`).
4. Re-check `doc/08_tracking/bug/jit_module_val_array_indexing_15x_slow*.md` —
   the module-val array fixes wait on the same deploy.
