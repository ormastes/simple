/-
  GcBoundary.AliasCounterexample — Documented counterexample for alias-blindness.

  This module documents a concrete program that the real checker accepts but
  that violates T1's conclusion outside the alias-free fragment.

  Audit finding reference:
    doc/08_tracking/bug/gc_nogc_memory_audit_findings_2026-06-11.md
    § "Seed lint blind spots" — finding 4: "seed lint still alias-blind"

  THE COUNTEREXAMPLE
  ==================
  Simple program (pseudocode, nogc_async_mut.worker module):

      fn pass_gc_ref_directly(x: GcObject):
          use_in_nogc(x)   -- x.tier = gc; context.tier = nogc, no Copy

  The real checker sees NO import of gc_* families from this module, so
  check_gc_boundary_imports returns zero warnings.  The gc-allocated value
  flows through a *parameter* — invisible to import-edge scanning.

  In the formal model:
-/

import GcBoundary.Basic
import GcBoundary.Theorems

open GcBoundary

namespace GcBoundary.AliasCounterexample

/-- A variable x bound to a gc value in the environment. -/
def counterEnv : TierEnv := [(0, Tier.gc)]

/-- The expression: bare Var(0), gc-typed, no Copy wrapper. -/
def aliasExpr : Expr := Expr.Var 0

/-- `aliasExpr` is NOT alias-free: it is a gc-tier Var without a Copy. -/
theorem aliasExpr_not_alias_free : ¬ AliasFree counterEnv aliasExpr := by
  simp [AliasFree, aliasExpr, TierEnv.lookup, counterEnv]

/-- `aliasExpr` has tier gc in counterEnv. -/
theorem aliasExpr_has_tier_gc (fc : FnCtx) :
    HasTier fc counterEnv aliasExpr Tier.gc := by
  apply HasTier.var
  simp [TierEnv.lookup, counterEnv]

/-- The structural noalloc body walk does not reject a bare variable alias. -/
theorem aliasExpr_noalloc_body_ok (fc : FnCtx) :
    noallocBodyOk fc aliasExpr := by
  simp [noallocBodyOk, aliasExpr]

/-
  KEY FINDING:
  The real checker would accept a nogc_async_mut.worker module containing
  `pass_gc_ref_directly(x)` because:
    1. The module imports no gc_* family directly.
    2. GC_ALIAS_MANIFEST covers module-path aliases (e.g. std.gpu → gc_async_mut),
       NOT parameter-passing of gc-typed values through function arguments.
    3. The checker's import-edge scan is blind to value-level aliasing.

  Therefore T1 (check_sound_wrt_model) applies ONLY in the alias-free
  fragment.  `aliasExpr` above lies outside that fragment:
  - `aliasExpr_has_tier_gc` shows it types as gc.
  - `aliasExpr_not_alias_free` shows it is outside AliasFree.
  - T1's hypotheses require AliasFree, so the theorem does not apply.
  - The real checker would accept this expression (no import violation).

  Remediation (open, per audit findings):
    A value-flow / points-to analysis is required to close this gap.
    Tracked as HIGH finding in gc_nogc_memory_audit_findings_2026-06-11.md.
-/

end GcBoundary.AliasCounterexample
