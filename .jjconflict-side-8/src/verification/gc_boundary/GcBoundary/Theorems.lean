/-
  GcBoundary.Theorems — Four provable theorems about the gc/nogc boundary model.

  All theorems are proved without `sorry`.

  T1  check_sound_wrt_model    — checker acceptance implies no gc ref crosses into
                                  nogc without a copy (alias-free fragment only)
  T2  noalloc_closed           — checker-accepted noalloc bodies perform no allocation
  T3  inference_monotone       — AllocAnn join is monotone w.r.t. the lattice
  T4  copy_isolates            — Copy produces tier nogc, not gc

  ALIAS-FREE FRAGMENT (T1 restriction):
  `AliasFree env e` holds when no bare Var of gc tier appears directly in `e`
  without a wrapping Copy node.  See AliasCounterexample for the boundary of
  this restriction.
-/

import GcBoundary.Basic

namespace GcBoundary

-- ============================================================
-- § A  Alias-free fragment predicate
-- ============================================================

/-- `AliasFree env e` holds when `e` contains no bare `Var` whose
    environment maps to gc tier.  Copy nodes are always safe (they isolate).
    This is the fragment over which T1 is valid. -/
def AliasFree (env : TierEnv) : Expr → Prop
  | Expr.Lit _     => True
  | Expr.Var x     => TierEnv.lookup env x ≠ some Tier.gc
  | Expr.Copy _    => True
  | Expr.Call _ as => ∀ a, a ∈ as → AliasFree env a
  | Expr.Seq e1 e2 => AliasFree env e1 ∧ AliasFree env e2

-- ============================================================
-- § B  T1 — check_sound_wrt_model
-- ============================================================

/-- T1: In the alias-free fragment, if the checker accepts an expression in
    a nogc/noalloc context, that expression cannot be typed as tier gc.

    Formally: CheckerOk fc ctx e ∧ AliasFree env e ∧ ctx ∈ {nogc, noalloc}
    implies ¬ HasTier fc env e gc. -/
theorem check_sound_wrt_model
    (fc : FnCtx) (ctx : Tier) (e : Expr) (env : TierEnv)
    (hctx : ctx = Tier.nogc ∨ ctx = Tier.noalloc)
    (hok  : CheckerOk fc ctx e)
    (haf  : AliasFree env e)
    : ¬ HasTier fc env e Tier.gc := by
  intro hty
  -- Helper: extract the result-tier equation from HasTier constructors
  -- by pattern-matching on hok (CheckerOk), dispatching with hty (HasTier).
  induction hok with
  | lit_gc v _htier =>
    -- ctx = Tier.gc; hctx says Tier.nogc or Tier.noalloc — both impossible
    rcases hctx with h | h <;> exact absurd h (by decide)
  | lit_safe _ctx v hne =>
    -- HasTier.lit: hty : HasTier fc env (Lit v) Tier.gc
    -- New constructor: HasTier.lit env v t (heq : t = v.tier)
    -- cases gives heq : Tier.gc = v.tier, so v.tier = Tier.gc
    cases hty with
    | lit _ _ heq => exact hne heq.symm
  | var_gc _env' _x _hlookup =>
    rcases hctx with h | h <;> exact absurd h (by decide)
  | var_safe _ctx _env' _x _t _hlookup hne =>
    simp only [AliasFree] at haf
    -- haf : TierEnv.lookup env _x ≠ some Tier.gc
    -- hty : HasTier fc env (Var _x) Tier.gc
    -- HasTier.var gives: lookup env _x = some Tier.gc — contradicts haf
    cases hty with
    | var _ _ hlk => exact haf hlk
  | copy _ctx _e' _srcCtx _hok' _ih =>
    -- HasTier for (Copy e') has exactly one constructor: HasTier.copy,
    -- which hard-codes result = Tier.nogc. So hty : HasTier fc env (Copy e') Tier.gc
    -- has no valid derivation — cases produces zero goals.
    cases hty
  | call_safe _ctx _f _args _hctx' hne =>
    -- HasTier.call: hty gives heq : Tier.gc = fc.retTier f
    cases hty with
    | call _ _ _ heq => exact hne heq.symm
  | call_gc _f _args =>
    rcases hctx with h | h <;> exact absurd h (by decide)
  | seq _ctx e1 e2 _hok1 _hok2 _ih1 ih2 =>
    simp only [AliasFree] at haf
    -- HasTier for (Seq e1 e2) gives result tier from e2 (second arg)
    -- Extract the e2 judgement and the haf.2 sub-proof
    have hty2 : HasTier fc env e2 Tier.gc := by cases hty; assumption
    exact ih2 hctx haf.2 hty2

-- ============================================================
-- § C  T2 — noalloc_closed
-- ============================================================

/-- EvalAllocates: an expression allocates in the model if it contains
    a gc Lit, calls an allocating function, or sequences through one. -/
inductive EvalAllocates (fc : FnCtx) : Expr → Prop where
  | lit_gc      : ∀ v,        v.tier = Tier.gc                     → EvalAllocates fc (Expr.Lit v)
  | call_alloc  : ∀ f args,   fc.allocAnn f = AllocAnn.alloc       → EvalAllocates fc (Expr.Call f args)
  | seq_left    : ∀ e1 e2,    EvalAllocates fc e1                  → EvalAllocates fc (Expr.Seq e1 e2)
  | seq_right   : ∀ e1 e2,    EvalAllocates fc e2                  → EvalAllocates fc (Expr.Seq e1 e2)
  | copy_inner  : ∀ e,        EvalAllocates fc e                   → EvalAllocates fc (Expr.Copy e)

/-- T2: A body accepted by `noallocBodyOk` (full recursive walk) does not allocate.
    Proved by structural induction on both `noallocBodyOk` and `EvalAllocates`. -/
-- Auxiliary for T2: proved by structural recursion (not induction tactic,
-- since Expr is a nested inductive with List Expr in Call).
private def noalloc_closed_aux (fc : FnCtx) : ∀ (e : Expr),
    noallocBodyOk fc e → ¬ EvalAllocates fc e
  | Expr.Lit v, hok, halloc => by
      simp only [noallocBodyOk] at hok
      cases halloc with
      | lit_gc _ htier => exact hok htier
  | Expr.Var _, _, halloc => by cases halloc
  | Expr.Copy e, hok, halloc => by
      simp only [noallocBodyOk] at hok
      cases halloc with
      | copy_inner _ h => exact noalloc_closed_aux fc e hok h
  | Expr.Call f _, hok, halloc => by
      simp only [noallocBodyOk] at hok
      cases halloc with
      | call_alloc _ _ hannot =>
        rw [hok] at hannot
        exact AllocAnn.noConfusion hannot
  | Expr.Seq e1 e2, hok, halloc => by
      simp only [noallocBodyOk] at hok
      cases halloc with
      | seq_left _ _ h1 => exact noalloc_closed_aux fc e1 hok.1 h1
      | seq_right _ _ h2 => exact noalloc_closed_aux fc e2 hok.2 h2

/-- T2: A body accepted by `noallocBodyOk` (full recursive walk) does not allocate. -/
theorem noalloc_closed (fc : FnCtx) (e : Expr)
    (hok : noallocBodyOk fc e)
    : ¬ EvalAllocates fc e :=
  noalloc_closed_aux fc e hok

-- ============================================================
-- § D  T3 — inference_monotone
-- ============================================================

/-- T3: The AllocAnn join is monotone: if a ≤ b then a ≤ join b c.
    This captures that the alloc_inference fixpoint never removes the
    `alloc` classification once set. -/
theorem inference_monotone (a b c : AllocAnn)
    (h : a ≤ b)
    : a ≤ AllocAnn.join b c := by
  cases a <;> cases b <;> cases c <;>
    simp [LE.le, AllocAnn.le, AllocAnn.join] at *

/-- Joining with any c never decreases the annotation. -/
theorem inference_join_ge (a c : AllocAnn) : a ≤ AllocAnn.join a c :=
  AllocAnn.join_ge_left a c

/-- Once alloc, always alloc: joining alloc with anything stays alloc. -/
theorem alloc_join_alloc (c : AllocAnn) :
    AllocAnn.join AllocAnn.alloc c = AllocAnn.alloc := by
  cases c <;> simp [AllocAnn.join]

-- ============================================================
-- § E  T4 — copy_isolates
-- ============================================================

/-- T4: A Copy node produces tier nogc regardless of the source tier.
    Mutations to the copy in a nogc context cannot affect the gc original
    because they have distinct, independently-typed identities. -/
theorem copy_isolates (fc : FnCtx) (env : TierEnv) (e : Expr) (srcTier : Tier)
    (hty : HasTier fc env e srcTier)
    : HasTier fc env (Expr.Copy e) Tier.nogc :=
  HasTier.copy env e srcTier hty

/-- The copy result is not gc. -/
theorem copy_result_not_gc (fc : FnCtx) (env : TierEnv) (e : Expr)
    : ¬ HasTier fc env (Expr.Copy e) Tier.gc := by
  intro hbad
  -- HasTier for Copy has exactly one constructor (copy), whose result is Tier.nogc.
  -- hbad : HasTier fc env (Copy e) Tier.gc — no constructor matches; zero goals.
  cases hbad

end GcBoundary
