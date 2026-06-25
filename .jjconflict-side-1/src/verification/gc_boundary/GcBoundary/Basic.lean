/-
  GcBoundary.Basic — Memory-tier model for the Simple gc/nogc boundary checker.

  Source of truth:
    src/compiler/00.common/gc_boundary.spl
    src/compiler/35.semantics/gc_boundary_check.spl
    src/compiler/35.semantics/noalloc_checker.spl
    src/compiler/10.frontend/core/alloc_inference.spl

  Design notes
  ============
  The real checker works at **module-family granularity**: each module belongs to
  a family (gc_async_mut, nogc_async_mut, nogc_async_mut_noalloc, common) and
  the checker flags imports that cross from a lower-capability context into a
  higher-capability one.  The alloc_inference pass additionally classifies
  individual *functions* as allocating/non-allocating via fixpoint over the call
  graph, and the noalloc_checker rejects annotated functions whose call graph
  reaches any allocation site.

  This model abstracts the module-family check as a **memory tier** on values and
  contexts, and the function-level alloc classification as a **Bool** annotation
  on function nodes in a small expression language.

  ALIAS-BLINDNESS NOTE (axiom-free comment, not a theorem):
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  The real checker is alias-blind at the *value* level.  It checks import edges
  between modules/families, not whether a gc-allocated value flows through a
  variable or field into a nogc context at runtime.  The GC_ALIAS_MANIFEST in
  gc_boundary_check.spl partially mitigates *module-path* aliasing (e.g.
  std.gpu → gc_async_mut) but does NOT track value aliases such as:

      val x : GcRef = gc_alloc()   -- in gc module
      pass_to_nogc(x)              -- x is a direct reference, not a copy

  The checker accepts this program (no module-family violation); the model's T1
  theorem is therefore restricted to an **alias-free fragment** where no variable
  is bound to a gc-allocated value in a nogc/noalloc context without an explicit
  copy node.  A concrete counterexample outside this fragment is documented in
  `GcBoundary.AliasCounterexample`.
-/

namespace GcBoundary

-- ============================================================
-- § 1  Memory tiers
-- ============================================================

/-- Three memory capability tiers, ordered by allocation freedom.
    - `gc`      : may allocate; GC (currently: allocate-and-leak) manages lifetimes.
    - `nogc`    : no GC involvement; manual or stack lifetime; must not import gc_*.
    - `noalloc` : strict no-allocation contract; may not call any allocating function.
-/
inductive Tier where
  | gc
  | nogc
  | noalloc
  deriving DecidableEq, Repr

/-- Tier ordering: `noalloc ≤ nogc ≤ gc`.
    A value of tier `t` is safe to use in a context of tier `u` iff `t ≤ u`
    (i.e. the context is at least as permissive as the value's origin).
    Passing a `gc` value into a `nogc` context violates this order.
-/
def Tier.le (t u : Tier) : Prop :=
  match t, u with
  | Tier.noalloc, _       => True
  | Tier.nogc,    Tier.gc => True
  | Tier.nogc,    Tier.nogc => True
  | Tier.gc,      Tier.gc => True
  | _,            _       => False

instance : LE Tier where le := Tier.le

theorem Tier.le_refl : ∀ t : Tier, t ≤ t := by
  intro t; cases t <;> simp [LE.le, Tier.le]

theorem Tier.le_trans : ∀ a b c : Tier, a ≤ b → b ≤ c → a ≤ c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;>
    simp [LE.le, Tier.le] at * <;> exact hbc

-- ============================================================
-- § 2  Annotation lattice for alloc_inference
-- ============================================================

/-- The alloc_inference annotation for a function.
    - `nonAlloc` : no allocation in any call path.
    - `alloc`    : reaches at least one allocation site.
    Ordered as a two-point lattice: `nonAlloc ≤ alloc`.
-/
inductive AllocAnn where
  | nonAlloc
  | alloc
  deriving DecidableEq, Repr, Inhabited

def AllocAnn.le (a b : AllocAnn) : Prop :=
  match a, b with
  | AllocAnn.nonAlloc, _ => True
  | AllocAnn.alloc, AllocAnn.alloc => True
  | AllocAnn.alloc, AllocAnn.nonAlloc => False

instance : LE AllocAnn where le := AllocAnn.le

def AllocAnn.join (a b : AllocAnn) : AllocAnn :=
  match a, b with
  | AllocAnn.alloc, _ => AllocAnn.alloc
  | _, AllocAnn.alloc => AllocAnn.alloc
  | AllocAnn.nonAlloc, AllocAnn.nonAlloc => AllocAnn.nonAlloc

theorem AllocAnn.le_refl : ∀ a : AllocAnn, a ≤ a := by
  intro a; cases a <;> simp [LE.le, AllocAnn.le]

theorem AllocAnn.join_ge_left (a b : AllocAnn) : a ≤ AllocAnn.join a b := by
  cases a <;> cases b <;> simp [LE.le, AllocAnn.le, AllocAnn.join]

theorem AllocAnn.join_ge_right (a b : AllocAnn) : b ≤ AllocAnn.join a b := by
  cases a <;> cases b <;> simp [LE.le, AllocAnn.le, AllocAnn.join]

-- ============================================================
-- § 3  Expression language
-- ============================================================

/-- Variable names (abstract). -/
abbrev Var := Nat

/-- A value carries its allocation origin tier. -/
structure Val where
  id   : Nat       -- abstract identity
  tier : Tier      -- allocation origin: gc | nogc | noalloc
  deriving Repr

/-- Expressions in the small language.
    - `Lit`   : a literal value with explicit tier (represents `new`, stack, etc.)
    - `Var`   : variable reference
    - `Copy`  : an explicit deep-copy node (satisfies the gc→nogc boundary rule)
    - `Call`  : function call with list of argument expressions
    - `Seq`   : sequencing two expressions (returns second)
-/
inductive Expr where
  | Lit  : Val → Expr
  | Var  : Var → Expr
  | Copy : Expr → Expr           -- explicit copy: isolates gc origin
  | Call : Nat → List Expr → Expr -- callee id, args
  | Seq  : Expr → Expr → Expr
  deriving Repr

-- ============================================================
-- § 4  Typing environment and judgement
-- ============================================================

/-- A typing environment maps variables to their tiers. -/
abbrev TierEnv := List (Var × Tier)

def TierEnv.lookup (env : TierEnv) (x : Var) : Option Tier :=
  match env.find? (fun p => p.fst == x) with
  | some (_, t) => some t
  | none        => none

/-- A function context: maps callee ids to their (annotation, body tier). -/
structure FnCtx where
  /-- The alloc annotation for each function id. -/
  allocAnn  : Nat → AllocAnn
  /-- The tier of values returned by each function. -/
  retTier   : Nat → Tier

/-- Typing judgement: `HasTier fc env e t` means expression `e` has tier `t`
    in function context `fc` and variable environment `env`. -/
inductive HasTier (fc : FnCtx) : TierEnv → Expr → Tier → Prop where
  /-- A literal has exactly its embedded tier.
      Written with a free `t` equal to `v.tier` so that `cases` on a
      `HasTier fc env (Lit v) Tier.gc` hypothesis succeeds without
      hitting the struct-field dependent-elimination restriction. -/
  | lit  : ∀ env v t,
      t = v.tier →
      HasTier fc env (Expr.Lit v) t

  /-- A variable has the tier its environment records. -/
  | var  : ∀ env x t,
      TierEnv.lookup env x = some t →
      HasTier fc env (Expr.Var x) t

  /-- A Copy node always has tier `nogc` (or better): the copy result is
      stack/manual-managed regardless of the source's tier.
      We conservatively give it `nogc` — it is not allocating-by-GC. -/
  | copy : ∀ env e _srcTier,
      HasTier fc env e _srcTier →
      HasTier fc env (Expr.Copy e) Tier.nogc

  /-- A Call expression has the return tier of the callee.
      Free `t` to avoid function-application dep-elim restriction. -/
  | call : ∀ env f args t,
      t = fc.retTier f →
      HasTier fc env (Expr.Call f args) t

  /-- Seq has the tier of its second (result) expression. -/
  | seq  : ∀ env e1 e2 _t1 t2,
      HasTier fc env e1 _t1 →
      HasTier fc env e2 t2 →
      HasTier fc env (Expr.Seq e1 e2) t2

-- ============================================================
-- § 5  Checker model
-- ============================================================

/-- The checker accepts an expression in a context tier `ctx` if every
    gc-origin sub-expression that flows into the context is wrapped in a
    Copy node.

    Formally: `CheckerOk fc ctx e` holds when `e` does not contain a
    direct `Var` or `Lit` of tier `gc` in a context that demands `nogc`
    or `noalloc`, without an intervening `Copy`.
-/
inductive CheckerOk (fc : FnCtx) : Tier → Expr → Prop where
  /-- A gc literal is only ok in a gc context. -/
  | lit_gc   : ∀ v, v.tier = Tier.gc → CheckerOk fc Tier.gc (Expr.Lit v)

  /-- A nogc/noalloc literal is ok in any context. -/
  | lit_safe : ∀ ctx v, v.tier ≠ Tier.gc → CheckerOk fc ctx (Expr.Lit v)

  /-- A variable of gc tier is only ok in a gc context. -/
  | var_gc   : ∀ env x,
      TierEnv.lookup env x = some Tier.gc →
      CheckerOk fc Tier.gc (Expr.Var x)

  /-- A variable of non-gc tier is ok in any context. -/
  | var_safe : ∀ ctx env x t,
      TierEnv.lookup env x = some t → t ≠ Tier.gc →
      CheckerOk fc ctx (Expr.Var x)

  /-- A Copy node is always ok in any context: it isolates the source tier. -/
  | copy     : ∀ ctx e srcCtx,
      CheckerOk fc srcCtx e →
      CheckerOk fc ctx (Expr.Copy e)

  /-- A Call is ok if the callee's return tier is safe for the context. -/
  | call_safe : ∀ ctx f args,
      (ctx = Tier.nogc ∨ ctx = Tier.noalloc) → fc.retTier f ≠ Tier.gc →
      CheckerOk fc ctx (Expr.Call f args)
  | call_gc   : ∀ f args,
      CheckerOk fc Tier.gc (Expr.Call f args)

  /-- Seq: both sub-expressions must be ok (second drives the result tier). -/
  | seq      : ∀ ctx e1 e2,
      CheckerOk fc ctx e1 →
      CheckerOk fc ctx e2 →
      CheckerOk fc ctx (Expr.Seq e1 e2)

/-- A noalloc function body is ok if every sub-expression in it:
    - makes no direct gc allocation (no gc-tier Lit), and
    - calls no function classified as allocating.
    This is structurally recursive, matching the real checker's full-body walk. -/
def noallocBodyOk (fc : FnCtx) : Expr → Prop
  | Expr.Lit v      => v.tier ≠ Tier.gc
  | Expr.Var _      => True
  | Expr.Copy e     => noallocBodyOk fc e
  | Expr.Call f _   => fc.allocAnn f = AllocAnn.nonAlloc
  | Expr.Seq e1 e2  => noallocBodyOk fc e1 ∧ noallocBodyOk fc e2

end GcBoundary
