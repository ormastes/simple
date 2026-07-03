/-
  AopWeaver.Model — Lean 4 formal model of the Simple AOP weaver semantics.

  Source of truth:
    src/lib/nogc_sync_mut/src/aop.spl        (runtime: AspectRegistry, AspectWeaver.wrap)
    src/compiler_rust/runtime/src/aop.rs     (around chain, proceed exactly-once)

  Model: pure inductive semantics over lists, Int priorities, Bool outcomes.
  No sorry.  No Mathlib — std only.
-/
namespace AopWeaver

-- ---------------------------------------------------------------------------
-- 1. Core types
-- ---------------------------------------------------------------------------

inductive AdviceKind
  | Before | After | AfterError | Around
  deriving DecidableEq, Repr, BEq

inductive PointcutKind
  | All | FunctionCall | MethodCall | ModuleLoad
  deriving DecidableEq, Repr, BEq

structure JoinPoint where
  kind : PointcutKind
  name : String
  deriving Repr

structure Pointcut where
  kind    : PointcutKind
  pattern : Option String   -- None = wildcard "*"
  deriving Repr

structure Aspect where
  name     : String
  priority : Int
  pointcut : Pointcut
  kind     : AdviceKind
  enabled  : Bool
  /-- regOrder: registration index.  Lower = registered earlier.
      Formalises the stable order guarantee of find_aspects. -/
  regOrder : Nat
  deriving Repr

-- ---------------------------------------------------------------------------
-- 2. Pointcut matching
-- ---------------------------------------------------------------------------

def patternMatches (pat : Option String) (name : String) : Bool :=
  match pat with
  | none   => true
  | some p => (p == name)

def matchesJP (pc : Pointcut) (jp : JoinPoint) : Bool :=
  match pc.kind with
  | PointcutKind.All          => patternMatches pc.pattern jp.name
  | PointcutKind.FunctionCall =>
      jp.kind == PointcutKind.FunctionCall && patternMatches pc.pattern jp.name
  | PointcutKind.MethodCall   =>
      jp.kind == PointcutKind.MethodCall   && patternMatches pc.pattern jp.name
  | PointcutKind.ModuleLoad   =>
      jp.kind == PointcutKind.ModuleLoad   && patternMatches pc.pattern jp.name

-- ---------------------------------------------------------------------------
-- 3. Aspect selection  (find_aspects)
--
--    Insertion sort with key (priority DESC, regOrder ASC).
-- ---------------------------------------------------------------------------

/-- a should appear before b in the sorted output.
    Uses decide so Bool operations and omega work cleanly. -/
def precedes (a b : Aspect) : Bool :=
  decide (a.priority > b.priority) ||
  (a.priority == b.priority && decide (a.regOrder < b.regOrder))

def insAspect (a : Aspect) : List Aspect → List Aspect
  | []        => [a]
  | b :: rest => if precedes a b then a :: b :: rest else b :: insAspect a rest

def iSort : List Aspect → List Aspect
  | []       => []
  | a :: as' => insAspect a (iSort as')

def findAspects (reg : List Aspect) (jp : JoinPoint) : List Aspect :=
  iSort (reg.filter (fun a => a.enabled && matchesJP a.pointcut jp))

-- ---------------------------------------------------------------------------
-- 4. Sorted / stable predicates
-- ---------------------------------------------------------------------------

def sortedDesc : List Aspect → Prop
  | [] | [_]       => True
  | a :: b :: rest => a.priority ≥ b.priority ∧ sortedDesc (b :: rest)

def stableDesc : List Aspect → Prop
  | [] | [_]       => True
  | a :: b :: rest =>
      (a.priority > b.priority ∨
       (a.priority = b.priority ∧ a.regOrder ≤ b.regOrder)) ∧
      stableDesc (b :: rest)

-- ---------------------------------------------------------------------------
-- 5. Weaver state  (denial counter)
-- ---------------------------------------------------------------------------

structure WeaverState where
  denialCount : Nat
  deriving Repr

def WeaverState.empty : WeaverState := ⟨0⟩

/-- Record a denial: increment denialCount. -/
def deny (s : WeaverState) : WeaverState := ⟨s.denialCount + 1⟩

theorem deny_increments (s : WeaverState) :
    (deny s).denialCount = s.denialCount + 1 := by
  simp [deny]

-- ---------------------------------------------------------------------------
-- 6. wrap() execution model
--
--    Handler = fn(state) → (ok : Bool, newState).
--    ok = false means Err (denial-triggering).
-- ---------------------------------------------------------------------------

abbrev Handler := WeaverState → Bool × WeaverState

/-- Handler-monotone: a handler never decreases denialCount. -/
def HandlerMono (h : Handler) : Prop := ∀ s, s.denialCount ≤ (h s).2.denialCount

/-- TargetMono: target never decreases denialCount. -/
def TargetMono (t : WeaverState → Nat × WeaverState) : Prop :=
  ∀ s, s.denialCount ≤ (t s).2.denialCount

/-- Run Before/Around pre-hooks.  First Err → (denied=true, denial recorded).
    Around in aop.spl is a pre-hook only (no proceed callback). -/
def runPre : List Aspect → List Handler → WeaverState → Bool × WeaverState
  | [],       _,        s => (false, s)
  | _,        [],       s => (false, s)
  | a :: as', h :: hs', s =>
    match a.kind with
    | AdviceKind.Before | AdviceKind.Around =>
      let p := h s
      if p.1 then runPre as' hs' p.2 else (true, deny p.2)
    | _ => runPre as' hs' s

/-- Run After hooks.  Err masks target result and records a denial. -/
def runPost : List Aspect → List Handler → WeaverState → Bool × WeaverState
  | [],       _,        s => (false, s)
  | _,        [],       s => (false, s)
  | a :: as', h :: hs', s =>
    match a.kind with
    | AdviceKind.After =>
      let p := h s
      if p.1 then runPost as' hs' p.2 else (true, deny p.2)
    | _ => runPost as' hs' s

/-- Full wrap.  Returns (targetExecuted, Option result, finalState). -/
def wrapExec
    (aspects : List Aspect)
    (hs : List Handler)
    (target : WeaverState → Nat × WeaverState)
    (s : WeaverState) : Bool × Option Nat × WeaverState :=
  let pre := runPre aspects hs s
  if pre.1 then (false, none, pre.2)
  else
    let tr   := target pre.2
    let post := runPost aspects hs tr.2
    if post.1 then (true, none, post.2)
    else           (true, some tr.1, post.2)

-- ---------------------------------------------------------------------------
-- 7. Around chain with proceed  (runtime aop.rs semantics)
-- ---------------------------------------------------------------------------

inductive ProceedCount | Zero | Once | Many deriving DecidableEq, Repr

structure AroundResult where
  proceedCalls : ProceedCount
  deriving Repr

def wellFormedChain (rs : List AroundResult) : Bool :=
  rs.all (fun r => r.proceedCalls == ProceedCount.Once)

def chainTargetCount (rs : List AroundResult) : Nat :=
  if wellFormedChain rs then 1 else 0

-- ---------------------------------------------------------------------------
-- 8. Theorems
-- ---------------------------------------------------------------------------

-- ===== Helpers for precedes ================================================

private theorem prec_ge (a b : Aspect) (h : precedes a b = true) :
    a.priority ≥ b.priority := by
  simp only [precedes, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h1 | ⟨h2, _⟩ <;> omega

private theorem not_prec_ge (a b : Aspect) (h : ¬ precedes a b = true) :
    b.priority ≥ a.priority := by
  simp only [Bool.not_eq_true, precedes, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  omega

private theorem prec_stable (a b : Aspect) (h : precedes a b = true) :
    a.priority > b.priority ∨ (a.priority = b.priority ∧ a.regOrder ≤ b.regOrder) := by
  simp only [precedes, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, Nat.le_of_lt h3⟩

private theorem not_prec_stable (a b : Aspect) (h : ¬ precedes a b = true) :
    b.priority > a.priority ∨ (b.priority = a.priority ∧ b.regOrder ≤ a.regOrder) := by
  simp only [Bool.not_eq_true, precedes, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  rcases h with ⟨h1, h2⟩
  rcases h2 with hne | hnlt
  · left; omega
  · by_cases heq : a.priority = b.priority
    · right; exact ⟨heq.symm, by omega⟩
    · left; omega

-- ===== Helpers for insAspect ===============================================

-- insAspect is non-empty
theorem insAspect_ne (a : Aspect) (l : List Aspect) : insAspect a l ≠ [] := by
  cases l with
  | nil => simp [insAspect]
  | cons b bs => simp [insAspect]; split <;> simp

-- head? of insAspect a (c :: cs)
theorem insAspect_cons_head (a c : Aspect) (cs : List Aspect) :
    (insAspect a (c :: cs)).head? = if precedes a c then some a else some c := by
  simp only [insAspect]; split <;> simp

-- head? of insAspect a []
theorem insAspect_nil_head (a : Aspect) : (insAspect a []).head? = some a := by
  simp [insAspect]

-- b.priority ≥ head of insAspect a bs
private theorem insAspect_head_ge (a b : Aspect) (bs : List Aspect)
    (hge_a  : b.priority ≥ a.priority)
    (hge_bs : ∀ x, bs.head? = some x → b.priority ≥ x.priority) :
    ∀ x, (insAspect a bs).head? = some x → b.priority ≥ x.priority := by
  cases bs with
  | nil =>
    rw [insAspect_nil_head]; intro x hx; simp at hx; subst hx; exact hge_a
  | cons c cs =>
    rw [insAspect_cons_head]; split
    · intro x hx; simp at hx; subst hx; exact hge_a
    · intro x hx; simp at hx; subst hx; exact hge_bs c rfl

-- b rel head of insAspect a bs (stability variant)
private theorem insAspect_head_stable (a b : Aspect) (bs : List Aspect)
    (hstab_a  : b.priority > a.priority ∨ (b.priority = a.priority ∧ b.regOrder ≤ a.regOrder))
    (hstab_bs : ∀ x, bs.head? = some x →
        b.priority > x.priority ∨ (b.priority = x.priority ∧ b.regOrder ≤ x.regOrder)) :
    ∀ x, (insAspect a bs).head? = some x →
        b.priority > x.priority ∨ (b.priority = x.priority ∧ b.regOrder ≤ x.regOrder) := by
  cases bs with
  | nil =>
    rw [insAspect_nil_head]; intro x hx; simp at hx; subst hx; exact hstab_a
  | cons c cs =>
    rw [insAspect_cons_head]; split
    · intro x hx; simp at hx; subst hx; exact hstab_a
    · intro x hx; simp at hx; subst hx; exact hstab_bs c rfl

-- sortedDesc (b :: l) from b ≥ head l
private theorem sortedDesc_cons (b : Aspect) (l : List Aspect)
    (hge : ∀ x, l.head? = some x → b.priority ≥ x.priority)
    (hsd : sortedDesc l) : sortedDesc (b :: l) := by
  cases l with
  | nil => simp [sortedDesc]
  | cons c cs => simp only [sortedDesc]; exact ⟨hge c rfl, hsd⟩

-- stableDesc (b :: l)
private theorem stableDesc_cons (b : Aspect) (l : List Aspect)
    (hrel : ∀ x, l.head? = some x →
        b.priority > x.priority ∨ (b.priority = x.priority ∧ b.regOrder ≤ x.regOrder))
    (hsd : stableDesc l) : stableDesc (b :: l) := by
  cases l with
  | nil => simp [stableDesc]
  | cons c cs => simp only [stableDesc]; exact ⟨hrel c rfl, hsd⟩

-- ===== insAspect preserves sortedDesc and stableDesc =======================

theorem insAspect_sorted (a : Aspect) (l : List Aspect)
    (h : sortedDesc l) : sortedDesc (insAspect a l) := by
  induction l with
  | nil => simp [insAspect, sortedDesc]
  | cons b bs ih =>
    simp only [insAspect]
    split
    · -- precedes a b: result is a :: b :: bs
      rename_i hp
      simp only [sortedDesc]; exact ⟨prec_ge a b hp, h⟩
    · -- ¬precedes a b: result is b :: insAspect a bs
      rename_i hnp
      apply sortedDesc_cons
      · apply insAspect_head_ge
        · exact not_prec_ge a b hnp
        · cases bs with
          | nil => intro x hx; simp at hx
          | cons c cs =>
            simp only [sortedDesc] at h
            intro x hx; simp at hx; subst hx; exact h.1
      · cases bs with
        | nil => simp [insAspect, sortedDesc]
        | cons c cs =>
          simp only [sortedDesc] at h; exact ih h.2

theorem insAspect_stable (a : Aspect) (l : List Aspect)
    (hsd : sortedDesc l) (hst : stableDesc l) :
    stableDesc (insAspect a l) := by
  induction l with
  | nil => simp [insAspect, stableDesc]
  | cons b bs ih =>
    simp only [insAspect]
    split
    · -- precedes a b: result is a :: b :: bs
      rename_i hp
      simp only [stableDesc]; exact ⟨prec_stable a b hp, hst⟩
    · -- ¬precedes a b: result is b :: insAspect a bs
      rename_i hnp
      apply stableDesc_cons
      · apply insAspect_head_stable
        · exact not_prec_stable a b hnp
        · cases bs with
          | nil => intro x hx; simp at hx
          | cons c cs =>
            simp only [stableDesc] at hst
            intro x hx; simp at hx; subst hx; exact hst.1
      · cases bs with
        | nil => simp [insAspect, stableDesc]
        | cons c cs =>
          simp only [sortedDesc] at hsd
          simp only [stableDesc] at hst
          exact ih hsd.2 hst.2

/-- iSort preserves both orderings. -/
theorem iSort_sorted_stable (l : List Aspect) :
    sortedDesc (iSort l) ∧ stableDesc (iSort l) := by
  induction l with
  | nil => simp [iSort, sortedDesc, stableDesc]
  | cons a as' ih =>
    simp only [iSort]
    exact ⟨insAspect_sorted a (iSort as') ih.1,
           insAspect_stable a (iSort as') ih.1 ih.2⟩

-- ===== T1: find_aspects output is sorted by priority descending ============

theorem T1_selection_sorted (reg : List Aspect) (jp : JoinPoint) :
    sortedDesc (findAspects reg jp) :=
  (iSort_sorted_stable _).1

-- ===== T2: equal priorities preserve registration order ===================

theorem T2_selection_stable (reg : List Aspect) (jp : JoinPoint) :
    stableDesc (findAspects reg jp) :=
  (iSort_sorted_stable _).2

-- ===== T3: no matching aspects → wrap = pure target application ============

theorem T3_no_match_preserves
    (target : WeaverState → Nat × WeaverState)
    (s : WeaverState)
    (hs : List Handler) :
    wrapExec [] hs target s =
      (true, some (target s).1, (target s).2) := by
  simp [wrapExec, runPre, runPost]

-- ===== T4: Before/Around that errors → target does not execute ============

/-- A handler that always returns Err. -/
def errHandler : Handler := fun s => (false, s)

/-- A single Before aspect. -/
def mkBefore : Aspect :=
  { name := "deny", priority := 0,
    pointcut := { kind := PointcutKind.All, pattern := none },
    kind := AdviceKind.Before, enabled := true, regOrder := 0 }

theorem T4_deny_skips_target
    (target : WeaverState → Nat × WeaverState)
    (s : WeaverState) :
    let trip := wrapExec [mkBefore] [errHandler] target s
    trip.1 = false ∧ trip.2.2.denialCount = s.denialCount + 1 := by
  simp [wrapExec, runPre, errHandler, mkBefore, deny]

-- ===== T5: denial count is monotone non-decreasing =========================

private def restMono {f : Handler} {hs' : List Handler}
    (hm : ∀ x ∈ f :: hs', HandlerMono x) :
    ∀ x ∈ hs', HandlerMono x :=
  fun x hx => hm x (List.Mem.tail _ hx)

private theorem runPre_mono (aspects : List Aspect) (hs : List Handler)
    (hm : ∀ h ∈ hs, HandlerMono h) (s : WeaverState) :
    s.denialCount ≤ (runPre aspects hs s).2.denialCount := by
  induction aspects generalizing hs s with
  | nil => simp [runPre]
  | cons a as' ih =>
    cases hs with
    | nil => simp [runPre]
    | cons h hs' =>
      simp only [runPre]
      have hh  : HandlerMono h  := hm h (List.Mem.head _)
      have hm' : ∀ x ∈ hs', HandlerMono x := restMono hm
      cases a.kind with
      | Before =>
        simp only
        split
        · exact Nat.le_trans (hh s) (ih hs' hm' _)
        · simp [deny]; exact Nat.le_trans (hh s) (Nat.le_succ _)
      | Around =>
        simp only
        split
        · exact Nat.le_trans (hh s) (ih hs' hm' _)
        · simp [deny]; exact Nat.le_trans (hh s) (Nat.le_succ _)
      | After    => exact ih hs' hm' s
      | AfterError => exact ih hs' hm' s

private theorem runPost_mono (aspects : List Aspect) (hs : List Handler)
    (hm : ∀ h ∈ hs, HandlerMono h) (s : WeaverState) :
    s.denialCount ≤ (runPost aspects hs s).2.denialCount := by
  induction aspects generalizing hs s with
  | nil => simp [runPost]
  | cons a as' ih =>
    cases hs with
    | nil => simp [runPost]
    | cons h hs' =>
      simp only [runPost]
      have hh  : HandlerMono h  := hm h (List.Mem.head _)
      have hm' : ∀ x ∈ hs', HandlerMono x := restMono hm
      cases a.kind with
      | After =>
        simp only
        split
        · exact Nat.le_trans (hh s) (ih hs' hm' _)
        · simp [deny]; exact Nat.le_trans (hh s) (Nat.le_succ _)
      | Before | Around | AfterError => exact ih hs' hm' s

theorem T5_deny_monotone
    (aspects : List Aspect)
    (hs : List Handler)
    (hm : ∀ h ∈ hs, HandlerMono h)
    (target : WeaverState → Nat × WeaverState)
    (htgt : TargetMono target)
    (s : WeaverState) :
    s.denialCount ≤ (wrapExec aspects hs target s).2.2.denialCount := by
  simp only [wrapExec]
  split
  · exact runPre_mono aspects hs hm s
  · split
    · exact Nat.le_trans (runPre_mono aspects hs hm s)
        (Nat.le_trans (htgt _) (runPost_mono aspects hs hm _))
    · exact Nat.le_trans (runPre_mono aspects hs hm s)
        (Nat.le_trans (htgt _) (runPost_mono aspects hs hm _))

-- ===== T6: well-formed around chain → target executes exactly once =========

theorem T6_proceed_linear (rs : List AroundResult) :
    chainTargetCount rs ≤ 1 ∧
    (wellFormedChain rs = true → chainTargetCount rs = 1) := by
  constructor
  · simp [chainTargetCount]; split <;> omega
  · intro h; simp [chainTargetCount, h]

-- ---------------------------------------------------------------------------
-- 9. Soundness findings  (analysis only — no proof obligations)
-- ---------------------------------------------------------------------------

/-
  SOUNDNESS FINDING F1 — Around pre-hook vs proceed-chain mismatch:
    AspectWeaver.wrap in aop.spl treats Around advice as a pre-hook: it calls
    handler(before_ctx) and, on Err, records a denial and returns early — the
    proceed callback is never threaded through.  rt_aop_invoke_around in
    aop.rs implements a full proceed chain with exactly-once enforcement via
    ProceedContext.  These two code paths are NEVER unified: the .spl weaver
    does not call rt_aop_invoke_around.  T6 models the aop.rs semantics only;
    aop.spl Around is modelled identically to Before (T4).  A user relying on
    aop.spl Around for proceed semantics receives a pre-hook, not a proceed-
    chain.

  SOUNDNESS FINDING F2 — Stability tiebreaker divergence:
    Runtime find_aspects (aop.spl) uses a strict-greater test (>) with NO
    secondary tiebreaker in the selection sort.  Equal-priority ties are
    preserved only by accident (first-found stays first due to selection-sort
    mechanics), not by specification.  The compiler-frontend
    sort_matched_by_priority additionally breaks ties by specificity, then
    lexicographic advice-function name.  The model encodes stability via
    regOrder (insertion sort is provably stable); this is a stronger guarantee
    than either runtime provides.  T1/T2 prove the model's own guarantees, not
    the runtime's.

  SOUNDNESS FINDING F3 — After denial masks target result:
    When an After advice returns Err, wrapExec yields (true, none, s3):
    targetExecuted=true but the result is lost.  A caller cannot distinguish
    "target failed" from "after-advice denied without returning target result".
    No theorem was requested for this; noted as an observable ambiguity.
-/

end AopWeaver
