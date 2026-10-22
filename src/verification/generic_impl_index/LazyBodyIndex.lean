import Std

/-!
A bounded operational model for the single-pass lazy body index in
`MonomorphizationPass.collect_generic_impl_methods`.

Assumptions: module function order and impl order are stable during the pass;
function symbol ids are stable; assigning duplicate ids follows last-write-wins
semantics; and generic impl methods resolve by symbol id. This is a model of
the lookup strategy, not a proof of correspondence to production HIR/Dict APIs.
-/

namespace LazyBodyIndex

structure SourceFn where
  symbol : Nat
  body : Nat
  deriving DecidableEq, Repr

structure Impl where
  hasTypeParams : Bool
  methodSymbols : List Nat
  deriving DecidableEq, Repr

abbrev BodyIndex := List (Nat × Nat)

/-- Construct the index entries once, retaining source order. -/
def buildIndex (functions : List SourceFn) : BodyIndex :=
  functions.map fun fn => (fn.symbol, fn.body)

/-- Reverse lookup gives last-write-wins over the stable source function order. -/
def lookupBody (index : BodyIndex) (symbol : Nat) : Option Nat :=
  (index.reverse.find? fun entry => entry.1 == symbol).map Prod.snd

def eagerOutputs (functions : List SourceFn) : List Impl → List (Option Nat)
  | [] => []
  | impl :: rest =>
      (if impl.hasTypeParams then
        impl.methodSymbols.map (lookupBody (buildIndex functions))
       else []) ++ eagerOutputs functions rest

def ensureIndex (functions : List SourceFn) (cached : Option BodyIndex) : BodyIndex × Bool :=
  match cached with
  | some index => (index, false)
  | none => (buildIndex functions, true)

/-- Execute the lazy collector. The first generic impl ensures one index;
    all later impls receive that same cached value. Nongeneric impls are skipped.
    A method symbol absent from the function table yields `none`. -/
def lazyRun (functions : List SourceFn) : List Impl → Option BodyIndex → List (Option Nat) × Nat
  | [], _ => ([], 0)
  | impl :: rest, cached =>
      if impl.hasTypeParams then
        let (index, built) := ensureIndex functions cached
        let (tail, builds) := lazyRun functions rest (some index)
        (impl.methodSymbols.map (lookupBody index) ++ tail,
         builds + if built then 1 else 0)
      else
        lazyRun functions rest cached

def lazyOutputs (functions : List SourceFn) (impls : List Impl) : List (Option Nat) :=
  (lazyRun functions impls none).1

def lazyBuildCount (functions : List SourceFn) (impls : List Impl) : Nat :=
  (lazyRun functions impls none).2

def hasGenericImpl : List Impl → Bool
  | [] => false
  | impl :: rest => impl.hasTypeParams || hasGenericImpl rest

theorem eager_outputs_empty_of_no_generic (functions : List SourceFn) (impls : List Impl)
    (h : hasGenericImpl impls = false) : eagerOutputs functions impls = [] := by
  induction impls with
  | nil => rfl
  | cons impl rest ih =>
      cases impl with
      | mk generic methods =>
        cases generic with
        | false =>
            have hrest : hasGenericImpl rest = false := by
              simpa [hasGenericImpl] using h
            simpa [eagerOutputs, hrest] using ih hrest
        | true => simp [hasGenericImpl] at h

theorem lazyRun_cached_count_zero (functions : List SourceFn) (impls : List Impl)
    (index : BodyIndex) : (lazyRun functions impls (some index)).2 = 0 := by
  induction impls with
  | nil => rfl
  | cons impl rest ih =>
      cases impl with
      | mk generic methods =>
        cases generic with
        | false => simpa [lazyRun] using ih
        | true => simpa [lazyRun, ensureIndex] using ih

theorem lazy_index_builds_at_most_once (functions : List SourceFn) (impls : List Impl) :
    lazyBuildCount functions impls ≤ 1 := by
  induction impls with
  | nil => simp [lazyBuildCount, lazyRun]
  | cons impl rest ih =>
      cases impl with
      | mk generic methods =>
        cases generic with
        | false => simpa [lazyBuildCount, lazyRun] using ih
        | true =>
            simp [lazyBuildCount, lazyRun, ensureIndex, lazyRun_cached_count_zero]

theorem lazyRun_output_equal_eager (functions : List SourceFn) (impls : List Impl)
    (cached : Option BodyIndex)
    (hc : cached = none ∨ cached = some (buildIndex functions)) :
    (lazyRun functions impls cached).1 = eagerOutputs functions impls := by
  induction impls generalizing cached with
  | nil => rfl
  | cons impl rest ih =>
      cases impl with
      | mk generic methods =>
        cases generic with
        | false =>
            simpa [lazyRun, eagerOutputs] using ih cached hc
        | true =>
            cases cached with
            | none =>
                simpa [lazyRun, ensureIndex, eagerOutputs] using
                  ih (some (buildIndex functions)) (Or.inr rfl)
            | some index =>
                have hindex : some index = some (buildIndex functions) := by
                  rcases hc with hnone | hsome
                  · cases hnone
                  · exact hsome
                injection hindex with hindex
                subst index
                simpa [lazyRun, ensureIndex, eagerOutputs] using
                  ih (some (buildIndex functions)) (Or.inr rfl)

theorem lazy_outputs_equal_eager (functions : List SourceFn) (impls : List Impl) :
    lazyOutputs functions impls = eagerOutputs functions impls := by
  simpa [lazyOutputs] using
    lazyRun_output_equal_eager functions impls none (Or.inl rfl)

theorem lazy_outputs_empty_without_generic (functions : List SourceFn) (impls : List Impl)
    (h : hasGenericImpl impls = false) : lazyOutputs functions impls = [] := by
  rw [lazy_outputs_equal_eager]
  exact eager_outputs_empty_of_no_generic functions impls h

theorem no_index_without_generic_impl (functions : List SourceFn) (impls : List Impl)
    (h : hasGenericImpl impls = false) : lazyBuildCount functions impls = 0 := by
  induction impls with
  | nil => rfl
  | cons impl rest ih =>
      cases impl with
      | mk generic methods =>
        cases generic with
        | false =>
            simpa [lazyBuildCount, lazyRun, hasGenericImpl] using ih (by simpa [hasGenericImpl] using h)
        | true => simp [hasGenericImpl] at h

end LazyBodyIndex
