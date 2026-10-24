/-
  WeaveCallOnlyV1 — the advice-body -> weave-output gap is redundant under
  CALL-ONLY weaving.

  The weavers (src/compiler/35.semantics/aspect_weave.spl `_weave_body`,
  src/compiler/50.mir/mir_aop_injection.spl `inject_*_advice` via
  `make_advice_call_inst`) only INSERT a call to the advice function by name
  into the join point; they never copy an advice body. So a woven consumer is
  a function of (its own code, the ordered advice NAMES and forms), and an
  advice body lives only in the advice module's own object, keyed by that
  module's own source. Plan gap advice_body_weave_root
  (cache_invalidation_formal_verification_2026-10-24.md).

  Proved: weave_independent_of_advice_bodies, advice_body_change_keeps_consumer,
  advice_body_change_changes_advice_module_key, and the counterexample
  copy_weave_would_need_body_in_key showing why the call-only property is
  the load-bearing assumption (pinned in source_bindings.txt and by
  test/00_formal_verification/compiler/aop_call_only_weave_contract_spec.spl).
  No sorry, no axioms.
-/
namespace WeaveCallOnlyV1

abbrev Instr := String

structure Advice where
  name : String
  body : List Instr
  deriving DecidableEq, Repr

/-- Call-only weaving: prepend one call per advice, by name. -/
def weave (consumer : List Instr) (advices : List Advice) : List Instr :=
  advices.map (fun a => "call " ++ a.name) ++ consumer

/-- Two advice lists that agree on names (bodies may differ). -/
def sameNames (xs ys : List Advice) : Prop := xs.map Advice.name = ys.map Advice.name

theorem weave_independent_of_advice_bodies (consumer : List Instr) (xs ys : List Advice)
    (h : sameNames xs ys) : weave consumer xs = weave consumer ys := by
  unfold weave sameNames at *
  congr 1
  have : xs.map (fun a => "call " ++ a.name) = (xs.map Advice.name).map (fun n => "call " ++ n) := by
    simp [List.map_map]
  have h2 : ys.map (fun a => "call " ++ a.name) = (ys.map Advice.name).map (fun n => "call " ++ n) := by
    simp [List.map_map]
  rw [this, h2, h]

/-- Editing one advice body never changes a woven consumer. -/
theorem advice_body_change_keeps_consumer (consumer : List Instr) (pre post : List Advice)
    (a : Advice) (b : List Instr) :
    weave consumer (pre ++ a :: post) = weave consumer (pre ++ { a with body := b } :: post) := by
  apply weave_independent_of_advice_bodies
  unfold sameNames; simp

/-- The advice module's own object is keyed by its source, which contains the body. -/
def adviceModuleKey (a : Advice) : String × List Instr := (a.name, a.body)

theorem advice_body_change_changes_advice_module_key (a : Advice) (b : List Instr)
    (h : b ≠ a.body) : adviceModuleKey a ≠ adviceModuleKey { a with body := b } := by
  unfold adviceModuleKey; intro he; simp at he; exact h he.symm

/-- If a weaver ever COPIED bodies, the consumer would depend on them: the
    call-only property is what makes the gap redundant. -/
def weaveCopy (consumer : List Instr) (advices : List Advice) : List Instr :=
  (advices.map Advice.body).foldr (· ++ ·) [] ++ consumer

theorem copy_weave_would_need_body_in_key :
    ∃ (c : List Instr) (a : Advice) (b : List Instr),
      weaveCopy c [a] ≠ weaveCopy c [{ a with body := b }] :=
  ⟨[], ⟨"log", ["x"]⟩, ["y"], by decide⟩

end WeaveCallOnlyV1
