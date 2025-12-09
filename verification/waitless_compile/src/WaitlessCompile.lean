namespace WaitlessCompile

/-- Model a compile-time "waitless" check: a pipeline of effects that must be non-blocking. -/
inductive Effect
  | compute
  | io
  | wait
  deriving DecidableEq, Repr

def waitless (e : Effect) : Bool :=
  match e with
  | Effect.wait => false
  | _ => true

def pipelineSafe (es : List Effect) : Prop :=
  ∀ e, e ∈ es → waitless e = true

theorem append_safe {a b : List Effect} :
    pipelineSafe a → pipelineSafe b → pipelineSafe (a ++ b) := by
  intro ha hb e hmem
  apply List.mem_append.mp hmem |> Or.elim
  · intro h; exact ha _ h
  · intro h; exact hb _ h

theorem wait_detected (e : Effect) :
    pipelineSafe [e] → e ≠ Effect.wait := by
  intro h
  have hw : waitless e = true := h _ (by simp)
  cases e <;> simp_all [waitless]

end WaitlessCompile
