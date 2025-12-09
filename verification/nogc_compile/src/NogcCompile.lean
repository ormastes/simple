namespace NogcCompile

/-- Mini IR with only arithmetic and explicit GC calls. -/
inductive Instr
  | const (n : Nat)
  | add
  | gcAlloc
  deriving DecidableEq, Repr

/-- No-GC programs exclude `gcAlloc`. -/
def nogc (p : List Instr) : Prop :=
  ∀ i, i ∈ p → i ≠ Instr.gcAlloc

def append (a b : List Instr) : List Instr :=
  a ++ b

theorem nogc_append {a b : List Instr} :
    nogc a → nogc b → nogc (append a b) := by
  intro ha hb i hmem
  have := List.mem_append.mp hmem
  cases this with
  | inl haMem => exact ha _ haMem
  | inr hbMem => exact hb _ hbMem

theorem nogc_singleton {i : Instr} (h : i ≠ Instr.gcAlloc) :
    nogc [i] := by
  intro j hj
  have h' : j = i := by simpa using hj
  subst h'
  exact h

end NogcCompile
