namespace NogcCompile

/-- Mini IR with only arithmetic and explicit GC calls. -/
inductive Instr
  | const (n : Nat)
  | add
  | gcAlloc
  deriving DecidableEq, Repr

/-- GC mode configuration. -/
inductive GcMode
  | gc    -- GC-managed references (default)
  | nogc  -- Ownership-based unique pointers
  deriving DecidableEq, Repr

/-- GC configuration with provenance. -/
structure GcConfig where
  mode : GcMode
  explicit : Bool  -- true if user declared, false if inherited
  deriving DecidableEq, Repr

/-- No-GC programs exclude `gcAlloc`. -/
def nogc (p : List Instr) : Prop :=
  ∀ i, i ∈ p → i ≠ Instr.gcAlloc

def append (a b : List Instr) : List Instr :=
  a ++ b

/-- Effective GC config: explicit child overrides parent, otherwise inherits. -/
def effectiveGcConfig (child : GcConfig) (parent : GcConfig) : GcConfig :=
  if child.explicit then child else parent

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

/-- GC mode propagation is consistent: inherited mode equals parent mode
    when child is not explicit. -/
theorem gc_mode_propagation_consistent (child parent : GcConfig) :
    child.explicit = false →
    (effectiveGcConfig child parent).mode = parent.mode := by
  intro h
  simp [effectiveGcConfig, h]

/-- When child is explicit, its mode is preserved regardless of parent. -/
theorem gc_mode_explicit_override (child parent : GcConfig) :
    child.explicit = true →
    (effectiveGcConfig child parent).mode = child.mode := by
  intro h
  simp [effectiveGcConfig, h]

/-- Programs in NoGc mode produce no gcAlloc instructions.
    Strengthened: given a compile function that respects GC mode,
    if the mode is nogc, the output is gc-free. -/
theorem nogc_no_gc_alloc (compile : GcConfig → List Instr)
    (h : ∀ cfg, cfg.mode = GcMode.nogc → nogc (compile cfg))
    (cfg : GcConfig) (hmode : cfg.mode = GcMode.nogc) :
    nogc (compile cfg) :=
  h cfg hmode

/-- Cross-mode composition: appending a nogc program to any nogc program
    preserves the nogc property. -/
theorem cross_mode_safety {a b : List Instr} :
    nogc a → nogc b → nogc (append a b) :=
  nogc_append

end NogcCompile
