/-!
# MonoBoundaryModel — nominal owner resolution and the mono→MIR boundary

MANUAL-OWNED: `simple gen-lean` never writes this file. It is a reduced model
of three production rules, not a refinement proof of the compiler:

1. Variant shadowing (commit `9697890ad02`, PR #3807,
   `20.hir/hir_lowering/_Items/declaration_lowering.spl` `lower_variant`):
   an enum variant never rebinds a bare name that the current scope already
   binds to a struct/class/enum/trait/alias declaration.
2. Nominal owner proof at instantiation (E-MONO-041,
   `40.mono/monomorphize_integration.spl`): every nominal type argument must
   resolve to a type declaration owner, otherwise the call is not specialized
   and a diagnostic is emitted (fail closed).
3. Mono→MIR boundary (E-MONO-033, `80.driver/driver_mono_publication_v1.spl`
   `driver_publish_mono_diagnostics_v1`): any mono diagnostic refuses MIR
   lowering, so no non-monomorphic generic call is published.

Names are interned as `Nat`. Scopes are newest-first association lists, which
matches `define` shadowing older bindings. Production symbol tables, glob
imports, the variant symbol's reachability through its enum and the
correspondence `DiagComplete` ↔ the real diagnostic stream are open
obligations recorded in
`doc/03_plan/generic_formal_verification_hardening_plan.md` §12.
-/
namespace MonoBoundaryModel

abbrev Ident := Nat

inductive SymKind where
  | structDecl
  | classDecl
  | enumDecl
  | traitDecl
  | aliasDecl
  | enumVariant
  | function
  | other
  deriving DecidableEq, Repr

/-- The kinds accepted by `scope_binds_type_symbol` and by the E-MONO-041
    owner proof. -/
def SymKind.isType : SymKind → Bool
  | .structDecl | .classDecl | .enumDecl | .traitDecl | .aliasDecl => true
  | _ => false

structure Sym where
  id : Nat
  kind : SymKind
  deriving DecidableEq, Repr

abbrev Scope := List (Ident × Sym)

def lookup : Scope → Ident → Option Sym
  | [], _ => none
  | (m, s) :: rest, n => if m = n then some s else lookup rest n

def bindsType (sc : Scope) (n : Ident) : Bool :=
  match lookup sc n with
  | some s => s.kind.isType
  | none => false

/-- Unconditional binding (`symbols.define`). -/
def define (sc : Scope) (n : Ident) (s : Sym) : Scope := (n, s) :: sc

/-- `lower_variant` after `9697890ad02`: the bare variant name is bound only
    when the scope does not already bind it to a type declaration. -/
def defineVariant (sc : Scope) (n : Ident) (id : Nat) : Scope :=
  if bindsType sc n then sc else define sc n ⟨id, .enumVariant⟩

/-- Owner-uniqueness under variant shadowing: lowering any variant leaves every
    existing type binding unchanged. -/
theorem defineVariant_preserves_type_binding (sc : Scope) (v n : Ident) (id : Nat)
    (s : Sym) (hl : lookup sc n = some s) (ht : s.kind.isType = true) :
    lookup (defineVariant sc v id) n = some s := by
  unfold defineVariant
  by_cases hb : bindsType sc v = true
  · rw [if_pos hb]
    exact hl
  · rw [if_neg hb]
    have hne : v ≠ n := by
      intro hvn
      subst hvn
      apply hb
      simp [bindsType, hl, ht]
    simp [define, lookup, hne, hl]

/-! ### E-MONO-041: nominal type arguments need a proven declaration owner -/

inductive MonoError where
  | noProvenOwner (n : Ident)
  deriving DecidableEq, Repr

def resolveOwner (sc : Scope) (n : Ident) : Except MonoError Sym :=
  match lookup sc n with
  | some s => if s.kind.isType then .ok s else .error (.noProvenOwner n)
  | none => .error (.noProvenOwner n)

def resolveArgs (sc : Scope) : List Ident → Except MonoError (List Sym)
  | [] => .ok []
  | n :: rest =>
    match resolveOwner sc n with
    | .error e => .error e
    | .ok s =>
      match resolveArgs sc rest with
      | .error e => .error e
      | .ok ss => .ok (s :: ss)

theorem resolveOwner_ok (sc : Scope) (n : Ident) (s : Sym)
    (h : resolveOwner sc n = .ok s) :
    lookup sc n = some s ∧ s.kind.isType = true := by
  unfold resolveOwner at h
  split at h
  · split at h
    · cases h
      constructor <;> assumption
    · cases h
  · cases h

theorem resolveOwner_ok_isType (sc : Scope) (n : Ident) (s : Sym)
    (h : resolveOwner sc n = .ok s) : s.kind.isType = true :=
  (resolveOwner_ok sc n s h).2

/-- Every argument of a successful instantiation resolves to a type owner;
    a variant, function or unbound name cannot be specialized. -/
theorem resolveArgs_ok_all_types (sc : Scope) :
    ∀ (ns : List Ident) (ss : List Sym),
      resolveArgs sc ns = .ok ss → ∀ s ∈ ss, s.kind.isType = true
  | [], ss => by
    intro h
    simp only [resolveArgs] at h
    cases h
    intro s hs
    cases hs
  | n :: rest, ss => by
    simp only [resolveArgs]
    cases h0 : resolveOwner sc n with
    | error e => intro h; cases h
    | ok s0 =>
      cases h1 : resolveArgs sc rest with
      | error e => intro h; cases h
      | ok ss0 =>
        intro h
        cases h
        intro s hs
        cases hs with
        | head => exact resolveOwner_ok_isType sc n s0 h0
        | tail _ hmem => exact resolveArgs_ok_all_types sc rest ss0 h1 s hmem

/-- Variant lowering cannot turn a proven owner into an E-MONO-041 refusal. -/
theorem resolveOwner_stable_under_variant (sc : Scope) (v n : Ident) (id : Nat)
    (s : Sym) (h : resolveOwner sc n = .ok s) :
    resolveOwner (defineVariant sc v id) n = .ok s := by
  obtain ⟨hl, ht⟩ := resolveOwner_ok sc n s h
  have hl' := defineVariant_preserves_type_binding sc v n id s hl ht
  unfold resolveOwner
  rw [hl']
  simp [ht]

/-- Bug replay (pre-`9697890ad02`): unconditional variant binding displaces
    the class `Block`, so the owner proof fails closed with E-MONO-041. -/
theorem unconditional_variant_binding_loses_owner :
    resolveOwner (define [(0, ⟨1, .classDecl⟩)] 0 ⟨2, .enumVariant⟩) 0
      = .error (.noProvenOwner 0) := rfl

theorem guarded_variant_binding_keeps_owner :
    resolveOwner (defineVariant [(0, ⟨1, .classDecl⟩)] 0 2) 0
      = .ok ⟨1, .classDecl⟩ := rfl

/-- A variant with no same-named type is still bound (the guard is not a
    blanket refusal). -/
theorem variant_without_type_is_bound :
    lookup (defineVariant [] 0 2) 0 = some ⟨2, .enumVariant⟩ := rfl

/-! ### E-MONO-033: no non-monomorphic generic call reaches MIR -/

inductive Call where
  | concrete (target : Ident)
  | generic (template : Ident) (typeArgs : List Ident)
  deriving DecidableEq, Repr

def Call.isGeneric : Call → Bool
  | .generic _ _ => true
  | .concrete _ => false

structure HirModule where
  calls : List Call

abbrev Diags := List Call

def Monomorphic (m : HirModule) : Prop :=
  ∀ c ∈ m.calls, c.isGeneric = false

/-- Diagnostic coverage: every generic call left in the module is diagnosed.
    For the real pass this is an open obligation (see the plan, §12). -/
def DiagComplete (m : HirModule) (d : Diags) : Prop :=
  ∀ c ∈ m.calls, c.isGeneric = true → c ∈ d

/-- `driver_publish_mono_diagnostics_v1`: any diagnostic refuses lowering. -/
def publishToMir (m : HirModule) (d : Diags) : Option HirModule :=
  if d = [] then some m else none

theorem publish_refuses_with_diagnostics (m : HirModule) (d : Diags)
    (h : d ≠ []) : publishToMir m d = none := by
  unfold publishToMir
  rw [if_neg h]

/-- Boundary soundness: given diagnostic coverage, a module accepted for MIR
    lowering contains no generic call. -/
theorem mono_boundary_sound (m m' : HirModule) (d : Diags)
    (hc : DiagComplete m d) (hp : publishToMir m d = some m') : Monomorphic m' := by
  unfold DiagComplete at hc
  unfold publishToMir at hp
  split at hp
  · rename_i hnil
    cases hp
    unfold Monomorphic
    intro c hmem
    cases hg : c.isGeneric with
    | false => rfl
    | true =>
      have hd : c ∈ d := hc c hmem hg
      rw [hnil] at hd
      cases hd
  · cases hp

/-- Model mono step for one call: specialize when every type argument has a
    proven owner, otherwise keep the call and diagnose it (E-MONO-041). The
    specialization identity is abstracted to the template name. -/
def rewriteCall (sc : Scope) : Call → Call × Diags
  | .concrete t => (.concrete t, [])
  | .generic tpl args =>
    match resolveArgs sc args with
    | .ok _ => (.concrete tpl, [])
    | .error _ => (.generic tpl args, [.generic tpl args])

def monoCalls (sc : Scope) : List Call → List Call × Diags
  | [] => ([], [])
  | c :: rest =>
    let r := rewriteCall sc c
    let rs := monoCalls sc rest
    (r.1 :: rs.1, r.2 ++ rs.2)

def monoPass (sc : Scope) (m : HirModule) : HirModule × Diags :=
  let r := monoCalls sc m.calls
  (⟨r.1⟩, r.2)

theorem rewriteCall_diag (sc : Scope) (c : Call)
    (hg : (rewriteCall sc c).1.isGeneric = true) :
    (rewriteCall sc c).1 ∈ (rewriteCall sc c).2 := by
  revert hg
  cases c with
  | concrete t => simp [rewriteCall, Call.isGeneric]
  | generic tpl args =>
    simp only [rewriteCall]
    cases resolveArgs sc args with
    | ok _ => simp [Call.isGeneric]
    | error _ => simp [Call.isGeneric]

theorem monoCalls_diag_complete (sc : Scope) :
    ∀ cs : List Call, ∀ c ∈ (monoCalls sc cs).1,
      c.isGeneric = true → c ∈ (monoCalls sc cs).2
  | [] => by simp [monoCalls]
  | c0 :: rest => by
    intro c hc hg
    simp only [monoCalls] at hc ⊢
    cases hc with
    | head => exact List.mem_append.mpr (Or.inl (rewriteCall_diag sc c0 hg))
    | tail _ hmem =>
      exact List.mem_append.mpr (Or.inr (monoCalls_diag_complete sc rest c hmem hg))

/-- The model pass discharges `DiagComplete` for its own output. -/
theorem monoPass_diag_complete (sc : Scope) (m : HirModule) :
    DiagComplete (monoPass sc m).1 (monoPass sc m).2 := by
  unfold DiagComplete monoPass
  intro c hc hg
  exact monoCalls_diag_complete sc m.calls c hc hg

/-- End to end (model): whatever the model mono pass hands to MIR is
    monomorphic. -/
theorem monoPass_publish_monomorphic (sc : Scope) (m m' : HirModule)
    (hp : publishToMir (monoPass sc m).1 (monoPass sc m).2 = some m') :
    Monomorphic m' :=
  mono_boundary_sound _ m' _ (monoPass_diag_complete sc m) hp

/-- A specialized call had a proven owner for every nominal argument. -/
theorem rewriteCall_concrete_has_owners (sc : Scope) (tpl : Ident)
    (args : List Ident) (t : Ident)
    (h : (rewriteCall sc (.generic tpl args)).1 = .concrete t) :
    ∃ ss, resolveArgs sc args = .ok ss ∧ ∀ s ∈ ss, s.kind.isType = true := by
  simp only [rewriteCall] at h
  cases hr : resolveArgs sc args with
  | ok ss => exact ⟨ss, rfl, resolveArgs_ok_all_types sc args ss hr⟩
  | error e =>
    rw [hr] at h
    simp at h

/-- Non-vacuity: a diagnosed generic call is refused. -/
theorem generic_call_refused :
    publishToMir ⟨[.generic 0 [1]]⟩ [.generic 0 [1]] = none := rfl

/-- Coverage is necessary: an undiagnosed generic call (e.g. one the counter
    missed) would be published. This is why G7 `post_mono_verify` recounts
    independently of the pass's own diagnostics. -/
theorem undiagnosed_generic_call_published :
    publishToMir ⟨[.generic 0 [1]]⟩ [] = some ⟨[.generic 0 [1]]⟩ := rfl

#print axioms defineVariant_preserves_type_binding
#print axioms resolveOwner_ok
#print axioms resolveArgs_ok_all_types
#print axioms resolveOwner_stable_under_variant
#print axioms unconditional_variant_binding_loses_owner
#print axioms guarded_variant_binding_keeps_owner
#print axioms variant_without_type_is_bound
#print axioms publish_refuses_with_diagnostics
#print axioms mono_boundary_sound
#print axioms rewriteCall_diag
#print axioms monoCalls_diag_complete
#print axioms monoPass_diag_complete
#print axioms monoPass_publish_monomorphic
#print axioms rewriteCall_concrete_has_owners
#print axioms generic_call_refused
#print axioms undiagnosed_generic_call_published

end MonoBoundaryModel
