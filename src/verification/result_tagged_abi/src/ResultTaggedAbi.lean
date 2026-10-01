/-
  ResultTaggedAbi — exact logical Result to tagged-runtime projection model.

  This proves the encoding/validator relation consumed by the per-build Simple
  translation validator. It does not assert that an arbitrary runtime binary
  implements rt_enum_new; release evidence must bind this root and its axiom
  audit to the exact runtime artifact hash.
-/
namespace ResultTaggedAbi

abbrev PayloadBits := BitVec 64

inductive Outcome where
  | ok (payload : PayloadBits)
  | err (payload : PayloadBits)
  deriving DecidableEq, Repr

structure TaggedProjection where
  enumId : Nat
  discriminant : Nat
  payload : PayloadBits
  deriving DecidableEq, Repr

def encode (resultEnumId : Nat) : Outcome → TaggedProjection
  | .ok payload => ⟨resultEnumId, 0, payload⟩
  | .err payload => ⟨resultEnumId, 1, payload⟩

def refines (resultEnumId : Nat) (source : Outcome)
    (target : TaggedProjection) : Prop :=
  target = encode resultEnumId source

def validate (resultEnumId : Nat) (source : Outcome)
    (target : TaggedProjection) : Bool :=
  target == encode resultEnumId source

theorem validate_sound (resultEnumId : Nat) (source : Outcome)
    (target : TaggedProjection) (accepted : validate resultEnumId source target = true) :
    refines resultEnumId source target := by
  simpa [validate, refines] using accepted

theorem refines_encode (resultEnumId : Nat) (source : Outcome) :
    refines resultEnumId source (encode resultEnumId source) := rfl

theorem normal_reachable (resultEnumId : Nat) :
    ∃ source target, source = Outcome.ok 41 ∧
      target = encode resultEnumId source ∧ validate resultEnumId source target = true := by
  exact ⟨.ok 41, encode resultEnumId (.ok 41), rfl, rfl, by simp [validate]⟩

theorem error_reachable (resultEnumId : Nat) :
    ∃ source target, source = Outcome.err 17 ∧
      target = encode resultEnumId source ∧ validate resultEnumId source target = true := by
  exact ⟨.err 17, encode resultEnumId (.err 17), rfl, rfl, by simp [validate]⟩

theorem variant_mutant_rejected (resultEnumId : Nat) (payload : PayloadBits) :
    validate resultEnumId (.err payload) ⟨resultEnumId, 0, payload⟩ = false := by
  simp [validate, encode]

theorem payload_mutant_rejected (resultEnumId : Nat) :
    validate resultEnumId (.ok 41) ⟨resultEnumId, 0, 42⟩ = false := by
  simp [validate, encode]

theorem enum_identity_mutant_rejected (resultEnumId : Nat) (payload : PayloadBits) :
    validate resultEnumId (.ok payload) ⟨resultEnumId + 1, 0, payload⟩ = false := by
  simp [validate, encode]

#print axioms validate_sound
#print axioms refines_encode
#print axioms normal_reachable
#print axioms error_reachable
#print axioms variant_mutant_rejected
#print axioms payload_mutant_rejected
#print axioms enum_identity_mutant_rejected

end ResultTaggedAbi
