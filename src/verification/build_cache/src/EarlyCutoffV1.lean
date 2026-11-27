/-
  EarlyCutoffV1 — T-RG1 red/green early-cutoff soundness for
  package_tldr_early_cutoff_v1
  (src/compiler/80.driver/cache/package_tldr_metadata.spl).

  A rebuilt dependency whose header agrees with the previous one on every
  COMPARED field lets its consumers stay green. Sound iff every header field a
  consumer may read is compared. The classification below is the reviewed
  claim; the SSpec twin
  test/00_formal_verification/compiler/package_tldr_early_cutoff_bounded_spec.spl
  pins the Simple function to `compared` field by field (each compared field's
  change blocks cutoff; each non-compared field's change does not).
  Plan: cache_invalidation_formal_verification_2026-10-24.md §4.1 T-RG1.
  Status: package_tldr_early_cutoff_v1 has no caller on release/1.0.0 yet, so
  this proves the predicate a future red/green driver must use.
  No sorry, no axioms.
-/
namespace EarlyCutoffV1

/-- Every PackageTldrHeaderV1 field (variant compared by config_variant_digest_v1). -/
inductive HField where
  | schema_version | producer_digest | package_identity | module_identity
  | source_identity | variant | source_digest | source_witness_digest
  | smf_digest | smf_sections | export_digest | abi_digest
  | initializer_digest | provider_digest | generated_source_digest
  | reverse_projection_digest | direct_imports | reverse_dependents
  | scc_identity | scc_members | interface_archive_digest | action_archive_digest
  deriving DecidableEq, Repr

open HField

/-- Fields package_tldr_early_cutoff_v1 compares (both headers must also validate). -/
def compared : List HField :=
  [producer_digest, package_identity, module_identity, variant, smf_digest,
   export_digest, abi_digest, initializer_digest, provider_digest,
   generated_source_digest, reverse_projection_digest, interface_archive_digest]

/-- Fields a consumer of the package may read. Producer-side inputs
    (source_*, smf_sections, action_archive_digest, direct_imports,
    scc_*) reach a consumer only through the compared output digests;
    reverse_dependents is derived FROM consumers. -/
def consumerVisible : List HField := compared

theorem consumer_visible_compared : ∀ f ∈ consumerVisible, f ∈ compared := by
  intro f hf; exact hf

abbrev Header := HField → String

def cutoff (p r : Header) : Bool := compared.all (fun f => p f == r f)

/-- T-RG1: early cutoff never keeps a consumer green whose output would change. -/
theorem early_cutoff_sound {Out : Type} (consume : Header → Out)
    (hreads : ∀ h1 h2 : Header, (∀ f ∈ consumerVisible, h1 f = h2 f) → consume h1 = consume h2)
    (p r : Header) (hc : cutoff p r = true) : consume p = consume r := by
  apply hreads
  intro f hf
  have hall := List.all_eq_true.mp hc f (consumer_visible_compared f hf)
  simpa using hall

/-- Every compared field blocks cutoff when it changes. -/
theorem compared_change_blocks_cutoff (p r : Header) (f : HField) (hf : f ∈ compared)
    (hne : p f ≠ r f) : cutoff p r = false := by
  unfold cutoff
  rw [Bool.eq_false_iff]
  intro hall
  have := List.all_eq_true.mp hall f hf
  simp at this
  exact hne this

theorem compared_count : compared.length = 12 := by decide

end EarlyCutoffV1
