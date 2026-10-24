/-
  CacheProtocol.Theorems.LiveKey — DURABLE MANUAL PROOFS over the LIVE key.
  The generator never writes this directory.

  Plan: doc/05_design/compiler/incremental_build/cache_invalidation_formal_verification_2026-10-24.md
    T-K1 key soundness           — live_key_sound, live_key_sound_without_gaps
    T-I1 invalidation completeness — invalidation_complete

  `ReadsOnly build` is the inputs-complete assumption, carried as a HYPOTHESIS
  (never an axiom): the build reads only the live key components and the
  counted gap inputs. Its correspondence to the Simple code is the reviewed
  source binding (src/verification/cache_protocol/source_bindings.txt,
  checked by scripts/check/check-cache-formal-source-binding.shs).

  Honest state: soundness holds unconditionally only once `allGaps = []`.
  Until then `live_key_sound` additionally requires the gap inputs to agree —
  i.e. a cache hit is sound only when none of the known gaps changed.
-/
import CacheProtocol.Generated.LiveKey

namespace CacheProtocol.Live

/-- Inputs-complete: the build is a function of the live key and the gap inputs. -/
def ReadsOnly {Out : Type} (build : Inputs → Out) : Prop :=
  ∀ i j : Inputs, i.live = j.live → i.gap = j.gap → build i = build j

/-- T-K1 (conditional): equal live encodings and equal gap inputs ⇒ equal output. -/
theorem live_key_sound {Out : Type} (build : Inputs → Out) (h : ReadsOnly build)
    (i j : Inputs) (hk : enc i.live = enc j.live) (hg : i.gap = j.gap) :
    build i = build j :=
  h i j (enc_inj hk) hg

/-- T-K1 (target form): once every gap is closed, equal live encoding alone
    implies equal output. Vacuous until `allGaps = []`. -/
theorem live_key_sound_without_gaps {Out : Type} (build : Inputs → Out)
    (h : ReadsOnly build) (hnone : allGaps = []) (i j : Inputs)
    (hk : enc i.live = enc j.live) : build i = build j := by
  apply h i j (enc_inj hk)
  funext g
  have hm := mem_allGaps g
  rw [hnone] at hm
  cases hm

/-- T-I1: any change that changes the output is visible in the live encoding
    or touches a counted known gap. -/
theorem invalidation_complete {Out : Type} (build : Inputs → Out)
    (h : ReadsOnly build) (i : Inputs) (δ : Inputs → Inputs)
    (hchg : build i ≠ build (δ i)) :
    enc i.live ≠ enc (δ i).live ∨ ∃ g, g ∈ allGaps ∧ i.gap g ≠ (δ i).gap g := by
  by_cases hk : enc i.live = enc (δ i).live
  · right
    apply Classical.byContradiction
    intro hno
    apply hchg
    apply h i (δ i) (enc_inj hk)
    funext g
    apply Classical.byContradiction
    intro hne
    exact hno ⟨g, mem_allGaps g, hne⟩
  · left
    exact hk

end CacheProtocol.Live
