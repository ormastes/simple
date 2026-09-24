import ThreePayloadCompile.Model

namespace ThreePayloadCompile

theorem journal_exact_replay_idempotent (s t : JournalState)
    (p : JournalPrepared) (h : journalAccept s p = some t) :
    journalAccept t p = some t := by
  by_cases hgen : p.generation = s.generation
  · by_cases hfresh :
        s.entries = p.entryPrefix ∧
          s.nextSequence = p.record.sequence
    · rcases hfresh with ⟨hentries, hsequence⟩
      simp [journalAccept, hgen, hentries, hsequence] at h
      subst t
      simp [journalAccept, hgen]
    · by_cases hreplay :
          s.entries = p.entryPrefix ++ [p.record] ∧
            s.nextSequence = p.record.sequence + 1
      · simp [journalAccept, hgen, hfresh, hreplay] at h
        subst t
        simp [journalAccept, hgen, hfresh, hreplay]
      · simp [journalAccept, hgen, hfresh, hreplay] at h
  · simp [journalAccept, hgen] at h

theorem journal_conflicting_prefix_rejected (s : JournalState)
    (p : JournalPrepared)
    (hFresh : s.entries ≠ p.entryPrefix)
    (hReplay : s.entries ≠ p.entryPrefix ++ [p.record]) :
    journalAccept s p = none := by
  simp [journalAccept, hFresh, hReplay]

theorem protected_pin_not_swept (snapshotEpoch currentEpoch : Nat)
    (closureComplete : Bool) (protectedObjects : List String)
    (candidate : String) (h : candidate ∈ protectedObjects) :
    sweepDecision snapshotEpoch currentEpoch closureComplete protectedObjects
      candidate ≠ .eligible := by
  have hc : protectedObjects.contains candidate = true :=
    List.contains_iff_mem.mpr h
  unfold sweepDecision
  by_cases hguard : snapshotEpoch != currentEpoch || !closureComplete
  · simp [hguard]
  · simp [hguard, h]

theorem publication_resolution_reports_durable_active
    (candidate : GenerationIdentity) (event : PublicationAttemptEvent)
    (durable : DurablePublicationState) :
    resolvePublicationAttempt candidate event durable =
        .refused durable.active ∨
      resolvePublicationAttempt candidate event durable =
        .committed candidate durable.active ∨
      resolvePublicationAttempt candidate event durable =
        .unknown candidate durable.active := by
  cases event <;> simp [resolvePublicationAttempt]

theorem competing_publication_is_not_replaced_by_loser
    (candidate : GenerationIdentity) (durable : DurablePublicationState)
    (h : candidate ∉ durable.committedGenerations) :
    resolvePublicationAttempt candidate .casConflict durable =
      .refused durable.active := by
  cases hc : durable.committedGenerations.contains candidate with
  | false => simp [resolvePublicationAttempt, hc]
  | true => exact False.elim (h (List.contains_iff_mem.mp hc))

theorem post_cas_cancellation_resolves_recorded_commit
    (candidate : GenerationIdentity) (durable : DurablePublicationState)
    (h : candidate ∈ durable.committedGenerations) :
    resolvePublicationAttempt candidate .cancellationAfterCas durable =
      .committed candidate durable.active := by
  have hc : durable.committedGenerations.contains candidate = true :=
    List.contains_iff_mem.mpr h
  simp [resolvePublicationAttempt, hc]

theorem precommit_event_with_recorded_candidate_is_unknown
    (candidate : GenerationIdentity) (durable : DurablePublicationState)
    (h : candidate ∈ durable.committedGenerations) :
    resolvePublicationAttempt candidate .precommitRefusal durable =
      .unknown candidate durable.active := by
  have hc : durable.committedGenerations.contains candidate = true :=
    List.contains_iff_mem.mpr h
  simp [resolvePublicationAttempt, hc]

theorem same_generation_different_manifest_is_unknown
    (generation : Nat) (leftManifest rightManifest : String)
    (hne : leftManifest ≠ rightManifest) (durable : DurablePublicationState)
    (hleft : ({ generation := generation, manifest := leftManifest } :
      GenerationIdentity) ∈ durable.committedGenerations)
    (hright : ({ generation := generation, manifest := rightManifest } :
      GenerationIdentity) ∉ durable.committedGenerations) :
    resolvePublicationAttempt
      { generation := generation, manifest := rightManifest }
      .casAcknowledgmentLost durable =
      .unknown { generation := generation, manifest := rightManifest }
        durable.active := by
  cases hc : durable.committedGenerations.contains
      ({ generation := generation, manifest := rightManifest } :
        GenerationIdentity) with
  | false => simp [resolvePublicationAttempt, hc]
  | true =>
      exact False.elim (hright (List.contains_iff_mem.mp hc))

theorem atomic_record_swap_preserves_candidate_nonempty_shape
    (expected : GenerationIdentity) (candidate : DurableGeneration)
    (durable next : DurablePublicationState)
    (hpublish : atomicRecordSwap expected candidate durable = some next) :
    next.active = candidate ∧ durableGenerationNonemptyShape next.active := by
  unfold atomicRecordSwap at hpublish
  split at hpublish
  case isTrue hguard =>
    injection hpublish with hnext
    subst next
    exact ⟨rfl, hguard.2⟩
  case isFalse _ => contradiction

end ThreePayloadCompile
