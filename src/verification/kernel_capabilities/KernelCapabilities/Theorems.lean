/-
  KernelCapabilities.Theorems — Five provable theorems about the IPC capability model.

  All theorems are proved without `sorry`.

  T1  non_escalation       — any capability a process grants has rights ⊆ its own rights.
  T2  attenuation          — derived capabilities have ≤ rights AND strictly smaller depth.
  T3  revocation_complete  — after revoke(tok), owner no longer passes check (weak; see F1).
  T4  gate_sound           — syscall gate authorizes iff caller holds the kind.
  T5  default_deny         — a principal with no record passes no check.

  FINDINGS (implementation gaps vs. specification):
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  F1  NON-TRANSITIVE REVOCATION (capability.spl revoke, ~line 130-160):
      `revoke()` removes the token only from `tok.owner`'s record.  Copies
      granted to OTHER principals before revocation remain valid.  T3 is the
      weak (owner-only) form.  Transitively-derived capabilities are NOT revoked.
      The implementation needs a grant-lineage table for full transitive revocation.

  F2  NO DELEGATION DEPTH IN IMPL (capability_types.spl CapabilityToken struct):
      Real `CapabilityToken` has fields `kind`, `generation`, `owner` only — NO
      `depth` field.  `grant()` does not enforce delegation bounds.  T2 is proved
      for the model (which adds `depth`) but NOT enforced by the implementation.

  F3  FULL-SET WILDCARD ESCALATION RISK (capability_types.spl CapabilitySet.full):
      `CapabilitySet.full()` is an unpledged empty list; `has()` returns `true` for
      any kind when `!is_pledged && caps.len() == 0`.  Intended for pid 1 / init only,
      but `_ensure_record` callsites lack a kernel-enforced pid-1 check.
      File: capability.spl, `_ensure_record`, `init_task_record`.
-/

import KernelCapabilities.Basic

namespace KernelCapabilities

-- ============================================================
-- § A  Auxiliary lemmas
-- ============================================================

theorem rights_subset_refl (r : Rights) : Rights.subset r r :=
  fun _ h => h

theorem rights_subset_trans (a b c : Rights)
    (hab : Rights.subset a b) (hbc : Rights.subset b c) : Rights.subset a c :=
  fun r hr => hbc r (hab r hr)

-- ============================================================
-- § T1  non_escalation
-- ============================================================

-- Helper: grant returns none when check passes but subsetB is false
private theorem grant_none_of_subsetB_false
    (s : CapState) (grantor grantee : Principal) (newTok : CapToken)
    (hcheck_ok : s.check grantor newTok.kind = true)
    (hs : Rights.subsetB newTok.rights
        (match s.findRecord grantor with
         | none => []
         | some rec =>
           if rec.caps.isFullSet then newTok.rights
           else match rec.caps.tokens.find? (fun t => t.kind == newTok.kind) with
                | none => [] | some t => t.rights) = false) :
    CapState.grant s grantor grantee newTok = none := by
  unfold CapState.grant
  simp [hcheck_ok]
  exact hs

/-- T1: A granted token's rights ⊆ the grantor's rights for that kind.
    Meaning: no principal can grant more rights than it holds. -/
theorem non_escalation
    (s : CapState) (grantor grantee : Principal) (newTok : CapToken)
    (r : CapState)
    (hgrant : CapState.grant s grantor grantee newTok = some r) :
    Rights.subset newTok.rights
      (match s.findRecord grantor with
       | none => []
       | some rec =>
         if rec.caps.isFullSet then newTok.rights
         else match rec.caps.tokens.find? (fun t => t.kind == newTok.kind) with
              | none   => [] | some t => t.rights) := by
  -- Establish check = true
  have hcheck_ok : s.check grantor newTok.kind = true := by
    cases hc : s.check grantor newTok.kind
    · simp only [CapState.grant, hc, Bool.not_false, ite_true] at hgrant; simp at hgrant
    · rfl
  -- Establish subsetB = true by contradiction
  have hsubset_ok : Rights.subsetB newTok.rights
      (match s.findRecord grantor with
       | none => []
       | some rec =>
         if rec.caps.isFullSet then newTok.rights
         else match rec.caps.tokens.find? (fun t => t.kind == newTok.kind) with
              | none => [] | some t => t.rights) = true := by
    cases hs : Rights.subsetB newTok.rights
        (match s.findRecord grantor with
         | none => []
         | some rec =>
           if rec.caps.isFullSet then newTok.rights
           else match rec.caps.tokens.find? (fun t => t.kind == newTok.kind) with
                | none => [] | some t => t.rights)
    · exact absurd hgrant (by
        rw [grant_none_of_subsetB_false s grantor grantee newTok hcheck_ok hs]
        simp)
    · rfl
  exact (Rights.subsetB_iff _ _).mp hsubset_ok

-- ============================================================
-- § T2  attenuation
-- ============================================================

/-- T2: A derived token has rights ⊆ parent rights AND strictly smaller depth.
    Meaning: derivation attenuates authority, never amplifies it. -/
theorem attenuation
    (s : CapState) (src : Principal) (newTok : CapToken)
    (r : CapState)
    (hderive : CapState.deriveToken s src newTok = some r) :
    ∃ parent : CapToken,
      Rights.subset newTok.rights parent.rights ∧ newTok.depth < parent.depth := by
  simp only [CapState.deriveToken] at hderive
  cases h1 : s.findRecord src with
  | none => simp [h1] at hderive
  | some rec =>
    simp only [h1] at hderive
    -- split on outer match: parentOpt = none or some parent
    split at hderive
    · -- parentOpt = none → none = some r is False
      simp at hderive
    · -- parentOpt = some parent
      -- hderive : (if subsetB && decide(depth<depth') then some {...} else none) = some r
      rename_i parent _
      split at hderive
      · -- true branch: hderive is the state equality; extract witnesses from hg
        rename_i hg
        rw [Bool.and_eq_true, decide_eq_true_eq] at hg
        exact ⟨parent, (Rights.subsetB_iff _ _).mp hg.1, hg.2⟩
      · simp at hderive

-- ============================================================
-- § T3  revocation_complete (weak — owner only)
-- ============================================================

-- Named transform for the revoke map, to avoid parse issues with inline record syntax
private def revokeTransform (tok : CapToken) (r : PrincipalRecord) : PrincipalRecord :=
  if (r.pid == tok.owner) = true then { pid := r.pid, caps := { isFullSet := r.caps.isFullSet, tokens := r.caps.tokens.filter (fun t => !(t.kind == tok.kind && t.generation == tok.generation)) } } else r

private theorem revoke_transform_other (tok : CapToken) (r : PrincipalRecord)
    (hne : (r.pid == tok.owner) = false) :
    revokeTransform tok r = r := by
  simp only [revokeTransform, show (r.pid == tok.owner) = true ↔ False from by simp [hne], ite_false]

private theorem revoke_transform_owner (tok : CapToken) (r : PrincipalRecord)
    (heq : r = { pid := tok.owner, caps := { isFullSet := false, tokens := [tok] } }) :
    revokeTransform tok r =
      { pid := tok.owner, caps := { isFullSet := false, tokens := [] } } := by
  subst heq
  simp [revokeTransform, List.filter]

-- CapState.revoke applies revokeTransform to each record
private theorem revoke_records_eq (s : CapState) (tok : CapToken) :
    (CapState.revoke s tok).records = s.records.map (revokeTransform tok) := by
  simp only [CapState.revoke]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, revokeTransform]

-- After mapping revokeTransform, find? for the owner returns the filtered record
private theorem revoke_find_owner (recs : List PrincipalRecord) (tok : CapToken)
    (hrec : recs.find? (fun r => r.pid == tok.owner) =
              some { pid := tok.owner, caps := { isFullSet := false, tokens := [tok] } }) :
    (recs.map (revokeTransform tok)).find? (fun r => r.pid == tok.owner) =
      some { pid := tok.owner, caps := { isFullSet := false, tokens := [] } } := by
  induction recs with
  | nil => simp at hrec
  | cons hd tl ih =>
    simp only [List.map, List.find?]
    cases heq : (hd.pid == tok.owner)
    · rw [revoke_transform_other tok hd heq]
      simp only [List.find?, heq] at hrec
      simp only [heq]
      exact ih hrec
    · rw [revoke_transform_owner tok hd
            (by simp only [List.find?, heq] at hrec; exact Option.some.inj hrec)]
      simp

/-- T3 (weak): After revoking a token, the owner no longer passes check.
    Precondition: the owner holds exactly [tok] in their capability set.
    FINDING F1: Owner-only form. Other principals retaining the token are unaffected. -/
theorem revocation_complete
    (s : CapState) (tok : CapToken)
    (hrec : s.findRecord tok.owner =
              some { pid := tok.owner,
                     caps := { isFullSet := false, tokens := [tok] } }) :
    (CapState.revoke s tok).check tok.owner tok.kind = false := by
  simp only [CapState.check, CapState.findRecord]
  rw [revoke_records_eq]
  rw [revoke_find_owner s.records tok (by simp only [CapState.findRecord] at hrec; exact hrec)]
  simp

-- ============================================================
-- § T4  gate_sound
-- ============================================================

/-- T4: The syscall gate authorizes iff the caller holds the kind.
    Meaning: necessary and sufficient — no bypass, no over-deny. -/
theorem gate_sound (s : CapState) (caller : Principal) (kind : CapKind) :
    syscallAuthorize s caller kind = s.check caller kind := by
  simp [syscallAuthorize]

theorem gate_denies_without_capability
    (s : CapState) (caller : Principal) (kind : CapKind)
    (hcheck : s.check caller kind = false) :
    syscallAuthorize s caller kind = false := by
  simp [syscallAuthorize, hcheck]

-- ============================================================
-- § T5  default_deny
-- ============================================================

/-- T5: A principal with no record passes no capability check.
    Meaning: default posture is deny-all; authority must be explicitly granted. -/
theorem default_deny
    (s : CapState) (pid : Principal)
    (hnorec : s.findRecord pid = none)
    (kind : CapKind) :
    s.check pid kind = false := by
  simp [CapState.check, hnorec]

theorem empty_set_denies_all
    (s : CapState) (pid : Principal) (kind : CapKind)
    (hrec : s.findRecord pid = some { pid := pid, caps := CapSet.empty }) :
    s.check pid kind = false := by
  simp [CapState.check, hrec, CapSet.empty]

end KernelCapabilities
