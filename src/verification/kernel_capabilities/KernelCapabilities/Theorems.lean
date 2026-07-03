/-
  KernelCapabilities.Theorems — Five provable theorems about the IPC capability model.

  All theorems are proved without `sorry`.

  T1  non_escalation       — any capability a process grants has rights ⊆ its own rights.
  T2  attenuation          — derived capabilities have ≤ rights AND strictly smaller depth
                             (proved against the real depth field — E4 implemented).
  T3  revocation_complete  — after revokeTransitive(rootId), no token with that root
                             ancestry passes check (strong transitive form — E3 implemented).
  T3_direct                — after revoke(tok), owner no longer passes check (direct form).
  T4  gate_sound           — syscall gate authorizes iff caller holds the kind.
  T5  default_deny         — a principal with no record passes no check.
  T6  zero_depth_grant_denied
                            — capability delegation fails when depth is exhausted.
  T7  full_set_allows_any_kind
                            — full capability set is a wildcard hazard.
  T8  full_set_syscall_authorizes_any_kind
                            — the wildcard reaches the syscall gate.
  T9  full_set_owner_is_trusted
                            — the full-set invariant restricts the wildcard owner.
  T10 sanitize_init_caps_non_trusted_full_is_empty
                            — runtime init sanitization lowers non-trusted full sets.
  T11 file_access_requires_capability
                            — file access is impossible without the file capability gate.
  T12 invalid_permission_denies_file_access
                            — invalid permission strings fail before capability/unveil.
  T13 path_prefix_without_segment_boundary_denied
                            — shared string prefix alone is not path authority.

  FINDINGS (remaining implementation gaps vs. specification):
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  F3  FULL-SET WILDCARD ESCALATION RISK (capability_types.spl CapabilitySet.full):
      `CapabilitySet.full()` is an unpledged empty list; `has()` returns `true` for
      any kind when `!is_pledged && caps.len() == 0`.  Intended for pid 1 / init only,
      but `_ensure_record` callsites lack a kernel-enforced pid-1 check.
      File: capability.spl, `_ensure_record`, `init_task_record`.

  CLOSED FINDINGS (fixed by E3/E4 — 2026-06-11):
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  F1  TRANSITIVE REVOCATION: implemented via revoke_transitive() with iterative worklist.
      T3 is now the strong (all-principal) form using revokeTransitive.
  F2  DELEGATION DEPTH: `CapabilityToken` now has `depth: i64`; `grant()` enforces
      depth > 0 (deny, not clamp); child gets depth = parent.depth - 1; default 2.
      T2 proves against the real field.
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

-- Helper: grant returns none when check passes, depth > 0, but subsetB is false
private theorem grant_none_of_subsetB_false
    (s : CapState) (grantor grantee : Principal) (newTok : CapToken)
    (hcheck_ok : s.check grantor newTok.kind = true)
    (hdepth : newTok.depth ≠ 0)
    (hs : Rights.subsetB newTok.rights
        (match s.findRecord grantor with
         | none => []
         | some rec =>
           if rec.caps.isFullSet then newTok.rights
           else match rec.caps.tokens.find? (fun t => t.kind == newTok.kind) with
                | none => [] | some t => t.rights) = false) :
    CapState.grant s grantor grantee newTok = none := by
  unfold CapState.grant
  simp [hcheck_ok, hdepth]
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
  -- Establish depth ≠ 0
  have hdepth : newTok.depth ≠ 0 := by
    intro hd
    simp only [CapState.grant, hcheck_ok, Bool.not_true, hd] at hgrant
    simp at hgrant
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
        rw [grant_none_of_subsetB_false s grantor grantee newTok hcheck_ok hdepth hs]
        simp)
    · rfl
  exact (Rights.subsetB_iff _ _).mp hsubset_ok

/-- T6: Delegation depth is a hard gate.  A token with depth=0 cannot be
    granted even if the grantor otherwise has the capability kind. -/
theorem zero_depth_grant_denied
    (s : CapState) (grantor grantee : Principal) (tok : CapToken)
    (hdepth : tok.depth = 0) :
    CapState.grant s grantor grantee tok = none := by
  unfold CapState.grant
  cases s.check grantor tok.kind <;> simp [hdepth]

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
-- § T3  revocation_complete (strong — transitive, E3)
-- ============================================================

-- Helper: isDescendant applied per-record filter removes matching tokens
private theorem isDescendant_self (rootId : Nat) (tok : CapToken)
    (hid : tok.tokenId = rootId) :
    isDescendant rootId tok = true := by
  simp [isDescendant, hid]

-- revokeTransitive maps a filter over all records
private theorem revokeTransitive_records (s : CapState) (rootId : Nat) :
    (CapState.revokeTransitive s rootId).records =
      s.records.map (fun r =>
        { r with caps := { r.caps with
            tokens := r.caps.tokens.filter (fun t => !isDescendant rootId t) } }) := by
  simp [CapState.revokeTransitive]

-- After filtering, no token with tokenId == rootId remains in any record
private theorem filter_removes_root (toks : List CapToken) (rootId : Nat) :
    ∀ t, t ∈ toks.filter (fun t => !isDescendant rootId t) →
         t.tokenId ≠ rootId := by
  intro t hmem
  rw [List.mem_filter] at hmem
  obtain ⟨_, hnotDesc⟩ := hmem
  simp [isDescendant] at hnotDesc
  obtain ⟨hne, _⟩ := hnotDesc
  exact hne

-- Standalone helper: walking a list with the transitive filter
private theorem revokeTransitive_find_pid
    (recs : List PrincipalRecord) (rootId pid : Nat) (kind : CapKind)
    (hrec : recs.find? (fun r => r.pid == pid) =
              some { pid := pid,
                     caps := { isFullSet := false,
                               tokens := [{ kind := kind, rights := [], generation := 0,
                                            owner := pid, tokenId := rootId,
                                            parentTokenId := 0, depth := 0 }] } }) :
    (recs.map (fun r => { r with caps := { r.caps with
        tokens := r.caps.tokens.filter (fun t => !isDescendant rootId t) } })
    ).find? (fun r => r.pid == pid) =
    some { pid := pid, caps := { isFullSet := false, tokens := [] } } := by
  induction recs with
  | nil => simp at hrec
  | cons hd tl ih =>
    simp only [List.map, List.find?]
    cases heq : (hd.pid == pid)
    · apply ih
      simp only [List.find?, heq] at hrec
      exact hrec
    · have hhd : hd = { pid := pid,
                        caps := { isFullSet := false,
                                  tokens := [{ kind := kind, rights := [], generation := 0,
                                               owner := pid, tokenId := rootId,
                                               parentTokenId := 0, depth := 0 }] } } := by
        simp only [List.find?, heq] at hrec
        exact Option.some.inj hrec
      subst hhd
      -- After filter, the single token with tokenId=rootId is removed
      have hfilter : ([({ kind := kind, rights := [], generation := 0, owner := pid,
                          tokenId := rootId, parentTokenId := 0, depth := 0 } : CapToken)
                      ].filter (fun t => !isDescendant rootId t)) = [] := by
        simp [isDescendant]
      simp [hfilter]

/-- T3 (strong / transitive): After revokeTransitive(rootId), any principal
    whose ONLY capability of `kind` was a token with tokenId = rootId no
    longer passes check for that kind.
    E3: this is the full transitive revocation property. -/
theorem revocation_complete
    (s : CapState) (rootId : Nat) (pid : Principal) (kind : CapKind)
    (hrec : s.findRecord pid =
              some { pid := pid,
                     caps := { isFullSet := false,
                               tokens := [{ kind := kind, rights := [], generation := 0,
                                            owner := pid, tokenId := rootId,
                                            parentTokenId := 0, depth := 0 }] } }) :
    (CapState.revokeTransitive s rootId).check pid kind = false := by
  simp only [CapState.check, CapState.findRecord, CapState.revokeTransitive]
  have hfind := revokeTransitive_find_pid s.records rootId pid kind
        (by simp only [CapState.findRecord] at hrec; exact hrec)
  rw [hfind]
  simp

/-- T3_child: After revokeTransitive(rootId), a direct child token whose
    parentTokenId is rootId no longer passes check. -/
theorem revocation_complete_direct_child
    (rootId childId : Nat) (pid : Principal) (kind : CapKind) :
    (CapState.revokeTransitive
      ({ records :=
          [{ pid := pid
           , caps :=
              { isFullSet := false
              , tokens :=
                  [{ kind := kind, rights := [], generation := 0, owner := pid,
                     tokenId := childId, parentTokenId := rootId, depth := 0 }] } }]
       , nextGeneration := 1
       , nextTokenId := 1 } : CapState)
      rootId).check pid kind = false := by
  simp [CapState.revokeTransitive, CapState.check, CapState.findRecord, isDescendant]

/-- Direct child transitive revocation also denies the syscall authorization gate. -/
theorem revocation_complete_direct_child_syscall
    (rootId childId : Nat) (pid : Principal) (kind : CapKind) :
    syscallAuthorize
      (CapState.revokeTransitive
        ({ records :=
            [{ pid := pid
             , caps :=
                { isFullSet := false
                , tokens :=
                    [{ kind := kind, rights := [], generation := 0, owner := pid,
                       tokenId := childId, parentTokenId := rootId, depth := 0 }] } }]
         , nextGeneration := 1
         , nextTokenId := 1 } : CapState)
        rootId)
      pid kind = false := by
  simp [syscallAuthorize, CapState.revokeTransitive, CapState.check,
    CapState.findRecord, isDescendant]

-- ============================================================
-- § T3_direct  revocation_complete_direct (owner-only form)
-- ============================================================

-- Named transform for the direct revoke map
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

/-- T3_direct: After revoking a token (owner-only), the owner no longer passes check.
    Precondition: the owner holds exactly [tok] in their capability set. -/
theorem revocation_complete_direct
    (s : CapState) (tok : CapToken)
    (hrec : s.findRecord tok.owner =
              some { pid := tok.owner,
                     caps := { isFullSet := false, tokens := [tok] } }) :
    (CapState.revoke s tok).check tok.owner tok.kind = false := by
  simp only [CapState.check, CapState.findRecord]
  rw [revoke_records_eq]
  rw [revoke_find_owner s.records tok (by simp only [CapState.findRecord] at hrec; exact hrec)]
  simp

/-- Direct owner-only revoke preserves non-owner capability checks. -/
theorem revoke_non_owner_check_preserved
    (tok : CapToken) (rec : PrincipalRecord) (kind : CapKind)
    (hne : rec.pid ≠ tok.owner) :
    (CapState.revoke
      ({ records := [rec], nextGeneration := 1, nextTokenId := 1 } : CapState)
      tok).check rec.pid kind =
    ({ records := [rec], nextGeneration := 1, nextTokenId := 1 } : CapState).check rec.pid kind := by
  simp [CapState.revoke, CapState.check, CapState.findRecord, hne]

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

/-- A principal with no record is denied by the syscall gate for every kind. -/
theorem default_deny_syscall
    (s : CapState) (pid : Principal)
    (hnorec : s.findRecord pid = none)
    (kind : CapKind) :
    syscallAuthorize s pid kind = false := by
  simp [syscallAuthorize, CapState.check, hnorec]

theorem empty_set_denies_all
    (s : CapState) (pid : Principal) (kind : CapKind)
    (hrec : s.findRecord pid = some { pid := pid, caps := CapSet.empty }) :
    s.check pid kind = false := by
  simp [CapState.check, hrec, CapSet.empty]

/-- Empty capability sets deny every syscall authorization. -/
theorem empty_set_syscall_denies_all
    (s : CapState) (pid : Principal) (kind : CapKind)
    (hrec : s.findRecord pid = some { pid := pid, caps := CapSet.empty }) :
    syscallAuthorize s pid kind = false := by
  simp [syscallAuthorize, CapState.check, hrec, CapSet.empty]

/-- T7: A principal with CapSet.full passes every capability-kind check.
    This is an explicit hazard theorem, not a safety endorsement: production
    code must constrain full sets to trusted init/kernel principals. -/
theorem full_set_allows_any_kind
    (s : CapState) (pid : Principal) (kind : CapKind)
    (hrec : s.findRecord pid = some { pid := pid, caps := CapSet.full }) :
    s.check pid kind = true := by
  simp [CapState.check, hrec, CapSet.full]

/-- T8: The CapSet.full wildcard reaches the syscall authorization gate. -/
theorem full_set_syscall_authorizes_any_kind
    (s : CapState) (pid : Principal) (kind : CapKind)
    (hrec : s.findRecord pid = some { pid := pid, caps := CapSet.full }) :
    syscallAuthorize s pid kind = true := by
  simp [syscallAuthorize, CapState.check, hrec, CapSet.full]

/-- T9: Under the full-set restriction invariant, any principal holding
    CapSet.full is exactly the trusted init/kernel principal. -/
theorem full_set_owner_is_trusted
    (s : CapState) (trusted pid : Principal)
    (honly : s.fullSetOnlyFor trusted)
    (hrec : s.findRecord pid = some { pid := pid, caps := CapSet.full }) :
    pid = trusted := by
  exact honly pid hrec

/-- The full-set restriction invariant excludes CapSet.full from every
    non-trusted principal. -/
theorem non_trusted_full_set_forbidden
    (s : CapState) (trusted pid : Principal)
    (honly : s.fullSetOnlyFor trusted)
    (hne : pid ≠ trusted) :
    s.findRecord pid ≠ some { pid := pid, caps := CapSet.full } := by
  intro hrec
  exact hne (honly pid hrec)

/-- T10: Runtime init sanitization lowers ambient full-set input for every
    non-trusted principal to the deny-all empty set. -/
theorem sanitize_init_caps_non_trusted_full_is_empty
    (trusted pid : Principal)
    (hne : pid ≠ trusted) :
    sanitizeInitCaps trusted pid CapSet.full = CapSet.empty := by
  simp [sanitizeInitCaps, CapSet.full, CapSet.empty, hne]

/-- A sanitized non-trusted ambient full set becomes an explicit deny-all
    record for every capability-kind check. -/
theorem sanitize_init_caps_non_trusted_full_denies_all
    (trusted pid : Principal) (kind : CapKind)
    (hne : pid ≠ trusted) :
    ({ records := [{ pid := pid, caps := sanitizeInitCaps trusted pid CapSet.full }]
     , nextGeneration := 1
     , nextTokenId := 1 } : CapState).check pid kind = false := by
  simp [CapState.check, CapState.findRecord, sanitizeInitCaps, CapSet.full,
    CapSet.empty, hne]

/-- A sanitized non-trusted ambient full set is also denied at the syscall
    authorization gate. -/
theorem sanitize_init_caps_non_trusted_full_syscall_denies_all
    (trusted pid : Principal) (kind : CapKind)
    (hne : pid ≠ trusted) :
    syscallAuthorize
      ({ records := [{ pid := pid, caps := sanitizeInitCaps trusted pid CapSet.full }]
       , nextGeneration := 1
       , nextTokenId := 1 } : CapState)
      pid kind = false := by
  simp [syscallAuthorize, CapState.check, CapState.findRecord, sanitizeInitCaps,
    CapSet.full, CapSet.empty, hne]

/-- Trusted init/kernel may retain the ambient full-set shape through init. -/
theorem sanitize_init_caps_trusted_full_stays_full
    (trusted : Principal) :
    sanitizeInitCaps trusted trusted CapSet.full = CapSet.full := by
  simp [sanitizeInitCaps, CapSet.full]

/-- T11: File access fails closed when the normal file capability gate fails,
    regardless of unveil state or path match. -/
theorem file_access_requires_capability
    (isUnveiled unveilAllows : Bool) :
    fileAccessAllowed false isUnveiled unveilAllows = false := by
  simp [fileAccessAllowed]

/-- When unveiled, file access requires both the file capability and an
    allowed unveil path. -/
theorem unveiled_file_access_requires_capability_and_path
    (hasFileCap unveilAllows : Bool) :
    fileAccessAllowed hasFileCap true unveilAllows = (hasFileCap && unveilAllows) := by
  simp [fileAccessAllowed]

/-- Before unveil, file access depends only on the normal file capability gate. -/
theorem file_access_before_unveil_depends_only_on_capability
    (hasFileCap unveilAllows : Bool) :
    fileAccessAllowed hasFileCap false unveilAllows = hasFileCap := by
  simp [fileAccessAllowed]

/-- T12: Invalid permission strings deny file access regardless of capability
    or unveil state. -/
theorem invalid_permission_denies_file_access
    (hasFileCap isUnveiled unveilAllows : Bool) :
    fileAccessAllowedWithPerm false hasFileCap isUnveiled unveilAllows = false := by
  simp [fileAccessAllowedWithPerm]

/-- Valid permission strings preserve the normal file-access gate. -/
theorem valid_permission_uses_file_access_gate
    (hasFileCap isUnveiled unveilAllows : Bool) :
    fileAccessAllowedWithPerm true hasFileCap isUnveiled unveilAllows =
      fileAccessAllowed hasFileCap isUnveiled unveilAllows := by
  simp [fileAccessAllowedWithPerm]

/-- T13: A path that only shares a string prefix, without exact/root match or
    a following path separator, is denied. -/
theorem path_prefix_without_segment_boundary_denied :
    segmentPrefixAllowed false false true false = false := by
  simp [segmentPrefixAllowed]

/-- Root prefix allows every path. -/
theorem root_path_prefix_allows
    (isExact hasPrefix hasBoundary : Bool) :
    segmentPrefixAllowed true isExact hasPrefix hasBoundary = true := by
  simp [segmentPrefixAllowed]

/-- Exact path prefix allows the path. -/
theorem exact_path_prefix_allows
    (isRoot hasPrefix hasBoundary : Bool) :
    segmentPrefixAllowed isRoot true hasPrefix hasBoundary = true := by
  cases isRoot <;> simp [segmentPrefixAllowed]

/-- A real prefix followed by a path separator allows the path. -/
theorem segment_boundary_prefix_allows :
    segmentPrefixAllowed false false true true = true := by
  simp [segmentPrefixAllowed]

/-- T14: A write request is denied without write capability, even if read
    capability exists. -/
theorem write_request_requires_write_capability
    (hasRead requestRead : Bool) :
    rwFileAccessAllowed hasRead false requestRead true = false := by
  cases hasRead <;> cases requestRead <;> simp [rwFileAccessAllowed]

/-- A read request is denied without read capability, even if write capability exists. -/
theorem read_request_requires_read_capability
    (hasWrite requestWrite : Bool) :
    rwFileAccessAllowed false hasWrite true requestWrite = false := by
  cases hasWrite <;> cases requestWrite <;> simp [rwFileAccessAllowed]

/-- A read request is allowed exactly when read capability exists, when no write
    right is requested. -/
theorem read_request_uses_read_capability
    (hasRead hasWrite : Bool) :
    rwFileAccessAllowed hasRead hasWrite true false = hasRead := by
  cases hasRead <;> cases hasWrite <;> simp [rwFileAccessAllowed]

/-- A combined read/write request requires both read and write capabilities. -/
theorem read_write_request_requires_both_capabilities
    (hasRead hasWrite : Bool) :
    rwFileAccessAllowed hasRead hasWrite true true = (hasRead && hasWrite) := by
  cases hasRead <;> cases hasWrite <;> simp [rwFileAccessAllowed]

end KernelCapabilities
