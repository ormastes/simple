/-
  OsEnforcement.TufUpdate — pure model of the SimpleOS update service's
  TUF-style signed-metadata verifier, with sorry-free proofs of the update
  security invariants (master plan §20 / §21.3).

  Source of truth (FVT — 2026-07-27):
    src/os/services/update/tuf_metadata.spl
      struct RoleMetadata { role, version, expires_at, threshold,
                            signer_key_ids, signatures_present,
                            delegated_key_ids, recorded_targets_version }
      count_valid_signers / verify_threshold / check_freshness /
      rollback_guard / verify_snapshot_consistency / keys_trusted_by_root /
      root_trusted_set / verify_update  (fail-closed pipeline, distinct
      TUF_* reason per attack class)

  Real semantics being modelled
  =============================
  verify_update runs the four TUF roles (root, timestamp, snapshot, targets)
  through five checks IN ORDER, failing closed on the first violation:
    1. every presented signature key traces to root's trusted set
       (root's own signer keys ++ its delegated keys — the trust anchor);
    2. each role has ≥ threshold DISTINCT valid signers (a signer counts only
       if authorized for the role and not already counted);
    3. no role metadata is past expires_at (freeze / freshness defense);
    4. no role's incoming version is below the locally trusted current
       version (rollback defense);
    5. snapshot's recorded targets version equals the presented targets
       version (anti mix-and-match).

  Modelling notes
  ===============
  Key-ids are `Nat` atoms (the .spl uses text; only equality is ever used).
  Signatures are modelled exactly as in the .spl: `sigsPresent` is the list
  of key-ids whose signatures are (by upstream assumption) already
  cryptographically verified.  `countValidAux` mirrors the .spl's
  seen-list distinctness loop.  The Outcome inductive mirrors the .spl's
  distinct TUF_* reason codes and the first-failing-check-decides order.
  Core Lean 4 only (List/Nat/Bool), no Mathlib.

  Headline theorems (SPipe manual layer):
    OsEnforcement.Tuf.accepted_no_rollback        (T1)
    OsEnforcement.Tuf.expired_rejected            (T2)
    OsEnforcement.Tuf.no_single_key_compromise    (T3)
    OsEnforcement.Tuf.snapshot_mismatch_rejected  (T4)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement.Tuf

-- ============================================================
-- § 1  Model structs (mirror RoleMetadata / CurrentVersions)
-- ============================================================

/-- Signed metadata for one TUF role (mirrors `RoleMetadata`).  The `role`
    name tag is elided: `verify_update` never branches on it. -/
structure RoleMeta where
  version                : Nat
  expiresAt              : Nat
  threshold              : Nat
  signerKeys             : List Nat  -- keys authorized to sign THIS role
  sigsPresent            : List Nat  -- keys whose signatures verified upstream
  delegatedKeys          : List Nat  -- root only: all keys root delegates
  recordedTargetsVersion : Nat       -- snapshot only: pinned targets version
  deriving Repr

/-- Locally trusted current version of each role (mirrors `CurrentVersions`). -/
structure Current where
  root      : Nat
  timestamp : Nat
  snapshot  : Nat
  targets   : Nat
  deriving Repr

/-- Verification outcome (mirrors `VerifyOutcome` + the TUF_* reason codes).
    Exactly one constructor per fail-closed rejection reason. -/
inductive Outcome where
  | accepted
  | untrustedKey       -- TUF_UNTRUSTED_KEY
  | badThreshold       -- TUF_BAD_THRESHOLD
  | expired            -- TUF_EXPIRED
  | rollback           -- TUF_ROLLBACK
  | snapshotMismatch   -- TUF_SNAPSHOT_MISMATCH
  deriving Repr, DecidableEq

-- ============================================================
-- § 2  Per-role verifier primitives (mirror the .spl functions)
-- ============================================================

/-- `rootTrustedSet root` mirrors `root_trusted_set`: root's own signing keys
    plus every key it delegates — the trust anchor. -/
def rootTrustedSet (root : RoleMeta) : List Nat :=
  root.signerKeys ++ root.delegatedKeys

/-- `keysTrusted m trusted` mirrors `keys_trusted_by_root`: deny if any signer
    key on `m` is not in root's trusted set. -/
def keysTrusted (m : RoleMeta) (trusted : List Nat) : Bool :=
  m.sigsPresent.all (fun k => trusted.contains k)

/-- Accumulator form of `count_valid_signers`: count key-ids that both signed
    AND are authorized, each distinct key counted once (`seen` list). -/
def countValidAux : List Nat → List Nat → List Nat → Nat
  | [], _, _ => 0
  | k :: rest, signer, seen =>
    if signer.contains k = true ∧ seen.contains k = false
    then countValidAux rest signer (k :: seen) + 1
    else countValidAux rest signer seen

/-- `countValidSigners m` mirrors `count_valid_signers`. -/
def countValidSigners (m : RoleMeta) : Nat :=
  countValidAux m.sigsPresent m.signerKeys []

/-- `verifyThreshold m` mirrors `verify_threshold`: deny unless at least
    `threshold` distinct valid signers signed. -/
def verifyThreshold (m : RoleMeta) : Bool :=
  decide (m.threshold ≤ countValidSigners m)

/-- `checkFreshness m now` mirrors `check_freshness`: deny if `now` is past
    `expires_at` (freeze / expiry defense). -/
def checkFreshness (m : RoleMeta) (now : Nat) : Bool :=
  decide (now ≤ m.expiresAt)

/-- `rollbackGuard cur incoming` mirrors `rollback_guard`: deny any incoming
    version below the current one. -/
def rollbackGuard (cur incoming : Nat) : Bool :=
  decide (cur ≤ incoming)

/-- `snapshotConsistent` mirrors `verify_snapshot_consistency`. -/
def snapshotConsistent (snapRecorded tgtVersion : Nat) : Bool :=
  snapRecorded == tgtVersion

-- ============================================================
-- § 3  Full verification pipeline (mirrors `verify_update`)
-- ============================================================

/-- `verifyUpdate` mirrors `verify_update`: the five checks run in TUF order
    and the FIRST failing check decides the rejection reason (fail closed).
    The role loops of the .spl are unrolled over the four fixed roles. -/
def verifyUpdate (root ts snap tgt : RoleMeta) (cur : Current) (now : Nat) :
    Outcome :=
  if keysTrusted root (rootTrustedSet root) && keysTrusted ts (rootTrustedSet root) &&
     keysTrusted snap (rootTrustedSet root) && keysTrusted tgt (rootTrustedSet root) then
    if verifyThreshold root && verifyThreshold ts &&
       verifyThreshold snap && verifyThreshold tgt then
      if checkFreshness root now && checkFreshness ts now &&
         checkFreshness snap now && checkFreshness tgt now then
        if rollbackGuard cur.root root.version && rollbackGuard cur.timestamp ts.version &&
           rollbackGuard cur.snapshot snap.version && rollbackGuard cur.targets tgt.version then
          if snapshotConsistent snap.recordedTargetsVersion tgt.version then
            .accepted
          else .snapshotMismatch
        else .rollback
      else .expired
    else .badThreshold
  else .untrustedKey

-- ============================================================
-- § 4  Acceptance implies every check passed (master extraction)
-- ============================================================

/-- Acceptance implies ALL five checks passed — the fail-closed pipeline has
    no path to `.accepted` that skips a check. -/
theorem accepted_checks {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    (h : verifyUpdate root ts snap tgt cur now = .accepted) :
    (keysTrusted root (rootTrustedSet root) && keysTrusted ts (rootTrustedSet root) &&
     keysTrusted snap (rootTrustedSet root) && keysTrusted tgt (rootTrustedSet root)) = true ∧
    (verifyThreshold root && verifyThreshold ts &&
     verifyThreshold snap && verifyThreshold tgt) = true ∧
    (checkFreshness root now && checkFreshness ts now &&
     checkFreshness snap now && checkFreshness tgt now) = true ∧
    (rollbackGuard cur.root root.version && rollbackGuard cur.timestamp ts.version &&
     rollbackGuard cur.snapshot snap.version && rollbackGuard cur.targets tgt.version) = true ∧
    snapshotConsistent snap.recordedTargetsVersion tgt.version = true := by
  unfold verifyUpdate at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      split at h
      · rename_i h3
        split at h
        · rename_i h4
          split at h
          · rename_i h5
            exact ⟨h1, h2, h3, h4, h5⟩
          · exact Outcome.noConfusion h
        · exact Outcome.noConfusion h
      · exact Outcome.noConfusion h
    · exact Outcome.noConfusion h
  · exact Outcome.noConfusion h

-- ============================================================
-- § 5  T1 — no rollback
-- ============================================================

/-- T1 — accepted_no_rollback:
    an accepted update NEVER carries any role version below the locally
    trusted current version — the TUF rollback defense holds for all four
    roles. -/
theorem accepted_no_rollback {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    (h : verifyUpdate root ts snap tgt cur now = .accepted) :
    cur.root ≤ root.version ∧ cur.timestamp ≤ ts.version ∧
    cur.snapshot ≤ snap.version ∧ cur.targets ≤ tgt.version := by
  obtain ⟨-, -, -, h4, -⟩ := accepted_checks h
  simp only [Bool.and_eq_true] at h4
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := h4
  exact ⟨of_decide_eq_true g1, of_decide_eq_true g2,
         of_decide_eq_true g3, of_decide_eq_true g4⟩

/-- T1 corollary — rollback_rejected:
    a targets metadata whose version is strictly below the current trusted
    targets version is NEVER accepted (a validly-signed but older replay is
    refused). -/
theorem rollback_rejected {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    (hroll : tgt.version < cur.targets) :
    verifyUpdate root ts snap tgt cur now ≠ .accepted := by
  intro hacc
  have hle := (accepted_no_rollback hacc).2.2.2
  omega

-- ============================================================
-- § 6  T2 — no freeze (expired metadata never accepted)
-- ============================================================

/-- T2 (positive form) — accepted metadata is fresh: `now` is within every
    role's `expires_at`. -/
theorem accepted_fresh {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    (h : verifyUpdate root ts snap tgt cur now = .accepted) :
    now ≤ root.expiresAt ∧ now ≤ ts.expiresAt ∧
    now ≤ snap.expiresAt ∧ now ≤ tgt.expiresAt := by
  obtain ⟨-, -, h3, -, -⟩ := accepted_checks h
  simp only [Bool.and_eq_true] at h3
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := h3
  exact ⟨of_decide_eq_true g1, of_decide_eq_true g2,
         of_decide_eq_true g3, of_decide_eq_true g4⟩

/-- T2 — expired_rejected:
    expired timestamp metadata (the freeze-attack detector role) is NEVER
    accepted.  By `accepted_fresh` the same holds for every role. -/
theorem expired_rejected {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    (hexp : ts.expiresAt < now) :
    verifyUpdate root ts snap tgt cur now ≠ .accepted := by
  intro hacc
  have hle := (accepted_fresh hacc).2.1
  omega

-- ============================================================
-- § 7  T3 — threshold + trusted keys (no single compromised key)
-- ============================================================

/-- Acceptance implies every role met its distinct-valid-signer threshold. -/
theorem accepted_thresholds {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    (h : verifyUpdate root ts snap tgt cur now = .accepted) :
    root.threshold ≤ countValidSigners root ∧ ts.threshold ≤ countValidSigners ts ∧
    snap.threshold ≤ countValidSigners snap ∧ tgt.threshold ≤ countValidSigners tgt := by
  obtain ⟨-, h2, -, -, -⟩ := accepted_checks h
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := h2
  exact ⟨of_decide_eq_true g1, of_decide_eq_true g2,
         of_decide_eq_true g3, of_decide_eq_true g4⟩

/-- `keysTrusted` unpacked: every presented signature key is in the set. -/
theorem keysTrusted_mem {m : RoleMeta} {trusted : List Nat}
    (h : keysTrusted m trusted = true) :
    ∀ k ∈ m.sigsPresent, k ∈ trusted := by
  intro k hk
  unfold keysTrusted at h
  rw [List.all_eq_true] at h
  exact List.contains_iff_mem.mp (h k hk)

/-- T3 (trust-anchor half) — accepted_keys_trusted:
    acceptance implies every presented signature on the targets role traces
    to root's trusted key set (root's own keys ++ delegated keys). -/
theorem accepted_keys_trusted {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    (h : verifyUpdate root ts snap tgt cur now = .accepted) :
    ∀ k ∈ tgt.sigsPresent, k ∈ rootTrustedSet root := by
  obtain ⟨h1, -, -, -, -⟩ := accepted_checks h
  simp only [Bool.and_eq_true] at h1
  exact keysTrusted_mem h1.2

/-- T3 corollary — untrusted_signer_rejected:
    if the targets metadata carries even one signature from a key outside
    root's trusted set, the update is NEVER accepted. -/
theorem untrusted_signer_rejected {root ts snap tgt : RoleMeta} {cur : Current} {now : Nat}
    {k : Nat} (hk : k ∈ tgt.sigsPresent) (hout : k ∉ rootTrustedSet root) :
    verifyUpdate root ts snap tgt cur now ≠ .accepted := by
  intro hacc
  exact hout (accepted_keys_trusted hacc k hk)

/-- Distinctness core: once `k0` is already seen, a signature list consisting
    only of `k0` contributes ZERO further valid signers. -/
theorem countValidAux_zero_of_seen {sigs signer seen : List Nat} {k0 : Nat}
    (hall : ∀ k ∈ sigs, k = k0) (hseen : k0 ∈ seen) :
    countValidAux sigs signer seen = 0 := by
  induction sigs generalizing seen with
  | nil => rfl
  | cons k rest ih =>
    have hk : k = k0 := hall k (by simp)
    subst hk
    have hs : seen.contains k = true := List.contains_iff_mem.mpr hseen
    unfold countValidAux
    rw [if_neg (by intro hc; rw [hc.2] at hs; exact Bool.noConfusion hs)]
    exact ih (fun x hx => hall x (by simp [hx])) hseen

/-- A signature list where every entry is the SAME key `k0` yields at most ONE
    distinct valid signer, no matter how many copies are presented. -/
theorem countValidAux_le_one_of_single {sigs signer seen : List Nat} {k0 : Nat}
    (hall : ∀ k ∈ sigs, k = k0) :
    countValidAux sigs signer seen ≤ 1 := by
  induction sigs generalizing seen with
  | nil => exact Nat.zero_le 1
  | cons k rest ih =>
    have hk : k = k0 := hall k (by simp)
    subst hk
    unfold countValidAux
    by_cases hcond : signer.contains k = true ∧ seen.contains k = false
    · rw [if_pos hcond]
      have h0 : countValidAux rest signer (k :: seen) = 0 :=
        countValidAux_zero_of_seen (fun x hx => hall x (by simp [hx])) (by simp)
      omega
    · rw [if_neg hcond]
      exact ih (fun x hx => hall x (by simp [hx]))

/-- With threshold ≥ 2, a role signed only by (copies of) one key can never
    meet its threshold. -/
theorem single_key_cannot_meet_threshold {m : RoleMeta} {k0 : Nat}
    (hth : 2 ≤ m.threshold) (hall : ∀ k ∈ m.sigsPresent, k = k0) :
    verifyThreshold m = false := by
  unfold verifyThreshold
  apply decide_eq_false
  intro hle
  have hone : countValidSigners m ≤ 1 :=
    countValidAux_le_one_of_single (signer := m.signerKeys) (seen := []) hall
  omega

/-- T3 — no_single_key_compromise:
    when the targets threshold is ≥ 2, an attacker holding ONE compromised
    key — presenting arbitrarily many signatures, all from that key — can
    NEVER get an update accepted.  Distinctness (the seen-list) makes replayed
    copies of one signature worthless. -/
theorem no_single_key_compromise {root ts snap tgt : RoleMeta} {cur : Current}
    {now : Nat} {k0 : Nat}
    (hth : 2 ≤ tgt.threshold) (hall : ∀ k ∈ tgt.sigsPresent, k = k0) :
    verifyUpdate root ts snap tgt cur now ≠ .accepted := by
  intro hacc
  obtain ⟨-, h2, -, -, -⟩ := accepted_checks hacc
  simp only [Bool.and_eq_true] at h2
  have hfalse := single_key_cannot_meet_threshold hth hall
  rw [h2.2] at hfalse
  exact Bool.noConfusion hfalse

-- ============================================================
-- § 8  T4 — snapshot consistency (anti mix-and-match)
-- ============================================================

/-- Acceptance implies snapshot pinned exactly the presented targets
    version. -/
theorem accepted_snapshot_consistent {root ts snap tgt : RoleMeta} {cur : Current}
    {now : Nat}
    (h : verifyUpdate root ts snap tgt cur now = .accepted) :
    snap.recordedTargetsVersion = tgt.version := by
  obtain ⟨-, -, -, -, h5⟩ := accepted_checks h
  unfold snapshotConsistent at h5
  exact eq_of_beq h5

/-- T4 — snapshot_mismatch_rejected:
    a targets file inconsistent with the snapshot's pinned targets version is
    NEVER accepted — an attacker cannot pair a fresh snapshot with a swapped
    or rolled-back targets metadata (anti mix-and-match). -/
theorem snapshot_mismatch_rejected {root ts snap tgt : RoleMeta} {cur : Current}
    {now : Nat}
    (hmix : snap.recordedTargetsVersion ≠ tgt.version) :
    verifyUpdate root ts snap tgt cur now ≠ .accepted := by
  intro hacc
  exact hmix (accepted_snapshot_consistent hacc)

-- Axiom audit (must report no sorryAx)
#print axioms accepted_checks
#print axioms accepted_no_rollback
#print axioms rollback_rejected
#print axioms accepted_fresh
#print axioms expired_rejected
#print axioms accepted_thresholds
#print axioms accepted_keys_trusted
#print axioms untrusted_signer_rejected
#print axioms no_single_key_compromise
#print axioms accepted_snapshot_consistent
#print axioms snapshot_mismatch_rejected

end OsEnforcement.Tuf
