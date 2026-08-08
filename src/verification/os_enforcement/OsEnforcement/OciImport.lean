/-
  OsEnforcement.OciImport — pure model of the SimpleOS "OCI at the edge"
  import adapter's fail-closed safety checks, with sorry-free proofs of the
  §6.3 import-safety invariants (master plan §6.3 / §21.3).

  Source of truth (FVT — 2026-07-27):
    src/os/services/container/oci_import.spl
      struct OciConfigInput / OciPolicy / OciImportResult
      oci_import_checked_ex(input, policy, check_traversal)
      The six §6.3 checks, fail-CLOSED, first failure decides the reason:
        (a) mount destination must not escape the container root
            (`dest_escapes` — ".." traversal / above-root)         ERR_TRAVERSAL
        (b) raw host bind mount denied unless allow_host_mounts     ERR_HOST_MOUNT
        (c) device node mount denied unless allow_devices           ERR_DEVICE
        (d) lifecycle hooks denied unless allow_hooks               ERR_HOOKS
        (e) declared unpack count/size bounded by policy            ERR_UNPACK
        (f) content digest required non-empty when require_digest   ERR_DIGEST
      On success: caps = intersection(config caps, policy ceiling) with every
      raw host-net token stripped (isolated network by default) — authority is
      never amplified.

  Modelling notes
  ===============
  Mount destinations are normalized component lists (`List Nat`) with the
  sentinel `DOTDOT = 0` standing for a ".." component; `destEscapes` mirrors
  the .spl's textual `dest.contains("..")` in this normalized model.
  Capability tokens are `Nat` atoms; the three raw host-net tokens of
  `is_host_net_cap` are three designated atoms.  `digestLen` models
  `input.digest.len()`; the check is presence (the .spl checks the digest is
  non-empty — actual content-hash comparison happens at unpack time, outside
  this adapter).  Fields the checks never read (image_ref, root_path,
  entrypoint, env, uid, gid, mem_budget) are elided; they are carried through
  to ContainerSpec untouched and carry no authority.  `importCheckedEx` keeps
  the .spl's `check_traversal` toggle (it exists so the spec layer can prove
  the check can FAIL), which is exactly what O3's deny-wins statement is
  about.  Core Lean 4 only (List/Nat/Bool), no Mathlib.

  Headline theorems (SPipe manual layer):
    OsEnforcement.Oci.accepted_no_traversal   (O1)
    OsEnforcement.Oci.accepted_digest_present (O2)
    OsEnforcement.Oci.deny_wins               (O3, via check_enable_monotone)
    OsEnforcement.Oci.accepted_isolated_net   (O4)
    OsEnforcement.Oci.accepted_caps_bounded   (O5)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement.Oci

-- ============================================================
-- § 1  Model structs (mirror OciConfigInput / OciPolicy)
-- ============================================================

/-- Sentinel component id for a ".." path component. -/
abbrev DOTDOT : Nat := 0

/-- OCI mount type token (mirrors the .spl's `mtype: text`). -/
inductive MType where
  | bind | device | tmpfs | volume | other
  deriving Repr, DecidableEq

/-- One mount from the OCI config (mirrors `OciMount`).  `srcIsHostPath`
    models `is_host_path(src)` — the source is an absolute host path. -/
structure Mount where
  srcIsHostPath : Bool
  dest          : List Nat  -- normalized destination components
  mtype         : MType
  deriving Repr

/-- The parsed OCI config (mirrors `OciConfigInput`, authority-free fields
    elided — see header). -/
structure Config where
  mounts       : List Mount
  caps         : List Nat
  hooksPresent : Bool
  digestLen    : Nat        -- models input.digest.len(); 0 = missing
  unpackCount  : Nat
  unpackSize   : Nat
  deriving Repr

/-- Import ceilings (mirrors `OciPolicy`).  All permissive flags default
    FALSE in the .spl's `oci_policy_default` (fail-closed). -/
structure ImportPolicy where
  allowHostMounts : Bool
  allowDevices    : Bool
  allowHooks      : Bool
  maxUnpackCount  : Nat
  maxUnpackSize   : Nat
  requireDigest   : Bool
  capCeiling      : List Nat
  deriving Repr

/-- Distinct rejection reason per §6.3 check (mirrors the ERR_* strings). -/
inductive Reason where
  | traversal | hostMount | device | hooks | unpack | digest
  deriving Repr, DecidableEq

/-- Import outcome: `accepted` carries the produced capability list
    (the caps field of the built ContainerSpec — the authority-bearing
    part). -/
inductive Outcome where
  | accepted (caps : List Nat)
  | rejected (r : Reason)
  deriving Repr, DecidableEq

-- ============================================================
-- § 2  Helpers (mirror the .spl helper functions)
-- ============================================================

/-- The three raw host-net capability atoms of `is_host_net_cap`
    ("cap.host_net" / "cap.net_host" / "cap.net_host_raw"). -/
abbrev CAP_HOST_NET     : Nat := 101
abbrev CAP_NET_HOST     : Nat := 102
abbrev CAP_NET_HOST_RAW : Nat := 103

/-- `isHostNetCap` mirrors `is_host_net_cap`. -/
def isHostNetCap (c : Nat) : Bool :=
  c == CAP_HOST_NET || c == CAP_NET_HOST || c == CAP_NET_HOST_RAW

/-- `destEscapes` mirrors `dest_escapes`: the destination contains a ".."
    component (normalized model of the .spl's textual contains("..")). -/
def destEscapes (dest : List Nat) : Bool := dest.contains DOTDOT

/-- `capsIntersectIsolated` mirrors `caps_intersect_isolated`: keep only caps
    present in BOTH the request and the policy ceiling, and strip every raw
    host-net token — the produced authority is never amplified and the
    default network is isolated. -/
def capsIntersectIsolated (requested ceiling : List Nat) : List Nat :=
  requested.filter (fun c => !isHostNetCap c && ceiling.contains c)

/-- Per-mount §6.3 checks (a)/(b)/(c), in .spl order, first failure wins. -/
def mountCheck (pol : ImportPolicy) (checkTraversal : Bool) (m : Mount) :
    Option Reason :=
  if checkTraversal = true ∧ destEscapes m.dest = true then some .traversal
  else if m.mtype = .bind ∧ m.srcIsHostPath = true ∧ pol.allowHostMounts = false then
    some .hostMount
  else if m.mtype = .device ∧ pol.allowDevices = false then some .device
  else none

/-- The .spl's `while m < mounts.len()` loop: first failing mount decides. -/
def mountsCheck (pol : ImportPolicy) (ct : Bool) : List Mount → Option Reason
  | [] => none
  | m :: rest =>
    match mountCheck pol ct m with
    | some r => some r
    | none   => mountsCheck pol ct rest

-- ============================================================
-- § 3  Core checked import (mirrors `oci_import_checked_ex`)
-- ============================================================

/-- `importCheckedEx` mirrors `oci_import_checked_ex`: checks (f), (d), (e)
    then the per-mount loop (a)/(b)/(c); on success builds the produced caps
    by ceiling-intersection with host-net stripped. -/
def importCheckedEx (cfg : Config) (pol : ImportPolicy) (checkTraversal : Bool) :
    Outcome :=
  if pol.requireDigest = true ∧ cfg.digestLen = 0 then .rejected .digest
  else if cfg.hooksPresent = true ∧ pol.allowHooks = false then .rejected .hooks
  else if pol.maxUnpackCount < cfg.unpackCount then .rejected .unpack
  else if pol.maxUnpackSize < cfg.unpackSize then .rejected .unpack
  else
    match mountsCheck pol checkTraversal cfg.mounts with
    | some r => .rejected r
    | none   => .accepted (capsIntersectIsolated cfg.caps pol.capCeiling)

/-- Production entry (mirrors `oci_import_checked`): traversal check ON. -/
def importChecked (cfg : Config) (pol : ImportPolicy) : Outcome :=
  importCheckedEx cfg pol true

-- ============================================================
-- § 4  Extraction lemmas
-- ============================================================

/-- A clean mount loop means every individual mount passed its checks. -/
theorem mountCheck_none_of_mountsCheck_none {pol : ImportPolicy} {ct : Bool}
    {ms : List Mount} (h : mountsCheck pol ct ms = none) :
    ∀ m ∈ ms, mountCheck pol ct m = none := by
  induction ms with
  | nil => intro m hm; cases hm
  | cons a rest ih =>
    intro m hm
    unfold mountsCheck at h
    split at h
    · exact nomatch h
    · rename_i heq
      cases hm with
      | head => exact heq
      | tail _ hm' => exact ih h m hm'

/-- Acceptance implies EVERY §6.3 check passed and the produced caps are
    exactly the isolated ceiling-intersection — the fail-closed pipeline has
    no path to `.accepted` that skips a check. -/
theorem acceptedEx_checks {cfg : Config} {pol : ImportPolicy} {ct : Bool}
    {caps : List Nat}
    (h : importCheckedEx cfg pol ct = .accepted caps) :
    ¬(pol.requireDigest = true ∧ cfg.digestLen = 0) ∧
    ¬(cfg.hooksPresent = true ∧ pol.allowHooks = false) ∧
    cfg.unpackCount ≤ pol.maxUnpackCount ∧
    cfg.unpackSize ≤ pol.maxUnpackSize ∧
    mountsCheck pol ct cfg.mounts = none ∧
    caps = capsIntersectIsolated cfg.caps pol.capCeiling := by
  unfold importCheckedEx at h
  split at h
  · exact Outcome.noConfusion h
  · rename_i h1
    split at h
    · exact Outcome.noConfusion h
    · rename_i h2
      split at h
      · exact Outcome.noConfusion h
      · rename_i h3
        split at h
        · exact Outcome.noConfusion h
        · rename_i h4
          split at h
          · exact Outcome.noConfusion h
          · rename_i heq
            injection h with hcaps
            exact ⟨h1, h2, Nat.le_of_not_lt h3, Nat.le_of_not_lt h4, heq,
                   hcaps.symm⟩

-- ============================================================
-- § 5  O1 — no path traversal in an accepted import
-- ============================================================

/-- O1 — accepted_no_traversal:
    in an accepted import, NO mount destination contains a ".." component —
    no layer entry path can escape the container root. -/
theorem accepted_no_traversal {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (h : importChecked cfg pol = .accepted caps) :
    ∀ m ∈ cfg.mounts, destEscapes m.dest = false := by
  obtain ⟨-, -, -, -, hmc, -⟩ := acceptedEx_checks h
  intro m hm
  have hone := mountCheck_none_of_mountsCheck_none hmc m hm
  unfold mountCheck at hone
  split at hone
  · exact nomatch hone
  · rename_i hc1
    cases he : destEscapes m.dest with
    | false => rfl
    | true  => exact absurd ⟨rfl, he⟩ hc1

/-- O1 corollary — the DOTDOT component is absent from every accepted mount
    destination. -/
theorem accepted_no_dotdot {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (h : importChecked cfg pol = .accepted caps) :
    ∀ m ∈ cfg.mounts, DOTDOT ∉ m.dest := by
  intro m hm hmem
  have hesc := accepted_no_traversal h m hm
  unfold destEscapes at hesc
  rw [List.contains_iff_mem.mpr hmem] at hesc
  exact Bool.noConfusion hesc

-- ============================================================
-- § 6  O2 — digest required means digest present
-- ============================================================

/-- O2 — accepted_digest_present:
    when the policy requires a content digest, an accepted import always has
    one (non-empty).  (The .spl adapter checks digest PRESENCE — per-layer
    content-hash comparison happens at unpack time, outside this edge
    adapter — so presence is exactly what is provable here.) -/
theorem accepted_digest_present {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (hreq : pol.requireDigest = true)
    (h : importChecked cfg pol = .accepted caps) :
    cfg.digestLen ≠ 0 := by
  obtain ⟨h1, -⟩ := acceptedEx_checks h
  intro h0
  exact h1 ⟨hreq, h0⟩

-- ============================================================
-- § 7  O3 — deny-wins: enabling a check never widens acceptance
-- ============================================================

/-- Turning the traversal check OFF can only make a passing mount keep
    passing: per-mount checks are monotone in the enabled-check set. -/
theorem mountCheck_off_none {pol : ImportPolicy} {m : Mount}
    (h : mountCheck pol true m = none) :
    mountCheck pol false m = none := by
  unfold mountCheck at h ⊢
  rw [if_neg (by intro hc; exact Bool.noConfusion hc.1)]
  split at h
  · exact nomatch h
  · exact h

/-- Loop form of `mountCheck_off_none`. -/
theorem mountsCheck_off_none {pol : ImportPolicy} {ms : List Mount}
    (h : mountsCheck pol true ms = none) :
    mountsCheck pol false ms = none := by
  induction ms with
  | nil => rfl
  | cons a rest ih =>
    unfold mountsCheck at h ⊢
    split at h
    · exact nomatch h
    · rename_i heq
      rw [mountCheck_off_none heq]
      exact ih h

/-- O3 (monotone form) — check_enable_monotone:
    anything accepted WITH the traversal check enabled is also accepted with
    it disabled, with identical produced caps — i.e. enabling a check only
    SHRINKS the accept set.  Adding a failing check can therefore never turn
    a rejection into an acceptance. -/
theorem check_enable_monotone {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (h : importCheckedEx cfg pol true = .accepted caps) :
    importCheckedEx cfg pol false = .accepted caps := by
  unfold importCheckedEx at h ⊢
  split at h
  · exact Outcome.noConfusion h
  · rename_i h1
    rw [if_neg h1]
    split at h
    · exact Outcome.noConfusion h
    · rename_i h2
      rw [if_neg h2]
      split at h
      · exact Outcome.noConfusion h
      · rename_i h3
        rw [if_neg h3]
        split at h
        · exact Outcome.noConfusion h
        · rename_i h4
          rw [if_neg h4]
          split at h
          · exact Outcome.noConfusion h
          · rename_i heq
            rw [mountsCheck_off_none heq]
            exact h

/-- O3 — deny_wins:
    an image the check-light pipeline already rejects is NEVER accepted by
    the pipeline with the additional (traversal) check enabled — rejection is
    monotone in the enabled-check set. -/
theorem deny_wins {cfg : Config} {pol : ImportPolicy} {r : Reason} {caps : List Nat}
    (hrej : importCheckedEx cfg pol false = .rejected r) :
    importCheckedEx cfg pol true ≠ .accepted caps := by
  intro hacc
  have hmono := check_enable_monotone hacc
  rw [hrej] at hmono
  exact Outcome.noConfusion hmono

-- ============================================================
-- § 8  O4/O5 — produced capability safety
-- ============================================================

/-- O4 — accepted_isolated_net:
    the produced capability set of an accepted import NEVER contains a raw
    host-net token — the default network is isolated. -/
theorem accepted_isolated_net {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (h : importChecked cfg pol = .accepted caps) :
    ∀ c ∈ caps, isHostNetCap c = false := by
  obtain ⟨-, -, -, -, -, hcaps⟩ := acceptedEx_checks h
  subst hcaps
  intro c hc
  unfold capsIntersectIsolated at hc
  rw [List.mem_filter] at hc
  have hb := hc.2
  rw [Bool.and_eq_true] at hb
  have hn := hb.1
  cases hi : isHostNetCap c with
  | false => rfl
  | true  => rw [hi] at hn; exact Bool.noConfusion hn

/-- O5 — accepted_caps_bounded (no amplification):
    every produced capability was BOTH requested by the config AND inside the
    policy ceiling — imported authority is an intersection, never amplified. -/
theorem accepted_caps_bounded {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (h : importChecked cfg pol = .accepted caps) :
    ∀ c ∈ caps, c ∈ cfg.caps ∧ c ∈ pol.capCeiling := by
  obtain ⟨-, -, -, -, -, hcaps⟩ := acceptedEx_checks h
  subst hcaps
  intro c hc
  unfold capsIntersectIsolated at hc
  rw [List.mem_filter] at hc
  have hb := hc.2
  rw [Bool.and_eq_true] at hb
  exact ⟨hc.1, List.contains_iff_mem.mp hb.2⟩

-- ============================================================
-- § 9  Remaining §6.3 checks — (b)/(c)/(d)/(e) hold on acceptance
-- ============================================================

/-- (c) — under a device-denying policy, an accepted import has no device
    mounts at all. -/
theorem accepted_no_unauthorized_device {cfg : Config} {pol : ImportPolicy}
    {caps : List Nat}
    (hd : pol.allowDevices = false)
    (h : importChecked cfg pol = .accepted caps) :
    ∀ m ∈ cfg.mounts, m.mtype ≠ .device := by
  obtain ⟨-, -, -, -, hmc, -⟩ := acceptedEx_checks h
  intro m hm hdev
  have hone := mountCheck_none_of_mountsCheck_none hmc m hm
  unfold mountCheck at hone
  split at hone
  · exact nomatch hone
  · split at hone
    · exact nomatch hone
    · split at hone
      · exact nomatch hone
      · rename_i hc3
        exact hc3 ⟨hdev, hd⟩

/-- (b) — under a host-mount-denying policy, an accepted import has no bind
    mount whose source is a raw host path. -/
theorem accepted_no_raw_host_mount {cfg : Config} {pol : ImportPolicy}
    {caps : List Nat}
    (hh : pol.allowHostMounts = false)
    (h : importChecked cfg pol = .accepted caps) :
    ∀ m ∈ cfg.mounts, ¬(m.mtype = .bind ∧ m.srcIsHostPath = true) := by
  obtain ⟨-, -, -, -, hmc, -⟩ := acceptedEx_checks h
  intro m hm hbind
  have hone := mountCheck_none_of_mountsCheck_none hmc m hm
  unfold mountCheck at hone
  split at hone
  · exact nomatch hone
  · split at hone
    · exact nomatch hone
    · rename_i hc2
      exact hc2 ⟨hbind.1, hbind.2, hh⟩

/-- (d) — under a hook-denying policy, an accepted import declared no
    lifecycle hooks. -/
theorem accepted_no_hooks {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (hh : pol.allowHooks = false)
    (h : importChecked cfg pol = .accepted caps) :
    cfg.hooksPresent = false := by
  obtain ⟨-, h2, -⟩ := acceptedEx_checks h
  cases hp : cfg.hooksPresent with
  | false => rfl
  | true  => exact absurd ⟨hp, hh⟩ h2

/-- (e) — an accepted import's declared unpack totals are within the policy
    bounds (resource-exhaustion defense). -/
theorem accepted_unpack_bounded {cfg : Config} {pol : ImportPolicy} {caps : List Nat}
    (h : importChecked cfg pol = .accepted caps) :
    cfg.unpackCount ≤ pol.maxUnpackCount ∧ cfg.unpackSize ≤ pol.maxUnpackSize := by
  obtain ⟨-, -, h3, h4, -⟩ := acceptedEx_checks h
  exact ⟨h3, h4⟩

-- Axiom audit (must report no sorryAx)
#print axioms mountCheck_none_of_mountsCheck_none
#print axioms acceptedEx_checks
#print axioms accepted_no_traversal
#print axioms accepted_no_dotdot
#print axioms accepted_digest_present
#print axioms check_enable_monotone
#print axioms deny_wins
#print axioms accepted_isolated_net
#print axioms accepted_caps_bounded
#print axioms accepted_no_unauthorized_device
#print axioms accepted_no_raw_host_mount
#print axioms accepted_no_hooks
#print axioms accepted_unpack_bounded

end OsEnforcement.Oci
