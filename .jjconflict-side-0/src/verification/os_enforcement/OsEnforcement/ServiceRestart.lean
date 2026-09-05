/-
  OsEnforcement.ServiceRestart — pure model of the SimpleOS service-supervisor
  restart transition, and a sorry-free proof of the "restart drops stale grants"
  and "restart-storm bounded" invariants (master plan §21).

  Source of truth (FV3 — 2026-07-27):
    src/os/services/service_manifest.spl
      struct ServiceManifest { name, version, restart_policy,
        max_restarts, restart_count, granted_handles: [text], state, … }
      POLICY_NEVER / POLICY_ON_FAILURE / POLICY_ALWAYS
      should_restart(policy, restart_count, max_restarts) -> bool
        never => false;  otherwise restart_count < max_restarts
      on_restart(m) -> ServiceManifest
        §21: granted_handles CLEARED to [], restart_count += 1,
        state := Restarting; name/version copied unchanged by _clone.

  Real semantics being modelled
  =============================
  A restarted service must RE-ACQUIRE every device/secret grant from the broker
  after respawn — none carry across the restart (`on_restart` sets
  `granted_handles = []`).  The supervisor's `should_restart` bounds the restart
  storm: `never` never restarts, and the other policies deny once
  `restart_count` reaches `max_restarts`.

  Modelling notes
  ===============
  Grant ids are abstracted as `List Nat` (each an opaque handle id).  `name` and
  `version` are abstracted as `Nat` identities — only their preservation across a
  restart matters here.  The policy string constants become an inductive `Policy`.
  Core Lean 4 only (List/Nat/Bool, no Mathlib), matching the empty package
  manifest and the ContainerIsolation / DeviceGrant modules' idiom.

  Headline theorems (SPipe manual layer):
    OsEnforcement.restart_drops_stale_grants   (SR1)
    OsEnforcement.restart_denied_at_cap         (SR2, deny half)
    OsEnforcement.restart_allowed_below_cap     (SR2, allow half)
    OsEnforcement.never_never_restarts          (SR2, never policy)
    OsEnforcement.restart_preserves_identity    (SR3)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Model — restart policy and the service manifest
-- ============================================================

/-- The three restart policies (POLICY_* string constants in the source). -/
inductive Policy where
  | never
  | onFailure
  | always
  deriving DecidableEq, Repr

/-- A service manifest, restricted to the fields the restart invariant governs.
    `name`/`version` are opaque identity ids; `grantedHandles` are the device /
    secret grant ids currently HELD. -/
structure Service where
  name           : Nat
  version        : Nat
  grantedHandles : List Nat
  restartCount   : Nat
  maxRestarts    : Nat
  policy         : Policy
  deriving Repr

/-- `onRestart s` mirrors `on_restart(m)`: clear ALL granted handles, increment
    the restart count, and copy name/version unchanged. -/
def onRestart (s : Service) : Service :=
  { s with grantedHandles := [], restartCount := s.restartCount + 1 }

/-- `shouldRestart p c m` mirrors `should_restart(policy, restart_count,
    max_restarts)`: `never` is always false; otherwise allow iff `c < m`. -/
def shouldRestart (p : Policy) (c m : Nat) : Bool :=
  match p with
  | Policy.never     => false
  | Policy.onFailure => decide (c < m)
  | Policy.always    => decide (c < m)

-- ============================================================
-- § 2  SR1 — a restart retains NO stale grants
-- ============================================================

/-- SR1 — restart_drops_stale_grants:
    for every service, the post-restart manifest holds an EMPTY grant list,
    regardless of the pre-crash handle set (the §21 invariant). -/
theorem restart_drops_stale_grants (s : Service) :
    (onRestart s).grantedHandles = [] := rfl

-- ============================================================
-- § 3  SR2 — the restart storm is bounded
-- ============================================================

/-- SR2 (never) — never_never_restarts:
    a `never`-policy service never restarts, for any count / cap. -/
theorem never_never_restarts (c m : Nat) :
    shouldRestart Policy.never c m = false := rfl

/-- SR2 (deny) — restart_denied_at_cap:
    once `restart_count ≥ max_restarts`, NO policy restarts — the storm is
    capped (a `never` service was never restarting to begin with). -/
theorem restart_denied_at_cap (p : Policy) (c m : Nat) (h : m ≤ c) :
    shouldRestart p c m = false := by
  have hnlt : ¬ c < m := Nat.not_lt.mpr h
  cases p with
  | never     => rfl
  | onFailure => simp only [shouldRestart, decide_eq_false hnlt]
  | always    => simp only [shouldRestart, decide_eq_false hnlt]

/-- SR2 (allow) — restart_allowed_below_cap:
    below the cap, an `on_failure` / `always` service DOES restart. -/
theorem restart_allowed_below_cap (p : Policy) (c m : Nat)
    (hne : p ≠ Policy.never) (h : c < m) :
    shouldRestart p c m = true := by
  cases p with
  | never     => exact absurd rfl hne
  | onFailure => simp only [shouldRestart, decide_eq_true h]
  | always    => simp only [shouldRestart, decide_eq_true h]

-- ============================================================
-- § 4  SR3 — a restart preserves identity, clears only grants
-- ============================================================

/-- SR3 — restart_preserves_identity:
    `on_restart` keeps name and version unchanged and the ONLY state it clears is
    the granted-handle set (which becomes empty). -/
theorem restart_preserves_identity (s : Service) :
    (onRestart s).name = s.name
      ∧ (onRestart s).version = s.version
      ∧ (onRestart s).grantedHandles = [] :=
  ⟨rfl, rfl, rfl⟩

-- Axiom audit (must report no sorryAx)
#print axioms restart_drops_stale_grants
#print axioms restart_denied_at_cap

end OsEnforcement
