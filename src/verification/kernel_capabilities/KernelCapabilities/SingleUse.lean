/-
  KernelCapabilities.SingleUse — Pure state-machine model of the SimpleOS
  single-use (one-shot) capability ledger, and a sorry-free proof of the
  single-use-consumption invariant.

  Source of truth (P1 — 2026-07-27):
    src/os/kernel/ipc/cspace_spawn.spl   (class SingleUseLedger, arm/consume)

  Real semantics being modelled (cspace_spawn.spl lines 82-125)
  ============================================================
    `arm(token_id)`     : if `token_id` is ALREADY in `token_ids`, return false
                          and leave the ledger UNCHANGED (no re-arm — re-arming
                          would silently refund a spent one-shot capability).
                          Otherwise push it (used=false) and return true.
    `consume(token_id)` : if `token_id` is armed AND not yet used, mark it used
                          and return true (the one success). If armed and already
                          used, return false (replay guard). If never armed,
                          return false (fail closed).

  Modelling notes
  ===============
  The real ledger stores parallel `token_ids : [u64]` and `used : [bool]` arrays.
  A `token_id` present in `token_ids` is ARMED; its `used[i]` flag tells whether
  it has been CONSUMED. We model this with two lists of ids:
    - `armed`    : the set of armed token ids            (mirrors `token_ids`)
    - `consumed` : the subset that has been spent         (mirrors `used[i]=true`)
  A consumed id is never removed from `armed` (matching the real arrays), so
  `arm` on a consumed id sees it as already-armed and is a no-op — the "no
  re-arm refund" property. This module reuses ONLY core Lean 4 (no Mathlib),
  matching Basic.lean / Theorems.lean and the empty package manifest.

  Manual proof entry point (SPipe manual layer): the three headline theorems
    KernelCapabilities.single_use_consume_once   (SU1)
    KernelCapabilities.unarmed_consume_denied     (SU2)
    KernelCapabilities.no_reuse_after_consume     (SU3)
  Post-regeneration gate: `cd src/verification/kernel_capabilities && lake build`.
-/

namespace KernelCapabilities

-- ============================================================
-- § 1  The single-use ledger
-- ============================================================

/-- Single-use capability ledger.
    - `armed`    : token ids registered as one-shot (mirrors `token_ids`).
    - `consumed` : the armed ids that have already been spent (mirrors `used`). -/
structure Ledger where
  armed    : List Nat
  consumed : List Nat
  deriving Repr

/-- The empty ledger: nothing armed, nothing consumed. -/
def Ledger.empty : Ledger := { armed := [], consumed := [] }

/-- `arm l id` mirrors `SingleUseLedger.arm`.
    Returns `(false, l)` UNCHANGED when `id` is already armed (no re-arm refund),
    else `(true, …)` with `id` added to the armed set. -/
def Ledger.arm (l : Ledger) (id : Nat) : Bool × Ledger :=
  if l.armed.contains id then
    (false, l)
  else
    (true, { l with armed := id :: l.armed })

/-- `consume l id` mirrors `SingleUseLedger.consume`.
    Returns `(true, …)` — marking `id` consumed — iff `id` is armed and not yet
    consumed. Otherwise `(false, l)` unchanged: a replay of a consumed id and a
    never-armed id both fail closed. -/
def Ledger.consume (l : Ledger) (id : Nat) : Bool × Ledger :=
  if l.armed.contains id && !l.consumed.contains id then
    (true, { l with consumed := id :: l.consumed })
  else
    (false, l)

-- ============================================================
-- § 2  Membership / boolean helpers
-- ============================================================

/-- An id is contained in the list it is consed onto. -/
private theorem contains_cons_self (id : Nat) (xs : List Nat) :
    (id :: xs).contains id = true := by
  simp

-- ============================================================
-- § 3  Core operational lemmas about `consume` and `arm`
-- ============================================================

/-- `consume` succeeds exactly when the id is armed and not yet consumed. -/
theorem Ledger.consume_fst (l : Ledger) (id : Nat) :
    (l.consume id).1 = (l.armed.contains id && !l.consumed.contains id) := by
  unfold Ledger.consume
  split
  · rename_i h; exact h.symm
  · rename_i h; simp only [Bool.not_eq_true] at h; exact h.symm

/-- On a successful `consume`, the id is added to the consumed set. -/
theorem Ledger.consume_snd_of_ok (l : Ledger) (id : Nat)
    (hok : (l.armed.contains id && !l.consumed.contains id) = true) :
    (l.consume id).2 = { l with consumed := id :: l.consumed } := by
  unfold Ledger.consume
  rw [if_pos hok]

/-- `consume` fails closed whenever the id has already been consumed. -/
theorem Ledger.consume_false_of_consumed (l : Ledger) (id : Nat)
    (h : l.consumed.contains id = true) :
    (l.consume id).1 = false := by
  rw [Ledger.consume_fst, h]
  simp

/-- `arm` is a no-op on an already-armed id (no re-arm refund). -/
theorem Ledger.arm_noop_of_armed (l : Ledger) (id : Nat)
    (h : l.armed.contains id = true) :
    (l.arm id).2 = l := by
  unfold Ledger.arm
  rw [if_pos h]

-- ============================================================
-- § 4  The single-use invariant — SU1, SU2, SU3
-- ============================================================

/-- SU1 — single_use_consume_once:
    after a SUCCESSFUL `consume id`, a second `consume id` on the resulting
    ledger is denied. The one-shot is spendable exactly once. -/
theorem single_use_consume_once (l : Ledger) (id : Nat)
    (h : (l.consume id).1 = true) :
    ((l.consume id).2.consume id).1 = false := by
  have hok : (l.armed.contains id && !l.consumed.contains id) = true := by
    rw [Ledger.consume_fst] at h; exact h
  rw [Ledger.consume_snd_of_ok l id hok]
  apply Ledger.consume_false_of_consumed
  exact contains_cons_self id l.consumed

/-- SU2 — unarmed_consume_denied:
    `consume id` on an id that was never armed is denied (fail closed). -/
theorem unarmed_consume_denied (l : Ledger) (id : Nat)
    (h : l.armed.contains id = false) :
    (l.consume id).1 = false := by
  rw [Ledger.consume_fst, h]
  simp

/-- SU3 — no_reuse_after_consume:
    after a successful `consume id`, attempting to `arm id` again (which the real
    code refuses — no re-arm refund) leaves the consumed flag set, so a follow-up
    `consume id` is still denied. Models the "no re-arm refund" guarantee exactly:
    `arm` on the (armed, consumed) id is a no-op and does NOT clear the flag. -/
theorem no_reuse_after_consume (l : Ledger) (id : Nat)
    (h : (l.consume id).1 = true) :
    (((l.consume id).2.arm id).2.consume id).1 = false := by
  have hok : (l.armed.contains id && !l.consumed.contains id) = true := by
    rw [Ledger.consume_fst] at h; exact h
  have harmed : l.armed.contains id = true := (Bool.and_eq_true _ _).mp hok |>.1
  -- Step 1: after the successful consume, consumed gains `id`, armed unchanged.
  rw [Ledger.consume_snd_of_ok l id hok]
  -- Step 2: `arm id` on the post-consume ledger is a no-op (id already armed).
  rw [Ledger.arm_noop_of_armed { l with consumed := id :: l.consumed } id harmed]
  -- Step 3: consume is denied because `id` is still in the consumed set.
  apply Ledger.consume_false_of_consumed
  exact contains_cons_self id l.consumed

/-- Corollary: a never-armed id cannot be consumed even after any single `arm`
    that is itself refused — but the honest, code-faithful statement is SU2/SU3
    above. This restates SU3's fail-closed posture from the empty ledger. -/
theorem empty_ledger_consume_denied (id : Nat) :
    (Ledger.empty.consume id).1 = false := by
  apply unarmed_consume_denied
  rfl

end KernelCapabilities
