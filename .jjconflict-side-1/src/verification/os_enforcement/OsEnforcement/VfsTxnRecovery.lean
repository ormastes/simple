/-
  OsEnforcement.VfsTxnRecovery — pure model of the SimpleOS VFS transaction
  recovery invariant (master plan §21.3): a VFS transaction recovers to EITHER
  its pre-state OR its committed state — never a torn intermediate (atomicity).

  Source of truth:
    src/os/port/sqlite/sqlite_vfs_contract.spl  (durability / atomicity contract)
    master plan §21.3 — "VFS transactions recover to either pre-state or
    committed state".

  Real semantics being modelled
  =============================
  A transaction carries the durable value BEFORE it started (`preState`), whether
  it reached its commit point (`committed`), and the value it would install
  (`pending`). Crash recovery is deterministic: if the transaction committed,
  recovery installs the pending (committed) value; otherwise it rolls back to the
  pre-state, discarding pending changes. There is no third outcome — recovery can
  never leave a half-applied intermediate. Core Lean 4 only (List/Nat/Bool, no
  Mathlib).

  Headline theorems (SPipe manual layer):
    OsEnforcement.recover_is_prestate_or_committed  (TXN1)
    OsEnforcement.uncommitted_rolls_back            (TXN2)
    OsEnforcement.committed_persists                (TXN3)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Model — transaction and deterministic recovery
-- ============================================================

/-- A VFS transaction: the durable value before it started, whether it committed,
    and the value it would install. -/
structure Txn where
  preState  : Nat
  committed : Bool
  pending   : Nat
  deriving Repr, DecidableEq

/-- The value a committed transaction installs. -/
def committedState (t : Txn) : Nat := t.pending

/-- Deterministic crash recovery: install the committed value if the transaction
    reached its commit point, otherwise roll back to the pre-state. -/
def recover (t : Txn) : Nat :=
  if t.committed then committedState t else t.preState

-- ============================================================
-- § 2  The recovery invariants — TXN1 .. TXN3
-- ============================================================

/-- TXN1 — recover_is_prestate_or_committed:
    recovery always lands on EITHER the pre-state OR the committed state; never a
    torn intermediate. -/
theorem recover_is_prestate_or_committed (t : Txn) :
    recover t = t.preState ∨ recover t = committedState t := by
  unfold recover
  split
  · right; rfl
  · left; rfl

/-- TXN2 — uncommitted_rolls_back:
    an uncommitted transaction recovers to exactly its pre-state — pending
    changes are discarded. -/
theorem uncommitted_rolls_back (t : Txn) (h : t.committed = false) :
    recover t = t.preState := by
  simp [recover, h]

/-- TXN3 — committed_persists:
    a committed transaction recovers to the committed state — durable once
    acknowledged. -/
theorem committed_persists (t : Txn) (h : t.committed = true) :
    recover t = committedState t := by
  simp [recover, h]

-- Axiom audit (must report no sorryAx)
#print axioms recover_is_prestate_or_committed
#print axioms committed_persists

end OsEnforcement
