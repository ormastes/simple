/-!
# Exact DBFS commit/crash visibility boundary

This narrow bridge models the product's `DbfsTxn.commit` gate. A crash drops
all noncommitted or unflushed state; only a WAL-flushed successful commit is
recoverably visible.
-/

namespace DbStorage.TxnCommitExact

inductive Status where
  | active
  | committed
  | aborted
  deriving DecidableEq, Repr

structure Txn where
  walFlushed : Bool
  status : Status
  deriving DecidableEq, Repr

def commit (txn : Txn) : Option Txn :=
  if txn.walFlushed then some { txn with status := .committed } else none

def crashVisible (txn : Txn) : Bool :=
  txn.walFlushed && txn.status = .committed

theorem commit_requires_durable_wal (txn committed : Txn)
    (h : commit txn = some committed) : txn.walFlushed = true := by
  simp [commit] at h
  exact h.1

theorem successful_commit_recovers_visible (txn committed : Txn)
    (h : commit txn = some committed) : crashVisible committed = true := by
  simp [commit] at h
  obtain ⟨hflush, rfl⟩ := h
  simp [crashVisible, hflush]

theorem failed_unflushed_commit_not_visible (txn : Txn)
    (hflush : txn.walFlushed = false) :
    commit txn = none ∧ crashVisible txn = false := by
  simp [commit, crashVisible, hflush]

theorem crash_before_or_after_commit_atomic (txn : Txn) :
    (commit txn = none ∧ crashVisible txn = false) ∨
      ∃ committed, commit txn = some committed ∧ crashVisible committed = true := by
  cases h : txn.walFlushed
  · left
    simp [commit, crashVisible, h]
  · right
    refine ⟨{ txn with status := .committed }, ?_, ?_⟩
    · simp [commit, h]
    · simp [crashVisible, h]

/-- Composite FV2 root for durability, visibility, and crash atomicity. -/
theorem commit_refinement_bundle :
    (∀ txn committed : Txn, commit txn = some committed →
      txn.walFlushed = true) ∧
    (∀ txn committed : Txn, commit txn = some committed →
      crashVisible committed = true) ∧
    (∀ txn : Txn, txn.walFlushed = false →
      commit txn = none ∧ crashVisible txn = false) ∧
    (∀ txn : Txn,
      (commit txn = none ∧ crashVisible txn = false) ∨
        ∃ committed, commit txn = some committed ∧
          crashVisible committed = true) := by
  exact ⟨commit_requires_durable_wal, successful_commit_recovers_visible,
    failed_unflushed_commit_not_visible,
    crash_before_or_after_commit_atomic⟩

#print axioms commit_refinement_bundle

end DbStorage.TxnCommitExact
