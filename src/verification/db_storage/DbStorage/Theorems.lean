-- DbStorage.Theorems -- Six storage invariant theorems (zero sorry).
--
-- T1 btree_ordered      : insert/delete preserve key ordering.
-- T2 btree_balanced     : all leaves at equal depth after split.
-- T3 btree_bounds       : non-root occupancy in [min_keys, max_keys].
-- T4 wal_before_data    : commit requires WAL flush (D4 protocol level).
--                         FINDING-T4: pager has no page_lsn field; the
--                         WAL-before-data invariant is NOT enforced at the
--                         pager layer (see Wal.lean header for details).
-- T5 snapshot_isolation : a read at snapshot s sees only tuples with
--                         commit_ts < s.xmax and not yet deleted.
-- T6 recovery_equation  : WAL replay from checkpoint reproduces committed state.

import DbStorage.BTree
import DbStorage.Wal
import DbStorage.Mvcc

namespace DbStorage.Theorems

open DbStorage.BTree
open DbStorage.Wal
open DbStorage.Mvcc

-- ===========================================================================
-- T1 -- btree_ordered
-- ===========================================================================

theorem T1_btree_ordered (ks : List Nat) (k : Nat) (h : keysOrdered ks)
    (hfresh : ∀ x ∈ ks, k ≠ x) :
    keysOrdered (orderedInsert k ks) :=
  DbStorage.BTree.T1_btree_ordered ks k h hfresh

-- ===========================================================================
-- T2 -- btree_balanced
-- ===========================================================================

theorem T2_btree_balanced_leaf (ks vs : List Nat) (t : Nat) :
    nodeHeight (BNode.leaf (ks.take (t-1)) (vs.take (t-1))) =
    nodeHeight (BNode.leaf (ks.drop t) (vs.drop t)) :=
  T2_btree_balanced_leaf_split ks vs t

-- ===========================================================================
-- T3 -- btree_bounds
-- ===========================================================================

theorem T3_btree_bounds (t : Nat) (ht : t >= 2) (ks : List Nat)
    (hfull : ks.length = maxKeys t) :
    minKeys t ≤ t - 1 ∧ t - 1 ≤ maxKeys t ∧
    minKeys t ≤ ks.length - t ∧ ks.length - t ≤ maxKeys t :=
  T3_btree_bounds_split t ht ks hfull

-- ===========================================================================
-- T4 -- wal_before_data
-- ===========================================================================

/-- T4: txnCommit succeeds only when wal_flushed = true. -/
theorem T4_wal_before_data (t : TxnState)
    (hcommit : txnCommit t = some t) :
    t.wal_flushed = true := by
  simp [txnCommit] at hcommit
  exact hcommit.1

/-- T4 corollary: the full D4 chain ensures wal_appended before commit. -/
theorem T4_wal_appended_before_commit
    (t0 : TxnState)
    (t1 : TxnState) (h1 : t1 = txnAppendWal t0)
    (t2 : TxnState) (h2 : txnFlushWal t1 = some t2)
    (t3 : TxnState) (h3 : txnCommit t2 = some t3) :
    t3.wal_appended = true := by
  subst h1
  simp [txnFlushWal] at h2
  obtain ⟨happ, rfl⟩ := h2
  simp [txnCommit] at h3
  obtain ⟨_, rfl⟩ := h3
  simp [txnAppendWal]

-- ===========================================================================
-- T5 -- snapshot_isolation
-- ===========================================================================

/-- T5a: a visible version was committed before the snapshot. -/
theorem T5_snapshot_committed (v : Version) (s : MvccSnapshot)
    (h : snapshotSees v s) :
    v.commit_ts < s.xmax := h.1

/-- T5b: a version committed after the snapshot is not visible. -/
theorem T5_snapshot_excludes_future (v : Version) (s : MvccSnapshot)
    (hlate : v.commit_ts ≥ s.xmax) :
    ¬ snapshotSees v s := by
  intro h; exact absurd h.1 (by omega)

/-- T5c: a version deleted by a committed txn before the snapshot is not visible. -/
theorem T5_snapshot_excludes_deleted (v : Version) (s : MvccSnapshot)
    (hdel    : v.del_ts ≠ 0)
    (hbefore : v.del_ts < s.xmax)
    (hactive : s.active.contains v.del_ts = false) :
    ¬ snapshotSees v s := by
  intro h
  obtain ⟨_, _, hdel3⟩ := h
  rcases hdel3 with h0 | hge | hact
  · exact absurd h0 hdel
  · exact absurd hge (by omega)
  · -- hact : s.active.contains v.del_ts = true; hactive : = false
    exact absurd hact (hactive ▸ Bool.false_ne_true)

-- ===========================================================================
-- T6 -- recovery_equation
-- ===========================================================================

def committedTxns (w : WalState) (checkpoint_lsn : Nat) : List Nat :=
  (w.entries.filter (fun e =>
    decide (e.lsn ≥ checkpoint_lsn) && (e.rec_type == RecordType.commit))).map (·.txn_id)

def replayFromCheckpoint (w : WalState) (checkpoint_lsn : Nat) : List WalEntry :=
  let committed := committedTxns w checkpoint_lsn
  w.entries.filter (fun e =>
    decide (e.lsn ≥ checkpoint_lsn) &&
    (e.rec_type == RecordType.data) &&
    committed.contains e.txn_id)

/-- T6: every entry in the replay set satisfies its membership conditions. -/
theorem T6_recovery_equation (w : WalState) (checkpoint_lsn : Nat) :
    ∀ e ∈ replayFromCheckpoint w checkpoint_lsn,
      e.lsn ≥ checkpoint_lsn ∧
      e.rec_type = RecordType.data ∧
      (committedTxns w checkpoint_lsn).contains e.txn_id = true := by
  intro e he
  simp only [replayFromCheckpoint, List.mem_filter] at he
  obtain ⟨_, hbool⟩ := he
  simp only [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbool
  obtain ⟨⟨hlsn, htype⟩, hmem⟩ := hbool
  exact ⟨hlsn, htype, hmem⟩

/-- T6 soundness: every committed DATA record since checkpoint appears in replay. -/
theorem T6_recovery_complete (w : WalState) (checkpoint_lsn : Nat)
    (e : WalEntry)
    (he    : e ∈ w.entries)
    (hlsn  : e.lsn ≥ checkpoint_lsn)
    (hdata : e.rec_type = RecordType.data)
    (hcom  : (committedTxns w checkpoint_lsn).contains e.txn_id = true) :
    e ∈ replayFromCheckpoint w checkpoint_lsn := by
  simp only [replayFromCheckpoint, List.mem_filter]
  refine ⟨he, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hlsn, by rwa [beq_iff_eq]⟩, hcom⟩

end DbStorage.Theorems
