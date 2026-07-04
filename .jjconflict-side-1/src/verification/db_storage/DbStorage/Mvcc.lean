-- DbStorage.Mvcc -- Formal model of mvcc.spl (PostgreSQL HeapTupleSatisfiesMVCC).
--
-- Source fidelity (mvcc.spl):
--   MvccSnapshot: xmin, xmax (monotone txn-id bounds), active list.
--   mvcc_is_visible rules (exact mirror):
--     R1: xmin in active                                   -> NOT visible
--     R2: xmin >= snapshot.xmax                            -> NOT visible
--     R3: xmin < snapshot.xmin AND xmax == 0               -> VISIBLE
--     R4: xmax != 0 AND xmax in active                     -> VISIBLE
--     R5: xmax != 0 AND xmax < snapshot.xmax AND not active -> NOT visible
--     R6: default                                          -> VISIBLE
--
-- xmin = txn_id that inserted the tuple (0 = invalid).
-- xmax = txn_id that deleted the tuple (0 = not deleted).
-- snapshot.xmin = smallest txn_id active at snapshot time.
-- snapshot.xmax = next txn_id to be assigned (not yet started).

namespace DbStorage.Mvcc

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

structure MvccHeader : Type where
  xmin : Nat
  xmax : Nat
  deriving DecidableEq, Repr

structure MvccTuple : Type where
  header : MvccHeader
  data   : Nat
  deriving Repr

structure MvccSnapshot : Type where
  xmin   : Nat
  xmax   : Nat
  active : List Nat
  deriving Repr

def MvccSnapshot.isTxnActive (s : MvccSnapshot) (txn_id : Nat) : Bool :=
  s.active.contains txn_id

-- ---------------------------------------------------------------------------
-- Visibility (direct mirror of mvcc_is_visible in mvcc.spl)
-- ---------------------------------------------------------------------------

def isVisible (t : MvccTuple) (s : MvccSnapshot) : Bool :=
  let xmin := t.header.xmin
  let xmax := t.header.xmax
  if s.isTxnActive xmin then false
  else if xmin >= s.xmax then false
  else if xmin < s.xmin && xmax == 0 then true
  else if xmax != 0 && s.isTxnActive xmax then true
  else if xmax != 0 && xmax < s.xmax && !s.isTxnActive xmax then false
  else true

-- ---------------------------------------------------------------------------
-- Abstract version record for T5/T6 proofs
-- ---------------------------------------------------------------------------

structure Version : Type where
  tuple     : MvccTuple
  commit_ts : Nat
  del_ts    : Nat
  deriving Repr

/-- Abstract snapshot-sees predicate:
    - tuple was inserted by a committed txn before the snapshot
      (commit_ts < xmax, not in active set)
    - tuple was not deleted before the snapshot
      (del_ts = 0, or del_ts >= xmax, or del_ts still active) -/
def snapshotSees (v : Version) (s : MvccSnapshot) : Prop :=
  v.commit_ts < s.xmax ∧
  !(s.active.contains v.commit_ts) ∧
  (v.del_ts = 0 ∨ v.del_ts ≥ s.xmax ∨ s.active.contains v.del_ts)

end DbStorage.Mvcc
