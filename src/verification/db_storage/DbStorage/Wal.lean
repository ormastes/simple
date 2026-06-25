-- DbStorage.Wal -- Formal model of SharedWal (wal.spl) and DbfsTxn (txn.spl).
--
-- Source fidelity (shared/wal.spl):
--   next_lsn starts at 1; append increments then records.
--   flush_wal sets durable_lsn = last entry's lsn (if non-empty).
--   flushed_lsn() returns durable_lsn (added 2026-06-11, E5).
--
-- Source fidelity (txn.spl D4 write protocol):
--   Steps: Data -> MetadataPrivate -> WalAppend -> WalFlush -> PublishRoot -> Commit
--   commit() fails if not wal_flushed.
--
-- E5 fix (2026-06-11): FINDING-T4 resolved.
--   pager.write_page now takes (page_lsn, wal_flushed_lsn) and enforces:
--   if page_lsn > 0 and wal_flushed_lsn < page_lsn -> Err.
--   WAL-before-data is now enforced at BOTH the D4 protocol level AND
--   the pager layer.
--   Reference: src/lib/nogc_sync_mut/db/dbfs_engine/pager.spl (write_page).

namespace DbStorage.Wal

-- WAL_RECORD_DATA=1, META=2, COMMIT=3, ABORT=4
-- Note: `meta` is a Lean 4 reserved keyword; we use `metaRec` for the META record type.
inductive RecordType where
  | data
  | metaRec
  | commit
  | abort
  deriving DecidableEq, BEq, Repr

instance : LawfulBEq RecordType where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a}         := by cases a <;> decide

structure WalEntry where
  lsn      : Nat
  txn_id   : Nat
  rec_type : RecordType
  deriving Repr

structure WalState where
  entries     : List WalEntry
  next_lsn    : Nat
  durable_lsn : Nat
  deriving Repr

def WalState.empty : WalState :=
  ⟨[], 1, 0⟩

-- Append: assign lsn = next_lsn, increment, append entry.
def walAppend (w : WalState) (txn_id : Nat) (rt : RecordType) : WalState × Nat :=
  let lsn  := w.next_lsn
  let e    := WalEntry.mk lsn txn_id rt
  let w'   := WalState.mk (w.entries ++ [e]) (w.next_lsn + 1) w.durable_lsn
  (w', lsn)

-- Flush: advance durable_lsn to the last appended LSN.
def walFlush (w : WalState) : WalState :=
  match w.entries.getLast? with
  | none   => w
  | some e => WalState.mk w.entries w.next_lsn e.lsn

-- D4 transaction status
inductive TxnStatus where
  | active
  | committed
  | aborted
  deriving DecidableEq, Repr

structure TxnState where
  txn_id         : Nat
  wal_appended   : Bool
  wal_flushed    : Bool
  root_published : Bool
  status         : TxnStatus
  deriving Repr

def TxnState.initial (id : Nat) : TxnState :=
  ⟨id, false, false, false, .active⟩

def txnAppendWal (t : TxnState) : TxnState :=
  { t with wal_appended := true }

def txnFlushWal (t : TxnState) : Option TxnState :=
  if t.wal_appended then some { t with wal_flushed := true } else none

def txnPublishRoot (t : TxnState) : Option TxnState :=
  if t.wal_flushed then some { t with root_published := true } else none

def txnCommit (t : TxnState) : Option TxnState :=
  if t.wal_flushed then some { t with status := .committed } else none

def txnAbort (t : TxnState) : TxnState :=
  { t with status := .aborted }

-- LSN lemmas
theorem append_lsn_eq_next (w : WalState) (txn_id : Nat) (rt : RecordType) :
    (walAppend w txn_id rt).2 = w.next_lsn := by
  simp [walAppend]

theorem append_next_lsn_succ (w : WalState) (txn_id : Nat) (rt : RecordType) :
    (walAppend w txn_id rt).1.next_lsn = w.next_lsn + 1 := by
  simp [walAppend]

theorem append_lsn_greatest (w : WalState) (txn_id : Nat) (rt : RecordType)
    (hinv : ∀ e ∈ w.entries, e.lsn < w.next_lsn) :
    ∀ e ∈ w.entries, e.lsn < (walAppend w txn_id rt).2 := by
  intro e he
  simp [walAppend]
  exact hinv e he

-- ===========================================================================
-- Pager model (E5 — WAL-before-data at pager layer, 2026-06-11)
-- ===========================================================================

-- flushed_lsn: accessor mirroring SharedWal.flushed_lsn() (= durable_lsn).
def walFlushedLsn (w : WalState) : Nat := w.durable_lsn

-- writePage: models pager.write_page gate.
--   Returns true (success) iff page_lsn = 0 OR wal_flushed_lsn >= page_lsn.
def writePageOk (page_lsn : Nat) (wal_flushed_lsn : Nat) : Bool :=
  page_lsn == 0 || wal_flushed_lsn ≥ page_lsn

end DbStorage.Wal
