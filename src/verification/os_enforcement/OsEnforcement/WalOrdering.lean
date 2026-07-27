/-
  OsEnforcement.WalOrdering — pure model of the SimpleOS / SQLite-VFS
  write-ahead-log ordering rule (master plan §8.5 / §15 / §21), and a sorry-free
  proof of the WAL-first durability invariant: a log record must reach durable
  storage BEFORE the corresponding data-page change is considered durable
  (the PostgreSQL/SQLite WAL-first rule).

  Source of truth:
    src/os/port/sqlite/sqlite_vfs_contract.spl  (durability contract)
    master plan §21.3 — "WAL commit implies required flush ordering".

  Real semantics being modelled
  =============================
  A write-ahead log is an ordered stream of events:
    * LogWrite p  — append a log record describing a change to page `p`
    * LogFlush    — fsync: every pending log record becomes durable
    * DataWrite p — write the data page `p` back to the main file; it may be
                    "counted durable" ONLY if its log record was already flushed
    * Commit      — mark the transaction committed (well-formed only after the
                    log records for all its pages have been flushed).

  We track three sets on the WAL state: `logged` (records appended since the last
  flush), `flushed` (records that reached durable storage), and `durable` (data
  pages acknowledged durable). The step function is where the WAL-first rule is
  enforced: a DataWrite is counted durable ONLY when the page is already in
  `flushed`; otherwise the data change is silently dropped (torn/lost-log crash
  safety). Core Lean 4 only (List/Nat/Bool, no Mathlib).

  Headline theorems (SPipe manual layer):
    OsEnforcement.wal_before_data              (WAL1)
    OsEnforcement.unflushed_data_not_durable   (WAL2)
    OsEnforcement.commit_implies_flush         (WAL3)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Model — WAL events and the enforcing step function
-- ============================================================

/-- One write-ahead-log event. -/
inductive WalEvent where
  | logWrite  : Nat → WalEvent
  | logFlush  : WalEvent
  | dataWrite : Nat → WalEvent
  | commit    : WalEvent
  deriving Repr, DecidableEq

/-- WAL state: log records appended since the last flush (`logged`), records that
    reached durable storage (`flushed`), and data pages acknowledged durable
    (`durable`). -/
structure WalState where
  logged  : List Nat
  flushed : List Nat
  durable : List Nat
  deriving Repr

/-- The empty WAL: nothing logged, flushed, or durable. -/
def WalState.empty : WalState := { logged := [], flushed := [], durable := [] }

/-- The WAL-first enforcing transition. A DataWrite is counted durable ONLY when
    its page already appears in `flushed` (log record already fsynced); otherwise
    the data change is NOT acknowledged — the crash-safety rule. -/
def step (s : WalState) (e : WalEvent) : WalState :=
  match e with
  | .logWrite p  => { s with logged := s.logged ++ [p] }
  | .logFlush    => { s with flushed := s.flushed ++ s.logged, logged := [] }
  | .dataWrite p =>
      if s.flushed.contains p then { s with durable := s.durable ++ [p] } else s
  | .commit      => s

/-- Replay an ordered event list from a starting state (the model's `append`). -/
def run (s : WalState) : List WalEvent → WalState
  | []      => s
  | e :: es => run (step s e) es

/-- Durability well-formedness: every data page counted durable has its log
    record flushed. This is exactly the WAL-first invariant. -/
def durable_ok (s : WalState) : Prop := ∀ p, p ∈ s.durable → p ∈ s.flushed

-- ============================================================
-- § 2  The step function preserves the WAL-first invariant
-- ============================================================

/-- A DataWrite whose page is already flushed appends that page to `durable`. -/
theorem step_dataWrite_mem (s : WalState) (q : Nat) (hc : q ∈ s.flushed) :
    step s (.dataWrite q) = { s with durable := s.durable ++ [q] } := by
  simp only [step]
  split
  · rfl
  · rename_i hcond
    exact absurd (List.contains_iff_mem.mpr hc) hcond

/-- A DataWrite whose page is NOT flushed leaves the state unchanged. -/
theorem step_dataWrite_not_mem (s : WalState) (q : Nat) (hc : ¬ q ∈ s.flushed) :
    step s (.dataWrite q) = s := by
  simp only [step]
  split
  · rename_i hcond
    exact absurd (List.contains_iff_mem.mp hcond) hc
  · rfl

/-- A single WAL transition preserves `durable_ok`. -/
theorem durable_ok_step (s : WalState) (e : WalEvent) (h : durable_ok s) :
    durable_ok (step s e) := by
  intro p hp
  cases e with
  | logWrite q =>
      -- flushed and durable unchanged
      simp only [step] at hp ⊢
      exact h p hp
  | logFlush =>
      -- flushed only grows (flushed ++ logged); durable unchanged
      simp only [step] at hp ⊢
      exact List.mem_append_left _ (h p hp)
  | dataWrite q =>
      by_cases hc : q ∈ s.flushed
      · rw [step_dataWrite_mem s q hc] at hp ⊢
        rcases List.mem_append.mp hp with h1 | h1
        · exact h p h1
        · rw [List.mem_singleton] at h1; subst h1; exact hc
      · rw [step_dataWrite_not_mem s q hc] at hp ⊢
        exact h p hp
  | commit =>
      simp only [step] at hp ⊢
      exact h p hp

/-- Replaying any event list preserves `durable_ok`. -/
theorem durable_ok_run (s : WalState) (es : List WalEvent) (h : durable_ok s) :
    durable_ok (run s es) := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (step s e) (durable_ok_step s e h)

-- ============================================================
-- § 3  The WAL ordering invariants — WAL1 .. WAL3
-- ============================================================

/-- WAL1 — wal_before_data:
    in a well-formed log built by `run` from the empty WAL, every data page
    counted durable has a flushed log record for the SAME page — the WAL-first
    ordering rule holds for any event sequence. -/
theorem wal_before_data (es : List WalEvent) :
    durable_ok (run WalState.empty es) := by
  apply durable_ok_run
  intro p hp
  simp [WalState.empty] at hp

/-- WAL2 — unflushed_data_not_durable:
    a DataWrite of a page whose log record was never flushed does NOT change the
    durable set — the data change is not acknowledged (torn/lost log ⇒ crash
    safety). -/
theorem unflushed_data_not_durable (s : WalState) (p : Nat)
    (h : s.flushed.contains p = false) :
    (step s (.dataWrite p)).durable = s.durable := by
  have hnm : ¬ p ∈ s.flushed := by
    intro hm
    rw [List.contains_iff_mem.mpr hm] at h
    exact Bool.noConfusion h
  rw [step_dataWrite_not_mem s p hnm]

-- ---- WAL3: commit requires all its pages flushed ----

/-- A commit is well-formed only if every page it commits already has its log
    record flushed. -/
def canCommit (s : WalState) (pages : List Nat) : Bool :=
  pages.all (fun p => s.flushed.contains p)

/-- Attempt to commit `pages`: succeeds (identity state) only when the required
    flush ordering holds; otherwise `none`. -/
def tryCommit (s : WalState) (pages : List Nat) : Option WalState :=
  if canCommit s pages then some s else none

/-- WAL3 — commit_implies_flush:
    if a commit of `pages` is well-formed (succeeds), then the log record for
    every committed page was already flushed — the §21 "WAL commit implies
    required flush ordering" invariant. -/
theorem commit_implies_flush (s : WalState) (pages : List Nat) (s' : WalState)
    (h : tryCommit s pages = some s') :
    ∀ p ∈ pages, p ∈ s.flushed := by
  intro p hp
  unfold tryCommit at h
  split at h
  · rename_i hc
    unfold canCommit at hc
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hc p hp)
  · simp at h

-- Axiom audit (must report no sorryAx)
#print axioms wal_before_data
#print axioms commit_implies_flush

end OsEnforcement
