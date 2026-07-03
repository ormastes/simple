/-
  MemoryModelDRF.lean - Reduced-valid DRF / SC model
  
  This generator emits a small valid Lean model for memory operations,
  happens-before, conflicts, data-race freedom, and a lightweight
  sequential-consistency witness.
-/
namespace MemoryModelDRF
inductive ThreadId where
  | mk : Nat → ThreadId
deriving DecidableEq, Repr, Inhabited

inductive LocationId where
  | mk : Nat → LocationId
deriving DecidableEq, Repr, Inhabited

inductive OperationId where
  | mk : Nat → OperationId
deriving DecidableEq, Repr, Inhabited

inductive MemoryOrdering
  | Relaxed
  | Acquire
  | Release
  | SeqCst
deriving DecidableEq, Repr, BEq, Inhabited

inductive MemoryOperation
  | Read : LocationId → ThreadId → MemoryOperation
  | Write : LocationId → ThreadId → MemoryOperation
  | Fence : MemoryOrdering → ThreadId → MemoryOperation
  | LockAcquire : LocationId → ThreadId → MemoryOperation
  | LockRelease : LocationId → ThreadId → MemoryOperation
deriving Repr, Inhabited

def MemoryOperation.threadId : MemoryOperation → ThreadId
  | MemoryOperation.Read _ tid => tid
  | MemoryOperation.Write _ tid => tid
  | MemoryOperation.Fence _ tid => tid
  | MemoryOperation.LockAcquire _ tid => tid
  | MemoryOperation.LockRelease _ tid => tid

def MemoryOperation.locationId? : MemoryOperation → Option LocationId
  | MemoryOperation.Read loc _ => some loc
  | MemoryOperation.Write loc _ => some loc
  | MemoryOperation.LockAcquire loc _ => some loc
  | MemoryOperation.LockRelease loc _ => some loc
  | MemoryOperation.Fence _ _ => none

def MemoryOperation.isWrite : MemoryOperation → Bool
  | MemoryOperation.Write _ _ => true
  | MemoryOperation.LockRelease _ _ => true
  | _ => false

structure Execution where
  ops : List (OperationId × MemoryOperation)
  programOrder : OperationId → OperationId → Prop
  synchronizesWith : OperationId → OperationId → Prop
  deriving Inhabited

def happensBefore (exec : Execution) (a b : OperationId) : Prop :=
  exec.programOrder a b ∨ exec.synchronizesWith a b

def conflicts (op1 op2 : MemoryOperation) : Prop :=
  match op1.locationId?, op2.locationId? with
  | some loc1, some loc2 => loc1 = loc2 ∧ (op1.isWrite = true ∨ op2.isWrite = true)
  | _, _ => False

theorem conflicts_symmetric (op1 op2 : MemoryOperation) :
  conflicts op1 op2 → conflicts op2 op1 := by
  cases op1 <;> cases op2 <;>
    simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite, eq_comm, Or.comm]

def hasDataRace (exec : Execution) : Prop :=
  ∃ id1 id2 op1 op2,
    (id1, op1) ∈ exec.ops ∧
    (id2, op2) ∈ exec.ops ∧
    id1 ≠ id2 ∧
    op1.threadId ≠ op2.threadId ∧
    conflicts op1 op2 ∧
    ¬happensBefore exec id1 id2 ∧
    ¬happensBefore exec id2 id1

def dataRaceFree (exec : Execution) : Prop :=
  ¬hasDataRace exec

theorem hasDataRace_symmetric (exec : Execution) :
    hasDataRace exec →
    ∃ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops ∧
      (id2, op2) ∈ exec.ops ∧
      id1 ≠ id2 ∧
      op1.threadId ≠ op2.threadId ∧
      conflicts op1 op2 ∧
      ¬happensBefore exec id1 id2 ∧
      ¬happensBefore exec id2 id1 := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, hthread, hconf, hnot12, hnot21⟩
  exact ⟨id2, id1, op2, op1, h2, h1, fun h => hneq h.symm,
    fun h => hthread h.symm, conflicts_symmetric op1 op2 hconf, hnot21, hnot12⟩

theorem hasDataRace_has_conflict (exec : Execution) :
    hasDataRace exec →
    ∃ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops ∧
      (id2, op2) ∈ exec.ops ∧
      id1 ≠ id2 ∧
      conflicts op1 op2 := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, _, hconf, _, _⟩
  exact ⟨id1, id2, op1, op2, h1, h2, hneq, hconf⟩

theorem hasDataRace_unordered (exec : Execution) :
    hasDataRace exec →
    ∃ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops ∧
      (id2, op2) ∈ exec.ops ∧
      id1 ≠ id2 ∧
      ¬happensBefore exec id1 id2 ∧
      ¬happensBefore exec id2 id1 := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, _, _, hnot12, hnot21⟩
  exact ⟨id1, id2, op1, op2, h1, h2, hneq, hnot12, hnot21⟩

theorem hasDataRace_has_distinct_ops (exec : Execution) :
    hasDataRace exec →
    ∃ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops ∧
      (id2, op2) ∈ exec.ops ∧
      id1 ≠ id2 := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, _, _, _, _⟩
  exact ⟨id1, id2, op1, op2, h1, h2, hneq⟩

theorem hasDataRace_has_distinct_threads (exec : Execution) :
    hasDataRace exec →
    ∃ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops ∧
      (id2, op2) ∈ exec.ops ∧
      op1.threadId ≠ op2.threadId := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, _, hthread, _, _, _⟩
  exact ⟨id1, id2, op1, op2, h1, h2, hthread⟩

theorem drf_single_thread_execution (exec : Execution) (tid : ThreadId)
    (hsingle : ∀ id op, (id, op) ∈ exec.ops → op.threadId = tid) :
    dataRaceFree exec := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, _, hthread, _, _, _⟩
  exact hthread ((hsingle id1 op1 h1).trans (hsingle id2 op2 h2).symm)

structure SequentiallyConsistent (exec : Execution) where
  witness : OperationId → OperationId → Prop
  respectsProgramOrder : ∀ a b, exec.programOrder a b → witness a b
  respectsSynchronizesWith : ∀ a b, exec.synchronizesWith a b → witness a b

theorem read_is_not_write (loc : LocationId) (tid : ThreadId) :
  MemoryOperation.isWrite (MemoryOperation.Read loc tid) = false := by
  rfl

theorem write_is_write (loc : LocationId) (tid : ThreadId) :
  MemoryOperation.isWrite (MemoryOperation.Write loc tid) = true := by
  rfl

theorem lock_acquire_is_not_write (loc : LocationId) (tid : ThreadId) :
  MemoryOperation.isWrite (MemoryOperation.LockAcquire loc tid) = false := by
  rfl

theorem lock_release_is_write (loc : LocationId) (tid : ThreadId) :
  MemoryOperation.isWrite (MemoryOperation.LockRelease loc tid) = true := by
  rfl

theorem read_read_no_conflict (loc : LocationId) (tid1 tid2 : ThreadId) :
  ¬conflicts (MemoryOperation.Read loc tid1) (MemoryOperation.Read loc tid2) := by
  intro h
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at h

theorem read_read_any_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId) :
  ¬conflicts (MemoryOperation.Read loc1 tid1) (MemoryOperation.Read loc2 tid2) := by
  intro h
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at h

theorem fence_left_no_conflict (ord : MemoryOrdering) (tid : ThreadId) (op : MemoryOperation) :
  ¬conflicts (MemoryOperation.Fence ord tid) op := by
  cases op <;> simp [conflicts, MemoryOperation.locationId?]

theorem fence_right_no_conflict (op : MemoryOperation) (ord : MemoryOrdering) (tid : ThreadId) :
  ¬conflicts op (MemoryOperation.Fence ord tid) := by
  cases op <;> simp [conflicts, MemoryOperation.locationId?]

theorem write_write_same_location_conflicts (loc : LocationId) (tid1 tid2 : ThreadId) :
  conflicts (MemoryOperation.Write loc tid1) (MemoryOperation.Write loc tid2) := by
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite]

theorem read_write_same_location_conflicts (loc : LocationId) (tid1 tid2 : ThreadId) :
  conflicts (MemoryOperation.Read loc tid1) (MemoryOperation.Write loc tid2) := by
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite]

theorem write_read_same_location_conflicts (loc : LocationId) (tid1 tid2 : ThreadId) :
  conflicts (MemoryOperation.Write loc tid1) (MemoryOperation.Read loc tid2) := by
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite]

theorem write_write_different_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (h : loc1 ≠ loc2) :
  ¬conflicts (MemoryOperation.Write loc1 tid1) (MemoryOperation.Write loc2 tid2) := by
  intro hc
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at hc
  exact h hc

theorem read_write_different_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (h : loc1 ≠ loc2) :
  ¬conflicts (MemoryOperation.Read loc1 tid1) (MemoryOperation.Write loc2 tid2) := by
  intro hc
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at hc
  exact h hc

theorem write_read_different_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (h : loc1 ≠ loc2) :
  ¬conflicts (MemoryOperation.Write loc1 tid1) (MemoryOperation.Read loc2 tid2) := by
  intro hc
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at hc
  exact h hc

theorem lock_acquire_release_same_location_conflicts
    (loc : LocationId) (tid1 tid2 : ThreadId) :
  conflicts (MemoryOperation.LockAcquire loc tid1) (MemoryOperation.LockRelease loc tid2) := by
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite]

theorem lock_release_acquire_same_location_conflicts
    (loc : LocationId) (tid1 tid2 : ThreadId) :
  conflicts (MemoryOperation.LockRelease loc tid1) (MemoryOperation.LockAcquire loc tid2) := by
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite]

theorem lock_release_release_same_location_conflicts
    (loc : LocationId) (tid1 tid2 : ThreadId) :
  conflicts (MemoryOperation.LockRelease loc tid1) (MemoryOperation.LockRelease loc tid2) := by
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite]

theorem lock_acquire_acquire_same_location_no_conflict
    (loc : LocationId) (tid1 tid2 : ThreadId) :
  ¬conflicts (MemoryOperation.LockAcquire loc tid1) (MemoryOperation.LockAcquire loc tid2) := by
  intro h
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at h

theorem lock_acquire_acquire_any_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId) :
  ¬conflicts (MemoryOperation.LockAcquire loc1 tid1) (MemoryOperation.LockAcquire loc2 tid2) := by
  intro h
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at h

theorem lock_acquire_release_different_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (h : loc1 ≠ loc2) :
  ¬conflicts (MemoryOperation.LockAcquire loc1 tid1) (MemoryOperation.LockRelease loc2 tid2) := by
  intro hc
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at hc
  exact h hc

theorem lock_release_acquire_different_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (h : loc1 ≠ loc2) :
  ¬conflicts (MemoryOperation.LockRelease loc1 tid1) (MemoryOperation.LockAcquire loc2 tid2) := by
  intro hc
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at hc
  exact h hc

theorem lock_release_release_different_location_no_conflict
    (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (h : loc1 ≠ loc2) :
  ¬conflicts (MemoryOperation.LockRelease loc1 tid1) (MemoryOperation.LockRelease loc2 tid2) := by
  intro hc
  simp [conflicts, MemoryOperation.locationId?, MemoryOperation.isWrite] at hc
  exact h hc

theorem hb_program_order (exec : Execution) (a : OperationId) (b : OperationId) :
  exec.programOrder a b → happensBefore exec a b := by
  intro h
  exact Or.inl h

theorem hb_sync (exec : Execution) (a : OperationId) (b : OperationId) :
  exec.synchronizesWith a b → happensBefore exec a b := by
  intro h
  exact Or.inr h

theorem drf_empty_execution :
  dataRaceFree { ops := [], programOrder := fun _ _ => False, synchronizesWith := fun _ _ => False } := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, _, _, _, _, _, _⟩
  cases h1

theorem drf_single_op_execution (id : OperationId) (op : MemoryOperation) :
  dataRaceFree
    { ops := [(id, op)]
    , programOrder := fun _ _ => False
    , synchronizesWith := fun _ _ => False } := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, _, _, _, _⟩
  simp at h1 h2
  rcases h1 with ⟨rfl, rfl⟩
  rcases h2 with ⟨rfl, rfl⟩
  exact hneq rfl

/-- If an execution has no conflicting operation pairs, it is data-race free. -/
theorem drf_when_no_conflicts (exec : Execution)
    (hnoconf : ∀ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops →
      (id2, op2) ∈ exec.ops →
      id1 ≠ id2 →
      ¬conflicts op1 op2) :
    dataRaceFree exec := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, _, hconf, _, _⟩
  exact (hnoconf id1 id2 op1 op2 h1 h2 hneq) hconf

theorem drf_two_ops_no_conflict
    (id1 id2 : OperationId) (op1 op2 : MemoryOperation)
    (hneq_ids : id1 ≠ id2)
    (hnoconf : ¬conflicts op1 op2) :
    dataRaceFree
      { ops := [(id1, op1), (id2, op2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  apply drf_when_no_conflicts
  intro a b opa opb ha hb hneq
  simp at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact hnoconf
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact fun hconf => hnoconf (conflicts_symmetric _ _ hconf)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)

theorem drf_two_reads_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Read loc tid1), (id2, MemoryOperation.Read loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.Read loc tid1) (MemoryOperation.Read loc tid2)
    hneq_ids (read_read_no_conflict loc tid1 tid2)

theorem drf_two_reads_any_location
    (id1 id2 : OperationId) (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Read loc1 tid1), (id2, MemoryOperation.Read loc2 tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.Read loc1 tid1) (MemoryOperation.Read loc2 tid2)
    hneq_ids (read_read_any_location_no_conflict loc1 loc2 tid1 tid2)

theorem drf_two_writes_different_location
    (id1 id2 : OperationId) (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hloc : loc1 ≠ loc2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Write loc1 tid1), (id2, MemoryOperation.Write loc2 tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.Write loc1 tid1) (MemoryOperation.Write loc2 tid2)
    hneq_ids (write_write_different_location_no_conflict loc1 loc2 tid1 tid2 hloc)

theorem drf_two_read_write_different_location
    (id1 id2 : OperationId) (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hloc : loc1 ≠ loc2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Read loc1 tid1), (id2, MemoryOperation.Write loc2 tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.Read loc1 tid1) (MemoryOperation.Write loc2 tid2)
    hneq_ids (read_write_different_location_no_conflict loc1 loc2 tid1 tid2 hloc)

theorem drf_two_write_read_different_location
    (id1 id2 : OperationId) (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hloc : loc1 ≠ loc2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Write loc1 tid1), (id2, MemoryOperation.Read loc2 tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.Write loc1 tid1) (MemoryOperation.Read loc2 tid2)
    hneq_ids (write_read_different_location_no_conflict loc1 loc2 tid1 tid2 hloc)

theorem drf_two_lock_acquires_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockAcquire loc tid1), (id2, MemoryOperation.LockAcquire loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.LockAcquire loc tid1) (MemoryOperation.LockAcquire loc tid2)
    hneq_ids (lock_acquire_acquire_same_location_no_conflict loc tid1 tid2)

theorem drf_two_lock_acquires_any_location
    (id1 id2 : OperationId) (loc1 loc2 : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockAcquire loc1 tid1), (id2, MemoryOperation.LockAcquire loc2 tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.LockAcquire loc1 tid1) (MemoryOperation.LockAcquire loc2 tid2)
    hneq_ids (lock_acquire_acquire_any_location_no_conflict loc1 loc2 tid1 tid2)

theorem drf_two_ops_fence_left
    (id1 id2 : OperationId) (ord : MemoryOrdering) (tid : ThreadId)
    (other : MemoryOperation) (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Fence ord tid), (id2, other)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    (MemoryOperation.Fence ord tid) other hneq_ids
    (fence_left_no_conflict ord tid other)

theorem drf_two_ops_fence_right
    (id1 id2 : OperationId) (other : MemoryOperation)
    (ord : MemoryOrdering) (tid : ThreadId) (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, other), (id2, MemoryOperation.Fence ord tid)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_no_conflict id1 id2
    other (MemoryOperation.Fence ord tid) hneq_ids
    (fence_right_no_conflict other ord tid)

theorem two_unordered_writes_same_location_race
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hneq_threads : tid1 ≠ tid2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.Write loc tid1, MemoryOperation.Write loc tid2, ?_, ?_, hneq_ids, hneq_threads, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact write_write_same_location_conflicts loc tid1 tid2
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw

theorem two_unordered_read_write_same_location_race
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hneq_threads : tid1 ≠ tid2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.Read loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.Read loc tid1, MemoryOperation.Write loc tid2, ?_, ?_, hneq_ids, hneq_threads, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact read_write_same_location_conflicts loc tid1 tid2
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw

theorem two_unordered_write_read_same_location_race
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hneq_threads : tid1 ≠ tid2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Read loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.Write loc tid1, MemoryOperation.Read loc tid2, ?_, ?_, hneq_ids, hneq_threads, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact write_read_same_location_conflicts loc tid1 tid2
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw

theorem two_unordered_lock_release_acquire_same_location_race
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hneq_threads : tid1 ≠ tid2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.LockRelease loc tid1), (id2, MemoryOperation.LockAcquire loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.LockRelease loc tid1,
    MemoryOperation.LockAcquire loc tid2, ?_, ?_, hneq_ids, hneq_threads, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact lock_release_acquire_same_location_conflicts loc tid1 tid2
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw

theorem two_unordered_lock_acquire_release_same_location_race
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hneq_threads : tid1 ≠ tid2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.LockAcquire loc tid1), (id2, MemoryOperation.LockRelease loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.LockAcquire loc tid1,
    MemoryOperation.LockRelease loc tid2, ?_, ?_, hneq_ids, hneq_threads, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact lock_acquire_release_same_location_conflicts loc tid1 tid2
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw

theorem two_unordered_lock_releases_same_location_race
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) (hneq_threads : tid1 ≠ tid2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.LockRelease loc tid1), (id2, MemoryOperation.LockRelease loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.LockRelease loc tid1,
    MemoryOperation.LockRelease loc tid2, ?_, ?_, hneq_ids, hneq_threads, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact lock_release_release_same_location_conflicts loc tid1 tid2
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw
  · intro hb
    cases hb with
    | inl hpo => exact hpo
    | inr hsw => exact hsw

/-- If every conflicting pair of distinct operations is ordered by happens-before
    in at least one direction, the execution is data-race free. -/
theorem drf_when_conflicts_ordered (exec : Execution)
    (hordered : ∀ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops →
      (id2, op2) ∈ exec.ops →
      id1 ≠ id2 →
      conflicts op1 op2 →
      happensBefore exec id1 id2 ∨ happensBefore exec id2 id1) :
    dataRaceFree exec := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, _, hconf, hnot12, hnot21⟩
  cases hordered id1 id2 op1 op2 h1 h2 hneq hconf with
  | inl hb12 => exact hnot12 hb12
  | inr hb21 => exact hnot21 hb21

theorem drf_when_conflicts_same_thread_or_ordered (exec : Execution)
    (hcovered : ∀ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops →
      (id2, op2) ∈ exec.ops →
      id1 ≠ id2 →
      conflicts op1 op2 →
      op1.threadId = op2.threadId ∨
        happensBefore exec id1 id2 ∨ happensBefore exec id2 id1) :
    dataRaceFree exec := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, hthread, hconf, hnot12, hnot21⟩
  cases hcovered id1 id2 op1 op2 h1 h2 hneq hconf with
  | inl hsame => exact hthread hsame
  | inr hordered =>
      cases hordered with
      | inl hb12 => exact hnot12 hb12
      | inr hb21 => exact hnot21 hb21

theorem drf_when_conflicts_program_ordered (exec : Execution)
    (hordered : ∀ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops →
      (id2, op2) ∈ exec.ops →
      id1 ≠ id2 →
      conflicts op1 op2 →
      exec.programOrder id1 id2 ∨ exec.programOrder id2 id1) :
    dataRaceFree exec := by
  apply drf_when_conflicts_ordered
  intro id1 id2 op1 op2 h1 h2 hneq hconf
  cases hordered id1 id2 op1 op2 h1 h2 hneq hconf with
  | inl po12 => exact Or.inl (Or.inl po12)
  | inr po21 => exact Or.inr (Or.inl po21)

theorem drf_when_conflicts_synchronized (exec : Execution)
    (hordered : ∀ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops →
      (id2, op2) ∈ exec.ops →
      id1 ≠ id2 →
      conflicts op1 op2 →
      exec.synchronizesWith id1 id2 ∨ exec.synchronizesWith id2 id1) :
    dataRaceFree exec := by
  apply drf_when_conflicts_ordered
  intro id1 id2 op1 op2 h1 h2 hneq hconf
  cases hordered id1 id2 op1 op2 h1 h2 hneq hconf with
  | inl sw12 => exact Or.inl (Or.inr sw12)
  | inr sw21 => exact Or.inr (Or.inr sw21)

/-- Host/server lock and channel models usually expose program-order or
    synchronizes-with edges directly.  If every conflict is ordered by one of
    those primitive edges in either direction, the execution is data-race free. -/
theorem drf_when_conflicts_program_or_sync_ordered (exec : Execution)
    (hordered : ∀ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops →
      (id2, op2) ∈ exec.ops →
      id1 ≠ id2 →
      conflicts op1 op2 →
      exec.programOrder id1 id2 ∨ exec.synchronizesWith id1 id2 ∨
      exec.programOrder id2 id1 ∨ exec.synchronizesWith id2 id1) :
    dataRaceFree exec := by
  apply drf_when_conflicts_ordered
  intro id1 id2 op1 op2 h1 h2 hneq hconf
  cases hordered id1 id2 op1 op2 h1 h2 hneq hconf with
  | inl po12 => exact Or.inl (Or.inl po12)
  | inr rest =>
    cases rest with
    | inl sw12 => exact Or.inl (Or.inr sw12)
    | inr rest2 =>
      cases rest2 with
      | inl po21 => exact Or.inr (Or.inl po21)
      | inr sw21 => exact Or.inr (Or.inr sw21)

/-- Concrete lock/channel handoff shape: two distinct operations with a
    synchronizes-with edge between them cannot form a data race. -/
theorem drf_two_ops_synchronized
    (id1 id2 : OperationId) (op1 op2 : MemoryOperation)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, op1), (id2, op2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id1 ∧ b = id2 } := by
  apply drf_when_conflicts_ordered
  intro a b opa opb ha hb hneq _hconf
  simp at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inl (Or.inr ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)

theorem drf_two_ops_synchronized_reverse
    (id1 id2 : OperationId) (op1 op2 : MemoryOperation)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, op1), (id2, op2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id2 ∧ b = id1 } := by
  apply drf_when_conflicts_ordered
  intro a b opa opb ha hb hneq _hconf
  simp at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inl (Or.inr ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)

/-- Concrete single-thread handoff shape: two distinct operations ordered by
    program order cannot form a data race. -/
theorem drf_two_ops_program_ordered
    (id1 id2 : OperationId) (op1 op2 : MemoryOperation)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, op1), (id2, op2)]
      , programOrder := fun a b => a = id1 ∧ b = id2
      , synchronizesWith := fun _ _ => False } := by
  apply drf_when_conflicts_ordered
  intro a b opa opb ha hb hneq _hconf
  simp at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)

theorem drf_two_ops_program_ordered_reverse
    (id1 id2 : OperationId) (op1 op2 : MemoryOperation)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, op1), (id2, op2)]
      , programOrder := fun a b => a = id2 ∧ b = id1
      , synchronizesWith := fun _ _ => False } := by
  apply drf_when_conflicts_ordered
  intro a b opa opb ha hb hneq _hconf
  simp at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)

theorem drf_two_synchronized_writes_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id1 ∧ b = id2 } :=
  drf_two_ops_synchronized id1 id2
    (MemoryOperation.Write loc tid1) (MemoryOperation.Write loc tid2) hneq_ids

theorem drf_two_synchronized_read_write_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Read loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id1 ∧ b = id2 } :=
  drf_two_ops_synchronized id1 id2
    (MemoryOperation.Read loc tid1) (MemoryOperation.Write loc tid2) hneq_ids

theorem drf_two_synchronized_write_read_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Read loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id1 ∧ b = id2 } :=
  drf_two_ops_synchronized id1 id2
    (MemoryOperation.Write loc tid1) (MemoryOperation.Read loc tid2) hneq_ids

theorem drf_two_synchronized_lock_release_acquire_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockRelease loc tid1), (id2, MemoryOperation.LockAcquire loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id1 ∧ b = id2 } :=
  drf_two_ops_synchronized id1 id2
    (MemoryOperation.LockRelease loc tid1) (MemoryOperation.LockAcquire loc tid2) hneq_ids

theorem drf_two_synchronized_lock_acquire_release_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockAcquire loc tid1), (id2, MemoryOperation.LockRelease loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id1 ∧ b = id2 } :=
  drf_two_ops_synchronized id1 id2
    (MemoryOperation.LockAcquire loc tid1) (MemoryOperation.LockRelease loc tid2) hneq_ids

theorem drf_two_synchronized_lock_releases_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockRelease loc tid1), (id2, MemoryOperation.LockRelease loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun a b => a = id1 ∧ b = id2 } :=
  drf_two_ops_synchronized id1 id2
    (MemoryOperation.LockRelease loc tid1) (MemoryOperation.LockRelease loc tid2) hneq_ids

theorem drf_two_program_ordered_read_write_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Read loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun a b => a = id1 ∧ b = id2
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_program_ordered id1 id2
    (MemoryOperation.Read loc tid1) (MemoryOperation.Write loc tid2) hneq_ids

theorem drf_two_program_ordered_writes_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun a b => a = id1 ∧ b = id2
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_program_ordered id1 id2
    (MemoryOperation.Write loc tid1) (MemoryOperation.Write loc tid2) hneq_ids

theorem drf_two_program_ordered_write_read_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Read loc tid2)]
      , programOrder := fun a b => a = id1 ∧ b = id2
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_program_ordered id1 id2
    (MemoryOperation.Write loc tid1) (MemoryOperation.Read loc tid2) hneq_ids

theorem drf_two_program_ordered_lock_release_acquire_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockRelease loc tid1), (id2, MemoryOperation.LockAcquire loc tid2)]
      , programOrder := fun a b => a = id1 ∧ b = id2
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_program_ordered id1 id2
    (MemoryOperation.LockRelease loc tid1) (MemoryOperation.LockAcquire loc tid2) hneq_ids

theorem drf_two_program_ordered_lock_acquire_release_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockAcquire loc tid1), (id2, MemoryOperation.LockRelease loc tid2)]
      , programOrder := fun a b => a = id1 ∧ b = id2
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_program_ordered id1 id2
    (MemoryOperation.LockAcquire loc tid1) (MemoryOperation.LockRelease loc tid2) hneq_ids

theorem drf_two_program_ordered_lock_releases_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.LockRelease loc tid1), (id2, MemoryOperation.LockRelease loc tid2)]
      , programOrder := fun a b => a = id1 ∧ b = id2
      , synchronizesWith := fun _ _ => False } :=
  drf_two_ops_program_ordered id1 id2
    (MemoryOperation.LockRelease loc tid1) (MemoryOperation.LockRelease loc tid2) hneq_ids

theorem scDRF (exec : Execution) :
  dataRaceFree exec → ∃ (_ : SequentiallyConsistent exec), True := by
  intro _
  refine ⟨{ witness := fun a b => happensBefore exec a b, respectsProgramOrder := by intro a b h; exact Or.inl h, respectsSynchronizesWith := by intro a b h; exact Or.inr h }, trivial⟩

end MemoryModelDRF
