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

def hasDataRace (exec : Execution) : Prop :=
  ∃ id1 id2 op1 op2,
    (id1, op1) ∈ exec.ops ∧
    (id2, op2) ∈ exec.ops ∧
    id1 ≠ id2 ∧
    conflicts op1 op2 ∧
    ¬happensBefore exec id1 id2 ∧
    ¬happensBefore exec id2 id1

def dataRaceFree (exec : Execution) : Prop :=
  ¬hasDataRace exec

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

theorem read_read_no_conflict (loc : LocationId) (tid1 tid2 : ThreadId) :
  ¬conflicts (MemoryOperation.Read loc tid1) (MemoryOperation.Read loc tid2) := by
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
  rcases hRace with ⟨id1, id2, op1, op2, h1, _, _, _, _, _⟩
  cases h1

/-- If an execution has no conflicting operation pairs, it is data-race free. -/
theorem drf_when_no_conflicts (exec : Execution)
    (hnoconf : ∀ id1 id2 op1 op2,
      (id1, op1) ∈ exec.ops →
      (id2, op2) ∈ exec.ops →
      id1 ≠ id2 →
      ¬conflicts op1 op2) :
    dataRaceFree exec := by
  intro hRace
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, hconf, _, _⟩
  exact (hnoconf id1 id2 op1 op2 h1 h2 hneq) hconf

theorem drf_two_reads_same_location
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    dataRaceFree
      { ops := [(id1, MemoryOperation.Read loc tid1), (id2, MemoryOperation.Read loc tid2)]
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
    exact read_read_no_conflict loc tid1 tid2
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact read_read_no_conflict loc tid2 tid1
  · rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    exact False.elim (hneq rfl)

theorem two_unordered_writes_same_location_race
    (id1 id2 : OperationId) (loc : LocationId) (tid1 tid2 : ThreadId)
    (hneq_ids : id1 ≠ id2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.Write loc tid1, MemoryOperation.Write loc tid2, ?_, ?_, hneq_ids, ?_, ?_, ?_⟩
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
    (hneq_ids : id1 ≠ id2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.Read loc tid1), (id2, MemoryOperation.Write loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.Read loc tid1, MemoryOperation.Write loc tid2, ?_, ?_, hneq_ids, ?_, ?_, ?_⟩
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
    (hneq_ids : id1 ≠ id2) :
    hasDataRace
      { ops := [(id1, MemoryOperation.Write loc tid1), (id2, MemoryOperation.Read loc tid2)]
      , programOrder := fun _ _ => False
      , synchronizesWith := fun _ _ => False } := by
  refine ⟨id1, id2, MemoryOperation.Write loc tid1, MemoryOperation.Read loc tid2, ?_, ?_, hneq_ids, ?_, ?_, ?_⟩
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
  rcases hRace with ⟨id1, id2, op1, op2, h1, h2, hneq, hconf, hnot12, hnot21⟩
  cases hordered id1 id2 op1 op2 h1 h2 hneq hconf with
  | inl hb12 => exact hnot12 hb12
  | inr hb21 => exact hnot21 hb21

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

theorem scDRF (exec : Execution) :
  dataRaceFree exec → ∃ (_ : SequentiallyConsistent exec), True := by
  intro _
  refine ⟨{ witness := fun a b => happensBefore exec a b, respectsProgramOrder := by intro a b h; exact Or.inl h, respectsSynchronizesWith := by intro a b h; exact Or.inr h }, trivial⟩

end MemoryModelDRF
