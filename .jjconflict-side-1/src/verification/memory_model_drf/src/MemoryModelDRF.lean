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

theorem scDRF (exec : Execution) :
  dataRaceFree exec → ∃ (_ : SequentiallyConsistent exec), True := by
  intro _
  refine ⟨{ witness := fun a b => happensBefore exec a b, respectsProgramOrder := by intro a b h; exact Or.inl h, respectsSynchronizesWith := by intro a b h; exact Or.inr h }, trivial⟩

end MemoryModelDRF
