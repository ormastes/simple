/-! Exact bounded model of Scheduler wait/exit/collect lifecycle. -/
namespace ProcessLifecycle.ProcessWaitExact

inductive ChildState where | live | zombie | reaped
  deriving DecidableEq, Repr

structure State where
  child : ChildState
  parentBlocked : Bool
  exitCode : Int
  deriving DecidableEq, Repr

inductive WaitResult where
  | blocked
  | collected (status : Int)
  | noChild
  deriving DecidableEq, Repr

def wait (s : State) : WaitResult × State :=
  match s.child with
  | .live => (.blocked, { s with parentBlocked := true })
  | .zombie => (.collected s.exitCode,
      { s with child := .reaped, parentBlocked := false })
  | .reaped => (.noChild, s)

def exit (s : State) (code : Int) : State :=
  match s.child with
  | .live =>
      { s with
        child := .zombie
        parentBlocked := false
        exitCode := code }
  | _ => s

theorem live_wait_blocks (s : State) (h : s.child = .live) :
    (wait s).1 = .blocked ∧ (wait s).2.parentBlocked = true := by
  simp [wait, h]

theorem exit_wakes_and_publishes_zombie (s : State) (code : Int)
    (h : s.child = .live) :
    (exit s code).child = .zombie ∧
    (exit s code).parentBlocked = false ∧
    (exit s code).exitCode = code := by
  simp [exit, h]

theorem collect_returns_status_and_reaps (s : State)
    (h : s.child = .zombie) :
    (wait s).1 = .collected s.exitCode ∧
    (wait s).2.child = .reaped := by
  simp [wait, h]

theorem second_collect_has_no_child (s : State)
    (h : s.child = .zombie) :
    (wait (wait s).2).1 = .noChild := by
  simp [wait, h]

theorem process_wait_refinement_bundle :
    (∀ s : State, s.child = .live →
      (wait s).1 = .blocked ∧ (wait s).2.parentBlocked = true) ∧
    (∀ (s : State) (code : Int), s.child = .live →
      (exit s code).child = .zombie ∧
      (exit s code).parentBlocked = false ∧
      (exit s code).exitCode = code) ∧
    (∀ s : State, s.child = .zombie →
      (wait s).1 = .collected s.exitCode ∧
      (wait s).2.child = .reaped) ∧
    (∀ s : State, s.child = .zombie →
      (wait (wait s).2).1 = .noChild) := by
  exact ⟨live_wait_blocks, exit_wakes_and_publishes_zombie,
    collect_returns_status_and_reaps, second_collect_has_no_child⟩

#print axioms process_wait_refinement_bundle

end ProcessLifecycle.ProcessWaitExact
