namespace MirRegionFrame

abbrev Region := Nat
abbrev State (α : Type) := Region → α

inductive Op (α : Type) where
  | read (region : Region)
  | write (region : Region) (value : α)
  deriving Repr

def writtenRegions : List (Op α) → List Region
  | [] => []
  | Op.read _ :: rest => writtenRegions rest
  | Op.write region _ :: rest => region :: writtenRegions rest

def run : State α → List (Op α) → State α
  | state, [] => state
  | state, Op.read _ :: rest => run state rest
  | state, Op.write region value :: rest =>
      run (fun candidate => if candidate = region then value else state candidate) rest

theorem run_frame
    (state : State α)
    (operations : List (Op α))
    (region : Region)
    (outside : region ∉ writtenRegions operations) :
    run state operations region = state region := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest induction_hypothesis =>
      cases operation with
      | read read_region =>
          exact induction_hypothesis state outside
      | write written_region value =>
          simp only [writtenRegions, List.mem_cons, not_or] at outside
          simp only [run]
          rw [induction_hypothesis]
          simp [outside.1]
          exact outside.2

theorem written_region_reachable
    (state : State Nat)
    (region value : Nat) :
    run state [Op.write region value] region = value := by
  simp [run]

theorem read_is_frame
    (state : State α)
    (region observed : Region) :
    run state [Op.read observed] region = state region := by
  rfl

end MirRegionFrame
