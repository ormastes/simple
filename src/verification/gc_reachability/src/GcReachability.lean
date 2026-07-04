/-
  GcReachability -- Tri-color mark-sweep safety for a mission-critical collector.

  Models an incremental tri-color garbage collector over an object graph:
    * every node has a fixed set of out-edges (`children`);
    * a `Coloring` assigns each node White / Gray / Black;
    * `markStep g col i` blackens a (gray) node `i` and grays its white children;
    * `sweep` reclaims exactly the white nodes.

  We prove the two SAFETY properties a mission-critical GC must guarantee:

    1. The strong tri-color invariant (`NoBlackWhite`: no black node points to a
       white node) is PRESERVED by every mark step.
    2. NO DANGLING AFTER COLLECT: under the invariant, a surviving (black) node
       never points to a reclaimed (white) node -- so no live object is left
       holding a pointer into freed memory.

  These are the seL4/SPARK-grade SAFETY theorems. The COMPLETENESS direction
  (marking terminates with every reachable node black) is stated as an open
  obligation in the gap matrix, NOT admitted here.

  All theorems are proved without `sorry` (std only, no Mathlib).
-/
namespace GcReachability

inductive Color
  | white
  | gray
  | black
deriving DecidableEq, Repr

-- Object graph: a total out-edge function over node ids.
structure Graph where
  children : Nat → List Nat

-- A coloring of the whole node space.
abbrev Coloring := Nat → Color

-- White-test as a decidable Bool (drives `sweep`'s filter).
def notWhite (c : Color) : Bool :=
  match c with
  | .white => false
  | _      => true

theorem notWhite_true_iff (c : Color) : notWhite c = true ↔ c ≠ Color.white := by
  cases c <;> simp [notWhite]

/-- Strong tri-color invariant: no black node has a white child. -/
def NoBlackWhite (g : Graph) (col : Coloring) : Prop :=
  ∀ i, col i = Color.black → ∀ c ∈ g.children i, col c ≠ Color.white

/-- One incremental mark step: blacken `i`, gray each of its white children. -/
def markStep (g : Graph) (col : Coloring) (i : Nat) : Coloring :=
  fun j =>
    if j = i then Color.black
    else if (col j = Color.white ∧ j ∈ g.children i) then Color.gray
    else col j

-- A mark step never turns any node white (colors only advance).
theorem markStep_never_whitens (g : Graph) (col : Coloring) (i j : Nat)
    (hj : col j ≠ Color.white) : markStep g col i j ≠ Color.white := by
  unfold markStep
  by_cases hji : j = i
  · simp [hji]
  · by_cases hg : (col j = Color.white ∧ j ∈ g.children i)
    · simp [hji, hg]
    · simp [hji, hg]; exact hj

-- A white child of the freshly-blackened node is grayed (hence not white).
theorem markStep_child_not_white (g : Graph) (col : Coloring) (i c : Nat)
    (hc : c ∈ g.children i) : markStep g col i c ≠ Color.white := by
  unfold markStep
  by_cases hci : c = i
  · simp [hci]
  · by_cases hw : col c = Color.white
    · simp [hci, hw, hc]
    · simp [hci]
      have : ¬ (col c = Color.white ∧ c ∈ g.children i) := by
        intro h; exact hw h.1
      simp [this]; exact hw

/-- SAFETY 1: every mark step preserves the strong tri-color invariant. -/
theorem markStep_preserves_invariant (g : Graph) (col : Coloring) (i : Nat)
    (hinv : NoBlackWhite g col) : NoBlackWhite g (markStep g col i) := by
  intro k hk c hc
  by_cases hki : k = i
  · -- k is the freshly blackened node: its children were grayed if white.
    subst hki
    exact markStep_child_not_white g col k c hc
  · -- k ≠ i and k is black under the new coloring ⇒ k was black before.
    have hkblack : col k = Color.black := by
      unfold markStep at hk
      by_cases hg : (col k = Color.white ∧ k ∈ g.children i)
      · simp [hki, hg] at hk
      · simpa [hki, hg] using hk
    have hcold : col c ≠ Color.white := hinv k hkblack c hc
    exact markStep_never_whitens g col i c hcold

/-- Sweep: keep exactly the non-white (surviving) nodes of a finite domain. -/
def sweep (col : Coloring) (dom : List Nat) : List Nat :=
  dom.filter (fun i => notWhite (col i))

theorem mem_sweep (col : Coloring) (dom : List Nat) (i : Nat) :
    i ∈ sweep col dom ↔ i ∈ dom ∧ col i ≠ Color.white := by
  unfold sweep
  rw [List.mem_filter]
  constructor
  · rintro ⟨hmem, hnw⟩; exact ⟨hmem, (notWhite_true_iff (col i)).mp hnw⟩
  · rintro ⟨hmem, hnw⟩; exact ⟨hmem, (notWhite_true_iff (col i)).mpr hnw⟩

-- Sweep reclaims every white node.
theorem sweep_reclaims_white (col : Coloring) (dom : List Nat) (i : Nat)
    (hw : col i = Color.white) : i ∉ sweep col dom := by
  intro hmem
  exact ((mem_sweep col dom i).mp hmem).2 hw

-- Sweep keeps every surviving (non-white) node of the domain.
theorem sweep_keeps_live (col : Coloring) (dom : List Nat) (i : Nat)
    (hmem : i ∈ dom) (hnw : col i ≠ Color.white) : i ∈ sweep col dom := by
  exact (mem_sweep col dom i).mpr ⟨hmem, hnw⟩

/-- SAFETY 2 (NO DANGLING AFTER COLLECT): under the tri-color invariant, every
    child of a surviving black node that is in the domain also survives the
    sweep. No live object is left pointing into reclaimed memory. -/
theorem no_dangling_after_sweep (g : Graph) (col : Coloring) (dom : List Nat)
    (hinv : NoBlackWhite g col)
    (i : Nat) (_hi : i ∈ sweep col dom) (hblack : col i = Color.black)
    (c : Nat) (hc : c ∈ g.children i) (hcdom : c ∈ dom) :
    c ∈ sweep col dom := by
  have hcnw : col c ≠ Color.white := hinv i hblack c hc
  exact sweep_keeps_live col dom c hcdom hcnw

end GcReachability
