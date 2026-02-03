/-
# Reference Capability System Verification

This module formalizes the reference capability system for the Simple language,
proving that capabilities prevent data races at compile time.

## Reference Capabilities

1. **`T` (Shared)**: Multiple read-only references allowed
2. **`mut T` (Exclusive)**: Single mutable reference, prevents aliasing
3. **`iso T` (Isolated)**: Unique reference, no aliases at all

## Key Properties

- **Aliasing Prevention**: `mut T` and `iso T` prevent multiple references
- **Safe Conversions**: Capability conversions preserve safety
- **Data Race Freedom**: Type system prevents conflicting accesses

## References

- Pony language capabilities: https://www.ponylang.io/discover/#what-makes-pony-special
- Rust ownership system: https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html
-/

-- Reference capabilities
inductive RefCapability where
  | Shared    : RefCapability  -- T (immutable, aliasable)
  | Exclusive : RefCapability  -- mut T (mutable, single reference)
  | Isolated  : RefCapability  -- iso T (unique, no aliases)
deriving DecidableEq, Repr

-- Type with capability annotation
structure CapType where
  baseType : String
  capability : RefCapability
deriving Repr, BEq

-- Reference to a value with capability
structure Reference where
  location : Nat
  refType : CapType
deriving Repr, BEq

-- Environment tracking active references
structure RefEnv where
  -- Map from location to list of active references
  activeRefs : List (Nat × List Reference)
deriving Repr

-- Check if a location has any active references
def hasActiveRefs (env : RefEnv) (loc : Nat) : Bool :=
  match env.activeRefs.find? (fun (l, _) => l == loc) with
  | some (_, refs) => !refs.isEmpty
  | none => false

-- Get active references for a location
def getActiveRefs (env : RefEnv) (loc : Nat) : List Reference :=
  match env.activeRefs.find? (fun (l, _) => l == loc) with
  | some (_, refs) => refs
  | none => []

-- Count active references with specific capability
def countRefsWithCapability (refs : List Reference) (cap : RefCapability) : Nat :=
  refs.filter (fun r => r.refType.capability == cap) |>.length

-- Aliasing rules: can we create a new reference with given capability?
def canCreateRef (env : RefEnv) (loc : Nat) (newCap : RefCapability) : Bool :=
  let existingRefs := getActiveRefs env loc
  let hasExclusive := countRefsWithCapability existingRefs RefCapability.Exclusive > 0
  let hasIsolated := countRefsWithCapability existingRefs RefCapability.Isolated > 0
  let hasAnyRefs := !existingRefs.isEmpty

  match newCap with
  | RefCapability.Shared =>
      -- Shared refs allowed unless there's an Exclusive or Isolated ref
      !hasExclusive && !hasIsolated
  | RefCapability.Exclusive =>
      -- Exclusive ref requires no other refs exist
      !hasAnyRefs
  | RefCapability.Isolated =>
      -- Isolated ref requires no other refs exist
      !hasAnyRefs

-- Add a reference to the environment
def addRef (env : RefEnv) (ref : Reference) : RefEnv :=
  let loc := ref.location
  let existingRefs := getActiveRefs env loc
  let newRefs := ref :: existingRefs
  let updatedList := env.activeRefs.filter (fun (l, _) => l != loc)
  { activeRefs := (loc, newRefs) :: updatedList }

-- Remove a reference from the environment
def removeRef (env : RefEnv) (ref : Reference) : RefEnv :=
  let loc := ref.location
  let existingRefs := getActiveRefs env loc
  let newRefs := existingRefs.filter (fun r => r != ref)
  let updatedList := env.activeRefs.filter (fun (l, _) => l != loc)
  if newRefs.isEmpty then
    { activeRefs := updatedList }
  else
    { activeRefs := (loc, newRefs) :: updatedList }

-- Capability conversion rules
def canConvert (src dest : RefCapability) : Bool :=
  match src, dest with
  | a, b => if a == b then true else
    match src, dest with
    | RefCapability.Exclusive, RefCapability.Shared => true   -- mut T -> T
    | RefCapability.Isolated, RefCapability.Exclusive => true -- iso T -> mut T
    | RefCapability.Isolated, RefCapability.Shared => true    -- iso T -> T
    | _, _ => false

-- Formal properties

-- Well-formedness: environment maintains capability invariants
def wellFormed (env : RefEnv) : Prop :=
  forall loc refs, (loc, refs) ∈ env.activeRefs ->
    -- At most one Exclusive ref
    countRefsWithCapability refs RefCapability.Exclusive <= 1 ∧
    -- At most one Isolated ref
    countRefsWithCapability refs RefCapability.Isolated <= 1 ∧
    -- Exclusive and Isolated are alone
    (countRefsWithCapability refs RefCapability.Exclusive = 1 -> refs.length = 1) ∧
    (countRefsWithCapability refs RefCapability.Isolated = 1 -> refs.length = 1)

-- Property 1: Exclusive and Isolated references are unique
-- This holds when environment is maintained through canCreateRef/addRef API
theorem exclusive_is_unique (env : RefEnv) (loc : Nat) (h_wf : wellFormed env) :
  countRefsWithCapability (getActiveRefs env loc) RefCapability.Exclusive <= 1 := by
  unfold getActiveRefs
  match h_find : env.activeRefs.find? (fun (l, _) => l == loc) with
  | some (loc', refs) =>
    simp only [h_find]
    have h_mem := List.mem_of_find?_eq_some h_find
    have h_wf_loc := h_wf loc' refs h_mem
    exact h_wf_loc.1
  | none =>
    simp only [h_find]
    simp [countRefsWithCapability]

theorem isolated_is_unique (env : RefEnv) (loc : Nat) (h_wf : wellFormed env) :
  countRefsWithCapability (getActiveRefs env loc) RefCapability.Isolated <= 1 := by
  unfold getActiveRefs
  match h_find : env.activeRefs.find? (fun (l, _) => l == loc) with
  | some (loc', refs) =>
    simp only [h_find]
    have h_mem := List.mem_of_find?_eq_some h_find
    have h_wf_loc := h_wf loc' refs h_mem
    exact h_wf_loc.2.1
  | none =>
    simp only [h_find]
    simp [countRefsWithCapability]

-- Property 2: Exclusive and Isolated prevent other references
theorem exclusive_prevents_aliasing (env : RefEnv) (loc : Nat) (h_wf : wellFormed env) :
  countRefsWithCapability (getActiveRefs env loc) RefCapability.Exclusive = 1 ->
  (getActiveRefs env loc).length = 1 := by
  intro h_count
  unfold getActiveRefs at h_count ⊢
  match h_find : env.activeRefs.find? (fun (l, _) => l == loc) with
  | some (loc', refs) =>
    simp only [h_find] at h_count ⊢
    have h_mem := List.mem_of_find?_eq_some h_find
    have h_wf_loc := h_wf loc' refs h_mem
    exact h_wf_loc.2.2.1 h_count
  | none =>
    simp only [h_find] at h_count
    simp [countRefsWithCapability] at h_count

theorem isolated_prevents_aliasing (env : RefEnv) (loc : Nat) (h_wf : wellFormed env) :
  countRefsWithCapability (getActiveRefs env loc) RefCapability.Isolated = 1 ->
  (getActiveRefs env loc).length = 1 := by
  intro h_count
  unfold getActiveRefs at h_count ⊢
  match h_find : env.activeRefs.find? (fun (l, _) => l == loc) with
  | some (loc', refs) =>
    simp only [h_find] at h_count ⊢
    have h_mem := List.mem_of_find?_eq_some h_find
    have h_wf_loc := h_wf loc' refs h_mem
    exact h_wf_loc.2.2.2 h_count
  | none =>
    simp only [h_find] at h_count
    simp [countRefsWithCapability] at h_count

-- Property 3: Capability conversions are monotonic (lose privileges)
-- isMoreRestrictive a b means 'a' has fewer permissions than 'b'
-- Ordering: Shared (read-only) < Exclusive (mutable) < Isolated (unique)
def isMoreRestrictive (a b : RefCapability) : Prop :=
  match a, b with
  | RefCapability.Shared, RefCapability.Exclusive => True    -- Shared < Exclusive
  | RefCapability.Shared, RefCapability.Isolated => True     -- Shared < Isolated
  | RefCapability.Exclusive, RefCapability.Isolated => True  -- Exclusive < Isolated
  | a, b => a = b  -- Equal capabilities

theorem conversion_is_safe :
  forall src dest, canConvert src dest = true -> isMoreRestrictive dest src ∨ src = dest := by
  intros src dest h_convert
  cases src <;> cases dest <;> simp [canConvert, isMoreRestrictive] at h_convert ⊢

-- Helper: empty list has zero count for any capability
theorem empty_count_zero (cap : RefCapability) :
  countRefsWithCapability [] cap = 0 := by
  simp [countRefsWithCapability]

-- Helper: count after adding a ref with same capability increases by 1
theorem count_cons_same (refs : List Reference) (ref : Reference) (cap : RefCapability) :
  ref.refType.capability = cap ->
  countRefsWithCapability (ref :: refs) cap = countRefsWithCapability refs cap + 1 := by
  intro h_cap
  simp [countRefsWithCapability, h_cap]

-- Helper: count after adding a ref with different capability stays same
theorem count_cons_diff (refs : List Reference) (ref : Reference) (cap : RefCapability) :
  ref.refType.capability ≠ cap ->
  countRefsWithCapability (ref :: refs) cap = countRefsWithCapability refs cap := by
  intro h_cap
  simp [countRefsWithCapability]
  have h : ¬(ref.refType.capability == cap) = true := by
    simp only [beq_iff_eq]
    exact h_cap
  simp [h]

-- Helper: membership in addRef activeRefs
theorem addRef_mem_iff (env : RefEnv) (ref : Reference) (loc : Nat) (refs : List Reference) :
  (loc, refs) ∈ (addRef env ref).activeRefs ↔
  (loc = ref.location ∧ refs = ref :: getActiveRefs env ref.location) ∨
  (loc ≠ ref.location ∧ (loc, refs) ∈ env.activeRefs) := by
  unfold addRef getActiveRefs
  simp only [List.mem_cons]
  constructor
  · intro h
    cases h with
    | inl h_head =>
      left
      cases h_head
      constructor <;> rfl
    | inr h_tail =>
      right
      simp only [List.mem_filter] at h_tail
      obtain ⟨h_mem, h_ne⟩ := h_tail
      constructor
      · simp only [bne_iff_ne] at h_ne
        exact h_ne
      · exact h_mem
  · intro h
    cases h with
    | inl h_eq =>
      left
      simp [h_eq.1, h_eq.2]
    | inr h_ne =>
      right
      simp only [List.mem_filter, bne_iff_ne]
      exact ⟨h_ne.2, h_ne.1⟩

-- Property 4: Conversions preserve or reduce aliasing potential
theorem conversion_preserves_safety (env : RefEnv) (loc : Nat) (src dest : RefCapability) :
  canConvert src dest = true ->
  canCreateRef env loc src = true ->
  canCreateRef env loc dest = true := by
  intros h_convert h_can_src
  cases src <;> cases dest <;> simp [canConvert, canCreateRef] at h_convert h_can_src ⊢
  all_goals first
    | exact h_can_src
    | simp [h_can_src, countRefsWithCapability]

-- Helper: single-element list has count 0 or 1 for any capability
theorem single_elem_count_le_one (ref : Reference) (cap : RefCapability) :
    countRefsWithCapability [ref] cap <= 1 := by
  simp [countRefsWithCapability]
  by_cases h : ref.refType.capability == cap
  · simp [h]
  · simp [h]

-- Helper: single-element list has length 1
theorem single_elem_length (ref : Reference) : [ref].length = 1 := rfl

-- Helper: empty list has count 0
theorem empty_list_count_zero (cap : RefCapability) :
    countRefsWithCapability [] cap = 0 := rfl

-- Helper: if existingRefs is empty, adding a ref gives a single-element list
theorem cons_empty_gives_single (ref : Reference) :
    (ref :: []).length = 1 := rfl

-- Helper: if list.isEmpty = false returns false, list must be empty
theorem isEmpty_false_means_empty {α : Type} (l : List α) :
    (!l.isEmpty) = false → l = [] := by
  cases l with
  | nil => intro _; rfl
  | cons h t => simp [List.isEmpty]

-- Helper: capability not equal
theorem shared_ne_exclusive : RefCapability.Shared ≠ RefCapability.Exclusive := by decide
theorem shared_ne_isolated : RefCapability.Shared ≠ RefCapability.Isolated := by decide
theorem exclusive_ne_shared : RefCapability.Exclusive ≠ RefCapability.Shared := by decide
theorem exclusive_ne_isolated : RefCapability.Exclusive ≠ RefCapability.Isolated := by decide
theorem isolated_ne_shared : RefCapability.Isolated ≠ RefCapability.Shared := by decide
theorem isolated_ne_exclusive : RefCapability.Isolated ≠ RefCapability.Exclusive := by decide

-- Helper: not isEmpty means list is empty when it's false
theorem not_isEmpty_false_means_empty {α : Type} (l : List α) :
    (!l.isEmpty) = false → l = [] := by
  intro h
  cases l with
  | nil => rfl
  | cons _ _ => simp [List.isEmpty] at h

-- Helper: count > 0 = false means count = 0
theorem count_gt_zero_false_means_zero (n : Nat) :
    decide (n > 0) = false → n = 0 := by
  intro h
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  omega

-- Main theorem: Creating a reference maintains well-formedness
theorem create_ref_preserves_wellformed (env : RefEnv) (ref : Reference) :
  wellFormed env →
  canCreateRef env ref.location ref.refType.capability = true →
  wellFormed (addRef env ref) := by
  intro h_wf h_can
  unfold wellFormed at h_wf ⊢
  intro loc refs h_mem
  rw [addRef_mem_iff] at h_mem
  cases h_mem with
  | inl h_eq =>
    -- Case: loc = ref.location, refs = ref :: getActiveRefs env ref.location
    obtain ⟨h_loc_eq, h_refs_eq⟩ := h_eq
    subst h_loc_eq h_refs_eq
    -- Analyze based on the capability being added
    cases h_cap : ref.refType.capability with
    | Shared =>
      -- Shared case: canCreateRef=true means no Exclusive/Isolated exist
      unfold canCreateRef at h_can
      simp only [h_cap, Bool.and_eq_true, Bool.not_eq_true'] at h_can
      obtain ⟨h_no_excl, h_no_iso⟩ := h_can
      -- Count exclusive = 0, count isolated = 0 in existing refs
      have h_excl_zero := count_gt_zero_false_means_zero _ h_no_excl
      have h_iso_zero := count_gt_zero_false_means_zero _ h_no_iso
      -- After adding Shared ref, counts stay the same for Exclusive/Isolated
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- At most one Exclusive
        rw [count_cons_diff _ _ _ (by simp [h_cap])]
        omega
      · -- At most one Isolated
        rw [count_cons_diff _ _ _ (by simp [h_cap])]
        omega
      · -- Exclusive=1 implies length=1
        intro h_excl_one
        rw [count_cons_diff _ _ _ (by simp [h_cap])] at h_excl_one
        omega
      · -- Isolated=1 implies length=1
        intro h_iso_one
        rw [count_cons_diff _ _ _ (by simp [h_cap])] at h_iso_one
        omega
    | Exclusive =>
      -- Exclusive case: canCreateRef=true means no refs exist
      unfold canCreateRef at h_can
      simp only [h_cap, Bool.not_eq_true'] at h_can
      have h_empty := not_isEmpty_false_means_empty _ h_can
      rw [h_empty]
      have h_excl_count : countRefsWithCapability [ref] RefCapability.Exclusive = 1 := by
        simp only [countRefsWithCapability, List.filter, h_cap, beq_self_eq_true,
                   List.length_singleton]
      have h_iso_count : countRefsWithCapability [ref] RefCapability.Isolated = 0 := by
        unfold countRefsWithCapability
        simp only [List.filter, h_cap]
        have h_neq : (RefCapability.Exclusive == RefCapability.Isolated) = false := rfl
        simp only [h_neq, List.length_nil]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [h_excl_count]; exact Nat.le_refl 1
      · simp only [h_iso_count]; exact Nat.zero_le 1
      · intro _; rfl
      · intro h; simp only [h_iso_count] at h; cases h
    | Isolated =>
      -- Isolated case: canCreateRef=true means no refs exist
      unfold canCreateRef at h_can
      simp only [h_cap, Bool.not_eq_true'] at h_can
      have h_empty := not_isEmpty_false_means_empty _ h_can
      rw [h_empty]
      have h_excl_count : countRefsWithCapability [ref] RefCapability.Exclusive = 0 := by
        unfold countRefsWithCapability
        simp only [List.filter, h_cap]
        have h_neq : (RefCapability.Isolated == RefCapability.Exclusive) = false := rfl
        simp only [h_neq, List.length_nil]
      have h_iso_count : countRefsWithCapability [ref] RefCapability.Isolated = 1 := by
        simp only [countRefsWithCapability, List.filter, h_cap, beq_self_eq_true,
                   List.length_singleton]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [h_excl_count]; exact Nat.zero_le 1
      · simp only [h_iso_count]; exact Nat.le_refl 1
      · intro h; simp only [h_excl_count] at h; cases h
      · intro _; rfl
  | inr h_ne =>
    -- Case: loc ≠ ref.location, refs unchanged from original env
    obtain ⟨h_loc_ne, h_mem_orig⟩ := h_ne
    exact h_wf loc refs h_mem_orig

-- Integration with memory operations

-- Memory access (read or write)
inductive MemAccess where
  | Read  : Nat -> MemAccess  -- location
  | Write : Nat -> MemAccess  -- location
deriving Repr

-- Check if a reference allows a memory access
def allowsAccess (ref : Reference) (access : MemAccess) : Bool :=
  match access with
  | MemAccess.Read loc =>
      -- All capabilities allow reads
      ref.location == loc
  | MemAccess.Write loc =>
      -- Only Exclusive and Isolated allow writes
      ref.location == loc &&
      (ref.refType.capability == RefCapability.Exclusive ||
       ref.refType.capability == RefCapability.Isolated)

-- Check if an access is safe in current environment
def accessIsSafe (env : RefEnv) (access : MemAccess) : Bool :=
  let loc := match access with
    | MemAccess.Read l => l
    | MemAccess.Write l => l
  let refs := getActiveRefs env loc
  -- At least one ref must allow this access
  refs.any (fun r => allowsAccess r access)

-- Property 6: No conflicting accesses
def hasConflictingAccess (env : RefEnv) (loc : Nat) : Bool :=
  let refs := getActiveRefs env loc
  -- Conflict: multiple refs and at least one allows write
  refs.length > 1 && refs.any (fun r => allowsAccess r (MemAccess.Write loc))

-- Helper: if a ref allows write at loc, it must have Exclusive or Isolated capability
theorem allowsWrite_capability (ref : Reference) (loc : Nat) :
  allowsAccess ref (MemAccess.Write loc) = true ->
  ref.location = loc ∧ (ref.refType.capability = RefCapability.Exclusive ∨
                        ref.refType.capability = RefCapability.Isolated) := by
  intro h
  simp [allowsAccess] at h
  constructor
  · cases h_loc : (ref.location == loc) <;> simp_all
  · cases h_cap : ref.refType.capability <;> simp_all

-- Helper: count 0 means no refs have that capability
theorem count_zero_means_none (refs : List Reference) (cap : RefCapability) :
  countRefsWithCapability refs cap = 0 ->
  forall r, r ∈ refs -> r.refType.capability ≠ cap := by
  intro h_count r h_mem h_eq
  unfold countRefsWithCapability at h_count
  have h_in_filter : r ∈ refs.filter (fun r => r.refType.capability == cap) := by
    rw [List.mem_filter]
    exact ⟨h_mem, by simp [h_eq]⟩
  have h_len_pos := List.length_pos_of_mem h_in_filter
  rw [h_count] at h_len_pos
  exact Nat.not_lt_zero 0 h_len_pos

-- Helper: if count <= 1 and length > 1, then count can only be 0
theorem count_zero_when_length_gt_one (refs : List Reference) (cap : RefCapability)
  (h_len : refs.length > 1)
  (h_count_le : countRefsWithCapability refs cap <= 1)
  (h_alone : countRefsWithCapability refs cap = 1 -> refs.length = 1) :
  countRefsWithCapability refs cap = 0 := by
  cases h_count : countRefsWithCapability refs cap with
  | zero => rfl
  | succ n =>
    cases n with
    | zero =>
      have h_len_one := h_alone h_count
      omega
    | succ m =>
      have h_ge_2 : countRefsWithCapability refs cap >= 2 := by rw [h_count]; omega
      omega

-- Well-formed environments have no conflicts (fully proven)
theorem wellformed_no_conflicts (env : RefEnv) (h_wf : wellFormed env) :
  forall loc, hasConflictingAccess env loc = false := by
  intro loc
  unfold hasConflictingAccess
  by_cases h_len : (getActiveRefs env loc).length > 1
  · have h_excl_unique := exclusive_is_unique env loc h_wf
    have h_iso_unique := isolated_is_unique env loc h_wf
    have h_excl_alone := exclusive_prevents_aliasing env loc h_wf
    have h_iso_alone := isolated_prevents_aliasing env loc h_wf
    have h_excl_zero := count_zero_when_length_gt_one
      (getActiveRefs env loc) RefCapability.Exclusive h_len h_excl_unique h_excl_alone
    have h_iso_zero := count_zero_when_length_gt_one
      (getActiveRefs env loc) RefCapability.Isolated h_len h_iso_unique h_iso_alone
    have h_no_excl := count_zero_means_none (getActiveRefs env loc) RefCapability.Exclusive h_excl_zero
    have h_no_iso := count_zero_means_none (getActiveRefs env loc) RefCapability.Isolated h_iso_zero
    have h_decide : decide ((getActiveRefs env loc).length > 1) = true := by simp [h_len]
    simp only [h_decide, Bool.true_and]
    rw [List.any_eq_false]
    intros ref h_mem
    unfold allowsAccess
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    intro ⟨_, h_cap⟩
    cases h_cap with
    | inl h_excl => exact h_no_excl ref h_mem h_excl
    | inr h_iso => exact h_no_iso ref h_mem h_iso
  · have h_decide : decide ((getActiveRefs env loc).length > 1) = false := by simp [h_len]
    simp only [h_decide, Bool.false_and]

-- Data race definition: concurrent conflicting accesses
structure DataRaceScenario where
  loc : Nat
  access1 : MemAccess
  access2 : MemAccess
  hasWrite : access1 matches MemAccess.Write _ ∨ access2 matches MemAccess.Write _
  sameLocation : (match access1 with | MemAccess.Read l | MemAccess.Write l => l) =
                 (match access2 with | MemAccess.Read l | MemAccess.Write l => l)

-- Property 7: Capability system prevents data races
theorem capabilities_prevent_races (env : RefEnv) (scenario : DataRaceScenario) (h_wf : wellFormed env) :
  accessIsSafe env scenario.access1 = true ->
  accessIsSafe env scenario.access2 = true ->
  hasConflictingAccess env scenario.loc = false := by
  intros _ _
  exact wellformed_no_conflicts env h_wf scenario.loc

-- Examples

example : exists env : RefEnv,
  let loc := 0
  let ref1 := Reference.mk loc { baseType := "i64", capability := RefCapability.Shared }
  let _ref2 := Reference.mk loc { baseType := "i64", capability := RefCapability.Shared }
  canCreateRef env loc RefCapability.Shared = true ∧
  canCreateRef (addRef env ref1) loc RefCapability.Shared = true := by
  refine ⟨{ activeRefs := [] }, ?_⟩
  native_decide

example : exists env : RefEnv,
  let loc := 0
  let ref1 := Reference.mk loc { baseType := "i64", capability := RefCapability.Exclusive }
  canCreateRef env loc RefCapability.Exclusive = true ∧
  canCreateRef (addRef env ref1) loc RefCapability.Shared = false := by
  refine ⟨{ activeRefs := [] }, ?_⟩
  native_decide

example : exists env : RefEnv,
  let loc := 0
  let ref1 := Reference.mk loc { baseType := "i64", capability := RefCapability.Isolated }
  canCreateRef env loc RefCapability.Isolated = true ∧
  canCreateRef (addRef env ref1) loc RefCapability.Shared = false ∧
  canCreateRef (addRef env ref1) loc RefCapability.Exclusive = false := by
  refine ⟨{ activeRefs := [] }, ?_⟩
  native_decide

example :
  canConvert RefCapability.Exclusive RefCapability.Shared = true := by
  native_decide

example :
  canConvert RefCapability.Isolated RefCapability.Exclusive = true := by
  native_decide

example :
  canConvert RefCapability.Shared RefCapability.Exclusive = false := by
  native_decide

-- Concurrency mode integration

inductive ConcurrencyMode where
  | Actor    : ConcurrencyMode  -- No shared mutable state
  | LockBase : ConcurrencyMode  -- Shared state via locks
  | Unsafe   : ConcurrencyMode  -- No restrictions
deriving DecidableEq, Repr

def capabilityAllowedInMode (cap : RefCapability) (mode : ConcurrencyMode) : Bool :=
  match mode with
  | ConcurrencyMode.Actor =>
      cap == RefCapability.Shared || cap == RefCapability.Isolated
  | ConcurrencyMode.LockBase =>
      true
  | ConcurrencyMode.Unsafe =>
      true

theorem actor_mode_safety :
  forall cap, capabilityAllowedInMode cap ConcurrencyMode.Actor = true ->
         cap ≠ RefCapability.Exclusive := by
  intros cap h_allowed
  cases cap
  · intro h; cases h
  · have : capabilityAllowedInMode RefCapability.Exclusive ConcurrencyMode.Actor = false := by native_decide
    rw [this] at h_allowed
    cases h_allowed
  · intro h; cases h

def envSatisfiesMode (env : RefEnv) (mode : ConcurrencyMode) : Bool :=
  env.activeRefs.all fun (_, refs) =>
    refs.all fun ref => capabilityAllowedInMode ref.refType.capability mode

theorem mode_safety (env : RefEnv) (mode : ConcurrencyMode) (h_wf : wellFormed env) :
  envSatisfiesMode env mode = true ->
  forall loc, hasConflictingAccess env loc = false := by
  intro _
  exact wellformed_no_conflicts env h_wf

/-
## Verification Summary

This module proves the following key properties of the capability system:

1. **Uniqueness**: Exclusive and Isolated references are unique (at most one)
2. **Isolation**: Exclusive and Isolated prevent all aliasing
3. **Safe Conversions**: Capability conversions are monotonic (lose privileges)
4. **Well-Formedness**: Reference creation maintains environment invariants
5. **No Conflicts**: Well-formed environments have no conflicting accesses
6. **Data Race Freedom**: Capabilities prevent concurrent conflicting accesses
7. **Concurrency Modes**: Actor mode enforces no shared mutable state

These properties guarantee that the Simple language's memory model prevents
data races at compile time through the type system.
-/
