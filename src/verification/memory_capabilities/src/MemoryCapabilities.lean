/-
  MemoryCapabilities.lean - Reduced-valid model for reference capabilities
  
  This generator emits a small valid Lean model for capability-tagged
  references, aliasing checks, capability conversions, and access safety.
-/
namespace MemoryCapabilities
inductive RefCapability
  | Shared
  | Exclusive
  | Isolated
deriving DecidableEq, Repr, BEq, Inhabited

inductive MemAccess
  | Read : Nat → MemAccess
  | Write : Nat → MemAccess
deriving Repr, Inhabited

structure CapType where
  baseType : String
  capability : RefCapability
  deriving Repr, Inhabited

structure Reference where
  location : Nat
  refType : CapType
  deriving Repr, Inhabited

structure RefEnv where
  activeRefs : List (Nat × List Reference)
  deriving Repr, Inhabited

def getActiveRefs (env : RefEnv) (loc : Nat) : List Reference :=
  match env.activeRefs.find? (fun entry => entry.fst == loc) with
  | some (_, refs) => refs
  | none => []

def countRefsWithCapability (refs : List Reference) (cap : RefCapability) : Nat :=
  refs.filter (fun r => r.refType.capability == cap) |>.length

def canCreateRef (env : RefEnv) (loc : Nat) (newCap : RefCapability) : Bool :=
  let refs := getActiveRefs env loc
  let hasExclusive := countRefsWithCapability refs RefCapability.Exclusive > 0
  let hasIsolated := countRefsWithCapability refs RefCapability.Isolated > 0
  let hasAny := !refs.isEmpty
  match newCap with
  | RefCapability.Shared => !hasExclusive && !hasIsolated
  | RefCapability.Exclusive => !hasAny
  | RefCapability.Isolated => !hasAny

def canConvert (srcCap dstCap : RefCapability) : Bool :=
  match srcCap, dstCap with
  | a, b => if a == b then true else
    match srcCap, dstCap with
    | RefCapability.Exclusive, RefCapability.Shared => true
    | RefCapability.Isolated, RefCapability.Exclusive => true
    | RefCapability.Isolated, RefCapability.Shared => true
    | _, _ => false

def isMoreRestrictive (a b : RefCapability) : Prop :=
  match a, b with
  | RefCapability.Isolated, RefCapability.Exclusive => True
  | RefCapability.Isolated, RefCapability.Shared => True
  | RefCapability.Exclusive, RefCapability.Shared => True
  | x, y => x = y

def allowsAccess (ref : Reference) (access : MemAccess) : Bool :=
  match access with
  | MemAccess.Read loc => ref.location == loc
  | MemAccess.Write loc =>
      ref.location == loc &&
      (ref.refType.capability == RefCapability.Exclusive ||
       ref.refType.capability == RefCapability.Isolated)

def accessIsSafe (env : RefEnv) (access : MemAccess) : Bool :=
  let loc := match access with | MemAccess.Read l => l | MemAccess.Write l => l
  (getActiveRefs env loc).any (fun r => allowsAccess r access)

def wellFormed (env : RefEnv) : Prop :=
  ∀ loc refs, (loc, refs) ∈ env.activeRefs →
    countRefsWithCapability refs RefCapability.Exclusive ≤ 1 ∧
    countRefsWithCapability refs RefCapability.Isolated ≤ 1 ∧
    countRefsWithCapability refs RefCapability.Exclusive +
      countRefsWithCapability refs RefCapability.Isolated ≤ 1

theorem can_convert_refl (cap : RefCapability) :
  canConvert cap cap = true := by
  cases cap <;> rfl

theorem exclusive_to_shared :
  canConvert RefCapability.Exclusive RefCapability.Shared = true := by
  rfl

theorem isolated_to_exclusive :
  canConvert RefCapability.Isolated RefCapability.Exclusive = true := by
  rfl

theorem isolated_to_shared :
  canConvert RefCapability.Isolated RefCapability.Shared = true := by
  rfl

theorem capability_downgrades_allowed :
  canConvert RefCapability.Exclusive RefCapability.Shared = true ∧
  canConvert RefCapability.Isolated RefCapability.Exclusive = true ∧
  canConvert RefCapability.Isolated RefCapability.Shared = true := by
  constructor
  · exact exclusive_to_shared
  · constructor
    · exact isolated_to_exclusive
    · exact isolated_to_shared

theorem shared_to_exclusive_denied :
  canConvert RefCapability.Shared RefCapability.Exclusive = false := by
  rfl

theorem exclusive_to_isolated_denied :
  canConvert RefCapability.Exclusive RefCapability.Isolated = false := by
  rfl

theorem shared_to_isolated_denied :
  canConvert RefCapability.Shared RefCapability.Isolated = false := by
  rfl

theorem capability_upgrades_denied :
  canConvert RefCapability.Shared RefCapability.Exclusive = false ∧
  canConvert RefCapability.Shared RefCapability.Isolated = false ∧
  canConvert RefCapability.Exclusive RefCapability.Isolated = false := by
  constructor
  · exact shared_to_exclusive_denied
  · constructor
    · exact shared_to_isolated_denied
    · exact exclusive_to_isolated_denied

theorem can_convert_implies_restrictive (srcCap dstCap : RefCapability) :
  canConvert srcCap dstCap = true → isMoreRestrictive srcCap dstCap := by
  cases srcCap <;> cases dstCap <;> simp [canConvert, isMoreRestrictive] <;> decide

theorem restrictive_implies_can_convert (srcCap dstCap : RefCapability) :
  isMoreRestrictive srcCap dstCap → canConvert srcCap dstCap = true := by
  cases srcCap <;> cases dstCap <;> simp [canConvert, isMoreRestrictive] <;> decide

theorem can_convert_iff_restrictive (srcCap dstCap : RefCapability) :
  canConvert srcCap dstCap = true ↔ isMoreRestrictive srcCap dstCap := by
  constructor
  · exact can_convert_implies_restrictive srcCap dstCap
  · exact restrictive_implies_can_convert srcCap dstCap

theorem empty_env_allows_shared (loc : Nat) :
  canCreateRef { activeRefs := [] } loc RefCapability.Shared = true := by
  simp [canCreateRef, getActiveRefs]
  exact ⟨rfl, rfl⟩

theorem empty_env_allows_exclusive (loc : Nat) :
  canCreateRef { activeRefs := [] } loc RefCapability.Exclusive = true := by
  simp [canCreateRef, getActiveRefs]

theorem empty_env_allows_isolated (loc : Nat) :
  canCreateRef { activeRefs := [] } loc RefCapability.Isolated = true := by
  simp [canCreateRef, getActiveRefs]

theorem empty_env_allows_all_caps (loc : Nat) :
  canCreateRef { activeRefs := [] } loc RefCapability.Shared = true ∧
  canCreateRef { activeRefs := [] } loc RefCapability.Exclusive = true ∧
  canCreateRef { activeRefs := [] } loc RefCapability.Isolated = true := by
  constructor
  · exact empty_env_allows_shared loc
  · constructor
    · exact empty_env_allows_exclusive loc
    · exact empty_env_allows_isolated loc

theorem empty_env_access_not_safe (access : MemAccess) :
  accessIsSafe { activeRefs := [] } access = false := by
  cases access <;> simp [accessIsSafe, getActiveRefs]

theorem existing_ref_denies_exclusive
    (baseType : String) (loc : Nat) (cap : RefCapability) :
    canCreateRef
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      loc RefCapability.Exclusive = false := by
  cases cap <;> simp [canCreateRef, getActiveRefs]

theorem existing_ref_denies_isolated
    (baseType : String) (loc : Nat) (cap : RefCapability) :
    canCreateRef
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      loc RefCapability.Isolated = false := by
  cases cap <;> simp [canCreateRef, getActiveRefs]

theorem existing_ref_denies_unique_create
    (baseType : String) (loc : Nat) (cap : RefCapability) :
    canCreateRef
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      loc RefCapability.Exclusive = false ∧
    canCreateRef
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      loc RefCapability.Isolated = false := by
  constructor
  · exact existing_ref_denies_exclusive baseType loc cap
  · exact existing_ref_denies_isolated baseType loc cap

theorem existing_shared_allows_shared (baseType : String) (loc : Nat) :
  canCreateRef
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    loc RefCapability.Shared = true := by
  simp [canCreateRef, getActiveRefs, countRefsWithCapability]
  exact ⟨rfl, rfl⟩

theorem two_shared_allows_shared (baseType : String) (loc : Nat) :
  canCreateRef
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    loc RefCapability.Shared = true := by
  simp [canCreateRef, getActiveRefs, countRefsWithCapability]
  exact ⟨rfl, rfl⟩

theorem shared_read_same_loc (baseType : String) (loc : Nat) :
  allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } } (MemAccess.Read loc) = true := by
  simp [allowsAccess]

theorem singleton_shared_read_safe (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Read loc) = true := by
  simp [accessIsSafe, getActiveRefs, allowsAccess]

theorem two_shared_read_safe (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Read loc) = true := by
  simp [accessIsSafe, getActiveRefs, allowsAccess]

theorem read_access_implies_same_location
    (baseType : String) (loc other : Nat) (cap : RefCapability) :
    allowsAccess { location := loc, refType := { baseType := baseType, capability := cap } }
      (MemAccess.Read other) = true →
    loc = other := by
  cases cap <;> simp [allowsAccess]

theorem exclusive_write_same_loc (baseType : String) (loc : Nat) :
  allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } } (MemAccess.Write loc) = true := by
  simp [allowsAccess]
  exact Or.inl rfl

theorem singleton_exclusive_write_safe (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Exclusive } }])] }
    (MemAccess.Write loc) = true := by
  simp [accessIsSafe, getActiveRefs, allowsAccess]
  exact Or.inl rfl

theorem isolated_write_same_loc (baseType : String) (loc : Nat) :
  allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } } (MemAccess.Write loc) = true := by
  simp [allowsAccess]
  exact Or.inr rfl

theorem singleton_isolated_write_safe (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Isolated } }])] }
    (MemAccess.Write loc) = true := by
  simp [accessIsSafe, getActiveRefs, allowsAccess]
  exact Or.inr rfl

theorem singleton_unique_write_safe (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Exclusive } }])] }
    (MemAccess.Write loc) = true ∧
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Isolated } }])] }
    (MemAccess.Write loc) = true := by
  constructor
  · exact singleton_exclusive_write_safe baseType loc
  · exact singleton_isolated_write_safe baseType loc

theorem write_access_implies_unique_cap
    (baseType : String) (loc : Nat) (cap : RefCapability) :
    allowsAccess { location := loc, refType := { baseType := baseType, capability := cap } }
      (MemAccess.Write loc) = true →
    cap = RefCapability.Exclusive ∨ cap = RefCapability.Isolated := by
  cases cap <;> simp [allowsAccess]
  exact ⟨rfl, rfl⟩

theorem write_access_implies_same_location_and_unique_cap
    (baseType : String) (loc other : Nat) (cap : RefCapability) :
    allowsAccess { location := loc, refType := { baseType := baseType, capability := cap } }
      (MemAccess.Write other) = true →
    loc = other ∧ (cap = RefCapability.Exclusive ∨ cap = RefCapability.Isolated) := by
  cases cap
  · simp [allowsAccess]
    intro _
    exact ⟨rfl, rfl⟩
  · simp [allowsAccess]
    intro h _
    exact h
  · simp [allowsAccess]
    intro h _
    exact h

theorem access_implies_same_location
    (baseType : String) (loc : Nat) (cap : RefCapability) (access : MemAccess) :
    allowsAccess { location := loc, refType := { baseType := baseType, capability := cap } }
      access = true →
    match access with
    | MemAccess.Read target => loc = target
    | MemAccess.Write target => loc = target := by
  cases access with
  | Read target =>
      intro h
      exact read_access_implies_same_location baseType loc target cap h
  | Write target =>
      intro h
      exact (write_access_implies_same_location_and_unique_cap baseType loc target cap h).left

theorem shared_write_same_loc_denied (baseType : String) (loc : Nat) :
  allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } } (MemAccess.Write loc) = false := by
  simp [allowsAccess]
  exact ⟨rfl, rfl⟩

theorem singleton_shared_write_not_safe (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Write loc) = false := by
  simp [accessIsSafe, getActiveRefs, allowsAccess]
  exact ⟨rfl, rfl⟩

theorem singleton_shared_read_only_at_location (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Read loc) = true ∧
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Write loc) = false := by
  constructor
  · exact singleton_shared_read_safe baseType loc
  · exact singleton_shared_write_not_safe baseType loc

theorem two_shared_write_not_safe (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Write loc) = false := by
  simp [accessIsSafe, getActiveRefs, allowsAccess]
  exact ⟨rfl, rfl⟩

theorem two_shared_read_only_at_location (baseType : String) (loc : Nat) :
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Read loc) = true ∧
  accessIsSafe
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    (MemAccess.Write loc) = false := by
  constructor
  · exact two_shared_read_safe baseType loc
  · exact two_shared_write_not_safe baseType loc

theorem read_wrong_location_denied
    (baseType : String) (loc other : Nat) (cap : RefCapability)
    (hne : loc ≠ other) :
    allowsAccess { location := loc, refType := { baseType := baseType, capability := cap } }
      (MemAccess.Read other) = false := by
  cases cap <;> simp [allowsAccess, hne]

theorem singleton_read_wrong_location_not_safe
    (baseType : String) (loc other : Nat) (cap : RefCapability)
    (hne : loc ≠ other) :
    accessIsSafe
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      (MemAccess.Read other) = false := by
  cases cap <;> simp [accessIsSafe, getActiveRefs, allowsAccess, hne]

theorem write_wrong_location_denied
    (baseType : String) (loc other : Nat) (cap : RefCapability)
    (hne : loc ≠ other) :
    allowsAccess { location := loc, refType := { baseType := baseType, capability := cap } }
      (MemAccess.Write other) = false := by
  cases cap <;> simp [allowsAccess, hne]

theorem singleton_write_wrong_location_not_safe
    (baseType : String) (loc other : Nat) (cap : RefCapability)
    (hne : loc ≠ other) :
    accessIsSafe
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      (MemAccess.Write other) = false := by
  cases cap <;> simp [accessIsSafe, getActiveRefs, allowsAccess, hne]

theorem singleton_access_wrong_location_not_safe
    (baseType : String) (loc other : Nat) (cap : RefCapability)
    (hne : loc ≠ other) :
    accessIsSafe
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      (MemAccess.Read other) = false ∧
    accessIsSafe
      { activeRefs :=
          [(loc,
            [{ location := loc,
               refType := { baseType := baseType, capability := cap } }])] }
      (MemAccess.Write other) = false := by
  constructor
  · exact singleton_read_wrong_location_not_safe baseType loc other cap hne
  · exact singleton_write_wrong_location_not_safe baseType loc other cap hne

theorem empty_env_wellformed :
  wellFormed { activeRefs := [] } := by
  intro loc refs h
  cases h

theorem empty_env_wellformed_and_no_access (access : MemAccess) :
  wellFormed { activeRefs := [] } ∧
  accessIsSafe { activeRefs := [] } access = false := by
  constructor
  · exact empty_env_wellformed
  · exact empty_env_access_not_safe access

theorem empty_env_complete_policy (loc : Nat) (access : MemAccess) :
  canCreateRef { activeRefs := [] } loc RefCapability.Shared = true ∧
  canCreateRef { activeRefs := [] } loc RefCapability.Exclusive = true ∧
  canCreateRef { activeRefs := [] } loc RefCapability.Isolated = true ∧
  wellFormed { activeRefs := [] } ∧
  accessIsSafe { activeRefs := [] } access = false := by
  constructor
  · exact empty_env_allows_shared loc
  · constructor
    · exact empty_env_allows_exclusive loc
    · constructor
      · exact empty_env_allows_isolated loc
      · exact empty_env_wellformed_and_no_access access

theorem singleton_env_wellformed (baseType : String) (loc : Nat) (cap : RefCapability) :
  wellFormed
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := cap } }])] } := by
  intro foundLoc refs h
  simp at h
  rcases h with ⟨_, hrefs⟩
  subst refs
  constructor
  · unfold countRefsWithCapability
    exact List.length_filter_le
      (fun r : Reference => r.refType.capability == RefCapability.Exclusive)
      ([{ location := loc, refType := { baseType := baseType, capability := cap } }] : List Reference)
  · constructor
    · unfold countRefsWithCapability
      exact List.length_filter_le
        (fun r : Reference => r.refType.capability == RefCapability.Isolated)
        ([{ location := loc, refType := { baseType := baseType, capability := cap } }] : List Reference)
    · cases cap
      · change countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }] : List Reference)
          RefCapability.Exclusive +
          countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }] : List Reference)
          RefCapability.Isolated ≤ 1
        rw [show countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }] : List Reference)
          RefCapability.Exclusive = 0 by rfl]
        rw [show countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }] : List Reference)
          RefCapability.Isolated = 0 by rfl]
        exact Nat.zero_le 1
      · change countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }] : List Reference)
          RefCapability.Exclusive +
          countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }] : List Reference)
          RefCapability.Isolated ≤ 1
        rw [show countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }] : List Reference)
          RefCapability.Exclusive = 1 by rfl]
        rw [show countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }] : List Reference)
          RefCapability.Isolated = 0 by rfl]
        exact Nat.le_refl 1
      · change countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }] : List Reference)
          RefCapability.Exclusive +
          countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }] : List Reference)
          RefCapability.Isolated ≤ 1
        rw [show countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }] : List Reference)
          RefCapability.Exclusive = 0 by rfl]
        rw [show countRefsWithCapability
          ([{ location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }] : List Reference)
          RefCapability.Isolated = 1 by rfl]
        exact Nat.le_refl 1

theorem empty_create_ref_wellformed (baseType : String) (loc : Nat) (cap : RefCapability) :
  canCreateRef { activeRefs := [] } loc cap = true ∧
  wellFormed
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := cap } }])] } := by
  constructor
  · cases cap <;> simp [canCreateRef, getActiveRefs]
    exact ⟨rfl, rfl⟩
  · exact singleton_env_wellformed baseType loc cap

theorem empty_create_all_singletons_wellformed (baseType : String) (loc : Nat) :
  (canCreateRef { activeRefs := [] } loc RefCapability.Shared = true ∧
    wellFormed { activeRefs := [(loc, [{ location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }])] }) ∧
  (canCreateRef { activeRefs := [] } loc RefCapability.Exclusive = true ∧
    wellFormed { activeRefs := [(loc, [{ location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }])] }) ∧
  (canCreateRef { activeRefs := [] } loc RefCapability.Isolated = true ∧
    wellFormed { activeRefs := [(loc, [{ location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }])] }) := by
  constructor
  · exact empty_create_ref_wellformed baseType loc RefCapability.Shared
  · constructor
    · exact empty_create_ref_wellformed baseType loc RefCapability.Exclusive
    · exact empty_create_ref_wellformed baseType loc RefCapability.Isolated

theorem two_shared_env_wellformed (baseType : String) (loc : Nat) :
  wellFormed
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] } := by
  intro foundLoc refs h
  simp at h
  rcases h with ⟨_, hrefs⟩
  subst refs
  constructor
  · change countRefsWithCapability
      ([
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
      ] : List Reference) RefCapability.Exclusive ≤ 1
    rw [show countRefsWithCapability
      ([
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
      ] : List Reference) RefCapability.Exclusive = 0 by rfl]
    exact Nat.zero_le 1
  · constructor
    · change countRefsWithCapability
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
        ] : List Reference) RefCapability.Isolated ≤ 1
      rw [show countRefsWithCapability
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
        ] : List Reference) RefCapability.Isolated = 0 by rfl]
      exact Nat.zero_le 1
    · change
        countRefsWithCapability
          ([
            { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
            { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
          ] : List Reference) RefCapability.Exclusive +
        countRefsWithCapability
          ([
            { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
            { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
          ] : List Reference) RefCapability.Isolated ≤ 1
      rw [show countRefsWithCapability
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
        ] : List Reference) RefCapability.Exclusive = 0 by rfl]
      rw [show countRefsWithCapability
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } }
        ] : List Reference) RefCapability.Isolated = 0 by rfl]
      exact Nat.zero_le 1

theorem shared_alias_create_wellformed (baseType : String) (loc : Nat) :
  canCreateRef
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] }
    loc RefCapability.Shared = true ∧
  wellFormed
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Shared } }])] } := by
  constructor
  · exact existing_shared_allows_shared baseType loc
  · exact two_shared_env_wellformed baseType loc

theorem two_exclusive_env_not_wellformed (baseType : String) (loc : Nat) :
  ¬ wellFormed
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Exclusive } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Exclusive } }])] } := by
  intro hwf
  have h := hwf loc
    ([
      { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
      { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }
    ] : List Reference)
  have hmem :
      (loc,
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }
        ] : List Reference)) ∈
      [(loc,
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }
        ] : List Reference))] := by
    simp
  have hbound := (h hmem).left
  have hcount :
      countRefsWithCapability
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } }
        ] : List Reference)
        RefCapability.Exclusive = 2 := by
    rfl
  rw [hcount] at hbound
  exact Nat.not_succ_le_self 1 hbound

theorem two_isolated_env_not_wellformed (baseType : String) (loc : Nat) :
  ¬ wellFormed
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Isolated } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Isolated } }])] } := by
  intro hwf
  have h := hwf loc
    ([
      { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } },
      { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
    ] : List Reference)
  have hmem :
      (loc,
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
        ] : List Reference)) ∈
      [(loc,
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
        ] : List Reference))] := by
    simp
  have hbound := (h hmem).right.left
  have hcount :
      countRefsWithCapability
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
        ] : List Reference)
        RefCapability.Isolated = 2 := by
    rfl
  rw [hcount] at hbound
  exact Nat.not_succ_le_self 1 hbound

theorem mixed_exclusive_isolated_env_not_wellformed (baseType : String) (loc : Nat) :
  ¬ wellFormed
    { activeRefs :=
        [(loc,
          [{ location := loc,
             refType := { baseType := baseType, capability := RefCapability.Exclusive } },
           { location := loc,
             refType := { baseType := baseType, capability := RefCapability.Isolated } }])] } := by
  intro hwf
  have h := hwf loc
    ([
      { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
      { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
    ] : List Reference)
  have hmem :
      (loc,
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
        ] : List Reference)) ∈
      [(loc,
        ([
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
          { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
        ] : List Reference))] := by
    simp
  have hbound := (h hmem).right.right
  have hcount :
      countRefsWithCapability
      ([
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
      ] : List Reference) RefCapability.Exclusive +
      countRefsWithCapability
      ([
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } },
        { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } }
      ] : List Reference) RefCapability.Isolated = 2 := by
    rfl
  rw [hcount] at hbound
  exact Nat.not_succ_le_self 1 hbound

end MemoryCapabilities
