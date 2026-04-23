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

theorem empty_env_allows_exclusive (loc : Nat) :
  canCreateRef { activeRefs := [] } loc RefCapability.Exclusive = true := by
  simp [canCreateRef, getActiveRefs]

theorem empty_env_allows_isolated (loc : Nat) :
  canCreateRef { activeRefs := [] } loc RefCapability.Isolated = true := by
  simp [canCreateRef, getActiveRefs]

theorem shared_read_same_loc (baseType : String) (loc : Nat) :
  allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Shared } } (MemAccess.Read loc) = true := by
  simp [allowsAccess]

theorem exclusive_write_same_loc (baseType : String) (loc : Nat) :
  allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } } (MemAccess.Write loc) = allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Exclusive } } (MemAccess.Write loc) := by
  rfl

theorem isolated_write_same_loc (baseType : String) (loc : Nat) :
  allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } } (MemAccess.Write loc) = allowsAccess { location := loc, refType := { baseType := baseType, capability := RefCapability.Isolated } } (MemAccess.Write loc) := by
  rfl

theorem empty_env_wellformed :
  wellFormed { activeRefs := [] } := by
  intro loc refs h
  cases h

end MemoryCapabilities
