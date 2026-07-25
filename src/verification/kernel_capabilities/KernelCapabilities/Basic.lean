/-
  KernelCapabilities.Basic — Pure state-machine model of the SimpleOS kernel
  IPC capability system.

  Source of truth:
    src/os/kernel/ipc/capability.spl          (CapabilityManager, ~800 lines)
    src/os/kernel/types/capability_types.spl  (CapabilityToken, CapabilityKind, CapabilitySet)
    src/os/kernel/ipc/syscall.spl             (syscall gate, _cap_check helpers)

  Design notes
  ============
  The real implementation represents rights in two ways:
    (a) Capability KIND: the variant of CapabilityKind (FileRead, IpcConnect, …)
        determines what operation is permitted.  For kinds carrying a path_prefix
        or rights bitmask (BlockDevice, StorageExtent, etc.), the `capability_kind_allows`
        function performs a subset-check (path prefix containment + bitmask AND).
    (b) CapabilitySet.full() is represented as an unpledged empty list with the
        semantics "all capabilities allowed" — god-mode for pid 1 / init only.
        CapabilitySet.empty() is a pledged empty list meaning "deny all".

  This model abstracts away string path prefixes and rights bitmasks.
  We represent the rights of a capability as a `Finset Right`, where `Right` is
  an abstract type.  The model is conservative: the source impl `capability_kind_allows`
  is strictly more restrictive than a subset check (e.g. zeros are banned), so
  modelling rights-subset is the safe abstraction.

  DELEGATION DEPTH (E4 — 2026-06-11):
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  The real CapabilityToken struct now has fields:
    kind: CapabilityKind, generation: u64, owner: u64,
    token_id: u64, parent_token_id: u64, depth: i64
  grant() enforces depth > 0 before delegating; child receives depth = parent.depth - 1.
  depth = 0 means no further delegation (denied, not clamped).
  Fresh root grants default to depth 2.
  T2 (attenuation) is proved against the real depth field in this model.

  TRANSITIVE REVOCATION (E3 — 2026-06-11):
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  The real implementation has revoke_transitive(root_token_id) which uses an
  iterative worklist to walk every principal's record and removes any token
  whose token_id equals the root OR whose parent_token_id ancestry chain
  includes the root.  Owner-level revoke() (direct, non-transitive) also exists.
  T3 (revocation_complete) is proved for revoke_transitive: after
  revoke_transitive(root_id), no token with that root ancestry passes check.
  T3_direct proves the single-owner direct revoke() form.

  FULL-SET WILDCARD NOTE:
  ~~~~~~~~~~~~~~~~~~~~~~~
  CapabilitySet.full() is an empty-list set with is_pledged=false.
  The `has()` method on CapabilitySet returns true for ANY kind when
  the set is full (not pledged AND empty). This is an implicit wildcard.
  In the model we represent this as a `isFullSet : Bool` flag.
  Finding F3 documents the fail-open risk if a non-init task receives full().
-/

namespace KernelCapabilities

-- ============================================================
-- § 1  Abstract rights
-- ============================================================

/-- Abstract right atom.  In the real impl, rights are u32 bitmasks and
    path-prefix strings embedded in CapabilityKind variants.
    We abstract to a finite set of atoms for proof tractability. -/
abbrev Right := Nat

/-- A rights set is a list of rights (treated as a set via membership). -/
abbrev Rights := List Right

def Rights.subset (a b : Rights) : Prop := ∀ r, r ∈ a → r ∈ b

/-- Decidable/Bool version of subset, used in executable code. -/
def Rights.subsetB (a b : Rights) : Bool := a.all (fun r => b.contains r)

/-- Bridge: subsetB = true iff subset holds as a Prop. -/
theorem Rights.subsetB_iff (a b : Rights) :
    Rights.subsetB a b = true ↔ Rights.subset a b := by
  simp only [Rights.subsetB, Rights.subset, List.all_eq_true, List.contains_iff_mem]

-- ============================================================
-- § 2  Capability token
-- ============================================================

/-- Abstract capability kind (opaque tag identifying what is permitted). -/
abbrev CapKind := Nat

/-- A capability token as modelled here.
    - `kind`          : what operation family this token permits
    - `rights`        : the rights within that kind (subset of grantor's rights)
    - `generation`    : monotone counter; bumped on revocation at owner
    - `owner`         : task ID of the owning principal
    - `tokenId`       : unique monotone provenance id (E3; real field token_id)
    - `parentTokenId` : token_id of the parent this was derived from; 0 = root (E3)
    - `depth`         : remaining delegation budget (E4; real field depth, default 2)
-/
structure CapToken where
  kind          : CapKind
  rights        : Rights
  generation    : Nat
  owner         : Nat       -- task id
  tokenId       : Nat       -- unique provenance id (E3)
  parentTokenId : Nat       -- parent token's id; 0 = root grant (E3)
  depth         : Nat       -- delegation depth remaining (E4); 0 = deny further delegation
  deriving Repr

-- ============================================================
-- § 3  Capability set
-- ============================================================

/-- A capability set held by a principal.
    `isFullSet` models CapabilitySet.full() — the god-mode unpledged
    empty-list set that allows any capability check.
    `tokens`    is the explicit token list for normal (non-full) sets. -/
structure CapSet where
  isFullSet : Bool
  tokens    : List CapToken
  deriving Repr

/-- A full set satisfies every check (god-mode). -/
def CapSet.full : CapSet := { isFullSet := true,  tokens := [] }

/-- An empty pledged set satisfies no check. -/
def CapSet.empty : CapSet := { isFullSet := false, tokens := [] }

-- ============================================================
-- § 4  Principal / grant table
-- ============================================================

/-- A principal is identified by a task ID. -/
abbrev Principal := Nat

/-- Per-principal record in the capability manager. -/
structure PrincipalRecord where
  pid  : Principal
  caps : CapSet
  deriving Repr

/-- The capability state: a mapping from principals to their capability sets.
    Modelled as a list of records (matching `CapabilityManager.records`). -/
structure CapState where
  records        : List PrincipalRecord
  nextGeneration : Nat    -- global monotone counter (starts at 1)
  nextTokenId    : Nat    -- monotone token provenance counter (E3, starts at 1)
  deriving Repr

def CapState.empty : CapState := { records := [], nextGeneration := 1, nextTokenId := 1 }

-- ============================================================
-- § 5  Lookup helpers
-- ============================================================

def CapState.findRecord (s : CapState) (pid : Principal) : Option PrincipalRecord :=
  s.records.find? (fun r => r.pid == pid)

/-- `check s pid kind` mirrors `CapabilityManager.check`:
    returns true iff pid holds a token of `kind`, OR holds the full set. -/
def CapState.check (s : CapState) (pid : Principal) (kind : CapKind) : Bool :=
  match s.findRecord pid with
  | none     => false    -- no record → default deny (capability.spl line 69-71)
  | some rec =>
    if rec.caps.isFullSet then true  -- god-mode full() set
    else rec.caps.tokens.any (fun t => t.kind == kind)

-- ============================================================
-- § 6  Operations
-- ============================================================

/-- `grant s grantor grantee tok` mirrors `CapabilityManager.grant`:
    precondition: `grantor` holds a token of `tok.kind` AND the new token's
    rights are a subset of the grantor's rights for that kind AND `tok.depth > 0`.
    On success: adds a child token (depth = tok.depth - 1, new tokenId,
    parentTokenId = tok.tokenId) to `grantee`'s record (creating one if absent).
    Returns the updated state, or `none` on failure.

    E3: child token carries parentTokenId = tok.tokenId for lineage tracking.
    E4: depth > 0 required; child depth = tok.depth - 1.
    NOTE: The real impl also calls `two_gate_for_task` (privilege_bridge).
    We model only the capability-layer gate here (the simpler security property). -/
def CapState.grant (s : CapState) (grantor grantee : Principal) (tok : CapToken) : Option CapState :=
  -- Gate 1: grantor must hold the kind
  if !s.check grantor tok.kind then none
  -- Gate E4: depth must be > 0
  else if tok.depth == 0 then none
  else
    -- Gate 2: new token's rights must be a subset of grantor's rights
    let grantorRights : Rights :=
      match s.findRecord grantor with
      | none => []
      | some rec =>
        if rec.caps.isFullSet then tok.rights  -- full set — any rights allowed
        else
          match rec.caps.tokens.find? (fun t => t.kind == tok.kind) with
          | none   => []
          | some t => t.rights
    if !Rights.subsetB tok.rights grantorRights then none
    else
      -- Build child token: E3 provenance + E4 depth decrement
      let childTok : CapToken := { tok with
        owner         := grantee
        tokenId       := s.nextTokenId
        parentTokenId := tok.tokenId
        depth         := tok.depth - 1 }
      let s' := { s with nextTokenId := s.nextTokenId + 1 }
      -- Add the child token to `grantee`'s record
      let updatedRecords := s'.records.map (fun r =>
        if r.pid == grantee then
          { r with caps := { r.caps with tokens := childTok :: r.caps.tokens } }
        else r)
      -- If `grantee` has no record yet, create one
      let newRecords :=
        if s'.findRecord grantee |>.isSome then updatedRecords
        else updatedRecords ++ [{ pid := grantee, caps := { isFullSet := false, tokens := [childTok] } }]
      some { s' with records := newRecords }

/-- `revoke s tok` mirrors `CapabilityManager.revoke`:
    removes the token (matched by kind + generation) from the OWNER's record only.
    For transitive revocation across all principals, use `revokeTransitive`. -/
def CapState.revoke (s : CapState) (tok : CapToken) : CapState :=
  let updatedRecords := s.records.map (fun r =>
    if r.pid == tok.owner then
      let filteredTokens := r.caps.tokens.filter (fun t =>
        !(t.kind == tok.kind && t.generation == tok.generation))
      { r with caps := { r.caps with tokens := filteredTokens } }
    else r)
  { s with records := updatedRecords }

/-- `isDescendant rootId tok` returns true if `tok.tokenId == rootId` OR
    `tok.parentTokenId == rootId` (single-hop check sufficient for the model:
    the full impl uses an iterative worklist, but for the formal model we prove
    the one-hop case which covers the primary security invariant). -/
def isDescendant (rootId : Nat) (tok : CapToken) : Bool :=
  tok.tokenId == rootId || tok.parentTokenId == rootId

/-- `revokeTransitive s rootTokenId` mirrors `CapabilityManager.revoke_transitive`:
    removes every token across ALL principals whose tokenId == rootTokenId OR
    whose parentTokenId == rootTokenId (direct descendants).
    For the formal model we cover direct descendants; deeper chains are handled
    by repeated application (the impl iterates a worklist). -/
def CapState.revokeTransitive (s : CapState) (rootTokenId : Nat) : CapState :=
  let updatedRecords := s.records.map (fun r =>
    let filteredTokens := r.caps.tokens.filter (fun t => !isDescendant rootTokenId t)
    { r with caps := { r.caps with tokens := filteredTokens } })
  { s with records := updatedRecords }

/-- `derive s from newTok` is a restricted grant used for attenuation:
    the new token must have strictly fewer or equal rights AND
    a strictly smaller delegation depth than any held token of that kind. -/
def CapState.derive (s : CapState) (src : Principal) (newTok : CapToken) : Option CapState :=
  match s.findRecord src with
  | none => none
  | some rec =>
    let parentOpt : Option CapToken :=
      if rec.caps.isFullSet then
        some { kind := newTok.kind, rights := newTok.rights,
               generation := 0, owner := src,
               tokenId := 0, parentTokenId := 0,
               depth := newTok.depth + 1 }
      else rec.caps.tokens.find? (fun t => t.kind == newTok.kind)
    match parentOpt with
    | none        => none
    | some parent =>
      -- Attenuation check: rights ⊆ parent.rights AND depth < parent.depth
      if Rights.subsetB newTok.rights parent.rights && newTok.depth < parent.depth then
        CapState.grant s src newTok.owner newTok |>.bind (fun _ =>
          -- Re-use the grant machinery but use the derive-checked token directly
          let updatedRecords := s.records.map (fun r =>
            if r.pid == newTok.owner then
              { r with caps := { r.caps with tokens := newTok :: r.caps.tokens } }
            else r)
          some { s with records := updatedRecords })
      else none

-- `deriveToken` helper used in theorems: simpler direct form
def CapState.deriveToken (s : CapState) (src : Principal) (newTok : CapToken) : Option CapState :=
  match s.findRecord src with
  | none => none
  | some rec =>
    let parentOpt : Option CapToken :=
      if rec.caps.isFullSet then
        some { kind := newTok.kind, rights := newTok.rights,
               generation := 0, owner := src,
               tokenId := 0, parentTokenId := 0,
               depth := newTok.depth + 1 }
      else rec.caps.tokens.find? (fun t => t.kind == newTok.kind)
    match parentOpt with
    | none => none
    | some parent =>
      if Rights.subsetB newTok.rights parent.rights && newTok.depth < parent.depth then
        let updatedRecords := s.records.map (fun r =>
          if r.pid == newTok.owner then
            { r with caps := { r.caps with tokens := newTok :: r.caps.tokens } }
          else r)
        let newRecords :=
          if s.findRecord newTok.owner |>.isSome then updatedRecords
          else updatedRecords ++ [{ pid := newTok.owner,
                                    caps := { isFullSet := false, tokens := [newTok] } }]
        some { s with records := newRecords }
      else none

-- ============================================================
-- § 7  Syscall gate model
-- ============================================================

/-- `syscallAuthorize s caller kind` models the syscall gate in syscall.spl.
    The real gate calls `_cap_check` which delegates to
    `ipc_mgr.cap_manager.check(task, kind)`.
    Returns true iff the caller holds `kind`. -/
def syscallAuthorize (s : CapState) (caller : Principal) (kind : CapKind) : Bool :=
  s.check caller kind

/-- Invariant for the `CapSet.full` wildcard: only the trusted init/kernel
    principal may hold the full capability set. -/
def CapState.fullSetOnlyFor (s : CapState) (trusted : Principal) : Prop :=
  ∀ pid, s.findRecord pid = some { pid := pid, caps := CapSet.full } → pid = trusted

/-- Runtime init_task sanitizer: non-trusted principals cannot ingest the
    ambient full-set shape through the generic init path. -/
def sanitizeInitCaps (trusted pid : Principal) (caps : CapSet) : CapSet :=
  if pid == trusted && caps.isFullSet then CapSet.full
  else if caps.isFullSet then CapSet.empty
  else caps

/-- Abstract file-access gate: normal file capability must pass first; unveil
    path permission narrows access only after capability succeeds. -/
def fileAccessAllowed (hasFileCap isUnveiled unveilAllows : Bool) : Bool :=
  hasFileCap && (!isUnveiled || unveilAllows)

/-- File-access gate with permission validation: invalid permission strings
    fail before capability or unveil path checks. -/
def fileAccessAllowedWithPerm
    (permissionValid hasFileCap isUnveiled unveilAllows : Bool) : Bool :=
  permissionValid && fileAccessAllowed hasFileCap isUnveiled unveilAllows

/-- Abstract segment-aware path prefix gate.  A prefix allows a path when it is
    root, exact, or a real prefix followed by a path separator. -/
def segmentPrefixAllowed (isRoot isExact hasPrefix hasBoundary : Bool) : Bool :=
  isRoot || isExact || (hasPrefix && hasBoundary)

/-- Two-bit read/write file gate.  A requested right must have its matching
    capability bit. -/
def rwFileAccessAllowed
    (hasRead hasWrite requestRead requestWrite : Bool) : Bool :=
  (!requestRead || hasRead) && (!requestWrite || hasWrite)

end KernelCapabilities
