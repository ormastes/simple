/-
  OsEnforcement.ContainerIsolation — pure model of the SimpleOS container
  namespace enforcement boundary, and a sorry-free proof of the deny-by-default
  isolation invariants (master plan §6 / §21).

  Source of truth (T2A — 2026-07-27):
    src/os/kernel/loader/container_namespace.spl
      struct ContainerNamespaceView { root: text, pids: [u64] }
      container_view_allows_path / container_view_allows_pid
      _split_components  (path normalization; collapses "." and "..")

  Real semantics being modelled
  =============================
  A ContainerNamespaceView confines a container to a VFS subtree `root` and a
  process-view set `pids`. It is DENY-BY-DEFAULT:
    * container_view_allows_path denies when root == "" or "/" (rootless), when
      root has zero components, when the request has fewer components than root,
      or when any root component differs from the request's — i.e. root must be a
      COMPONENT-WISE PREFIX of the request (starts_with is deliberately avoided,
      so "/c1" does NOT match "/c11").
    * _split_components collapses "." and drops the last accumulated component on
      "..", returning nil (a DENY signal) when ".." pops above the fs root.
    * container_view_allows_pid denies every pid not explicitly in `pids`.

  Modelling notes
  ===============
  Path components are abstracted as `List Nat` (each segment an id).  The `..`
  operator is modelled by the sentinel `DOTDOT = 0`; `normalize` mirrors
  `_split_components`, returning `none` exactly when a `..` escapes above the
  root.  Core Lean 4 only (List/Nat/Bool, no Mathlib), matching the empty
  package manifest and the KernelCapabilities modules' idiom.

  Headline theorems (SPipe manual layer):
    OsEnforcement.rootless_denies_all       (CI1)
    OsEnforcement.outside_root_denied        (CI2)
    OsEnforcement.traversal_cannot_escape    (CI3, general + escape + concrete)
    OsEnforcement.pid_outside_set_denied     (CI4)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Component-wise prefix containment
-- ============================================================

/-- `prefixB root path` is true iff `root` is a component-wise prefix of `path`.
    Mirrors the `while i < root_comps.len(): if req[i] != root[i] return false`
    loop plus the `req.len() < root.len()` early-deny in
    `container_view_allows_path`. -/
def prefixB : List Nat → List Nat → Bool
  | [],      _       => true
  | _ :: _,  []      => false
  | a :: as, b :: bs => a == b && prefixB as bs

/-- `allowsPath root path` mirrors `container_view_allows_path`.
    An empty `root` (rootless / "" / "/" / zero components) denies EVERYTHING;
    otherwise the request must have `root` as a component-wise prefix. -/
def allowsPath (root path : List Nat) : Bool :=
  match root with
  | []     => false
  | _ :: _ => prefixB root path

/-- On a non-empty root, `allowsPath` is exactly the prefix test. -/
theorem allowsPath_cons (a : Nat) (as path : List Nat) :
    allowsPath (a :: as) path = prefixB (a :: as) path := rfl

-- ============================================================
-- § 2  Process-view membership
-- ============================================================

/-- `allowsPid pids p` mirrors `container_view_allows_pid`: allow iff `p` is in
    the explicit set.  The empty set denies all pids. -/
def allowsPid (pids : List Nat) (p : Nat) : Bool := pids.contains p

-- ============================================================
-- § 3  Path normalization (`_split_components`)
-- ============================================================

/-- Sentinel component id for `..`. -/
abbrev DOTDOT : Nat := 0

/-- Accumulator form of `_split_components`: fold left, dropping the last
    accumulated component on `..`, returning `none` when `..` pops above the
    empty accumulator (the nil / DENY signal in the source). -/
def normAux : List Nat → List Nat → Option (List Nat)
  | [],        acc => some acc
  | c :: rest, acc =>
    if c = DOTDOT then
      match acc with
      | []     => none
      | _ :: _ => normAux rest acc.dropLast
    else
      normAux rest (acc ++ [c])

/-- `normalize path` mirrors `_split_components(path)`: `none` iff traversal
    escapes above the fs root. -/
def normalize (path : List Nat) : Option (List Nat) := normAux path []

/-- Post-normalization VFS decision: an escaping traversal (`none`) is DENIED;
    otherwise apply `allowsPath` to the normalized components. -/
def pathDecision (root path : List Nat) : Bool :=
  match normalize path with
  | none    => false
  | some np => allowsPath root np

-- ============================================================
-- § 4  The isolation invariants — CI1 .. CI4
-- ============================================================

/-- CI1 — rootless_denies_all:
    the rootless view (empty root, empty pid set) denies every path and pid. -/
theorem rootless_denies_all (path : List Nat) (p : Nat) :
    allowsPath [] path = false ∧ allowsPid [] p = false := by
  constructor
  · rfl
  · rfl

/-- CI2 — outside_root_denied:
    a path that does not have the (non-empty) container root as a component-wise
    prefix — e.g. a sibling root — is denied. -/
theorem outside_root_denied (a : Nat) (as path : List Nat)
    (h : prefixB (a :: as) path = false) :
    allowsPath (a :: as) path = false := by
  rw [allowsPath_cons]; exact h

/-- Concrete CI2 witness: root `/c1` denies sibling `/c11` (component ids 1 vs
    11 — the exact "starts_with would wrongly match" case the source avoids). -/
theorem outside_root_denied_sibling :
    allowsPath [1] [11] = false := by decide

/-- CI3 (general) — traversal_cannot_escape:
    if a path normalizes to components that do NOT keep `root` as a prefix, the
    post-normalization decision denies it. Covers `../` escapes to sibling
    subtrees. -/
theorem traversal_cannot_escape (root np path : List Nat)
    (hnorm : normalize path = some np)
    (hpre : prefixB root np = false) :
    pathDecision root path = false := by
  unfold pathDecision
  rw [hnorm]
  cases root with
  | nil       => rfl
  | cons a as => exact hpre

/-- CI3 (escape) — a traversal that pops above the fs root (`normalize = none`)
    is denied for every root. -/
theorem traversal_escape_denied (root path : List Nat)
    (hnorm : normalize path = none) :
    pathDecision root path = false := by
  unfold pathDecision
  rw [hnorm]

/-- CI3 (concrete) — under root `/c1`, the traversal `/c1/../c2` normalizes to
    `/c2` and is DENIED; and `/..` (pop above fs root) is denied. -/
theorem traversal_cannot_escape_concrete :
    pathDecision [1] [1, DOTDOT, 2] = false ∧ pathDecision [1] [DOTDOT] = false := by
  constructor
  · decide
  · decide

/-- CI4 — pid_outside_set_denied:
    a pid not in the container's process-view set is denied. -/
theorem pid_outside_set_denied (pids : List Nat) (p : Nat)
    (h : ¬ p ∈ pids) :
    allowsPid pids p = false := by
  unfold allowsPid
  cases hcp : pids.contains p with
  | false => rfl
  | true  => exact absurd (List.contains_iff_mem.mp hcp) h

-- Axiom audit (must report only propext/Classical.choice/Quot.sound style, no sorryAx)
#print axioms rootless_denies_all
#print axioms traversal_cannot_escape

end OsEnforcement
