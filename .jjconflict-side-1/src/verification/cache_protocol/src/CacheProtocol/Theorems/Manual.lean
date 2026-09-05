/-
  CacheProtocol.Theorems.Manual — DURABLE MANUAL PROOFS.
  The generator (src/app/gen_cache_model/main.spl) never writes this directory.

  Contents:
    all_semantic_fields_visible — encode equality ⟺ all 21 semantic fields equal
    no_false_hit                — re-proved over the 21-field v2 key
    aop_group_change_visible    — AOP soundness over the refined group roots:
                                  a change in ANY of the four AOP carriers
                                  (pos 13, 16, 17, 18) changes the encoding
    aop_change_visible          — v1 statement re-derived verbatim over v2
    v1_prefix_compatible        — with the six v2 suffix fields held fixed, the
                                  v2 encoding is exactly as discriminating as
                                  the PROVEN v1 encoding (cache_identity)
    aop_roots_reorder_hits, block_roots_reorder_hits — new set fields are
                                  order-independent (concrete, by decide)
-/
import CacheProtocol.Generated.Model
import CacheProtocol.Generated.Visibility
import CacheIdentity.Model
import CacheIdentity.Theorems

namespace CacheProtocol

-- ---------------------------------------------------------------------------
-- 1. all_semantic_fields_visible
-- ---------------------------------------------------------------------------

/-- Encodings agree exactly when ALL 21 semantic fields (after set
    canonicalisation) agree. Left-to-right: no aliasing between distinct
    semantic inputs. Right-to-left: nothing outside the 21 fields can
    perturb the digest input. -/
theorem all_semantic_fields_visible (k1 k2 : ActionKey) :
    encode k1 = encode k2 ↔
      (k1.domain = k2.domain ∧
       k1.compilerExe = k2.compilerExe ∧
       k1.liveCompilerSrc = k2.liveCompilerSrc ∧
       k1.schemaVersion = k2.schemaVersion ∧
       k1.targetTriple = k2.targetTriple ∧
       k1.hostArch = k2.hostArch ∧
       sortStrs k1.cfgFeatures = sortStrs k2.cfgFeatures ∧
       k1.stdlibVariant = k2.stdlibVariant ∧
       k1.runtimeFamily = k2.runtimeFamily ∧
       k1.sourceContent = k2.sourceContent ∧
       k1.resolutionWitness = k2.resolutionWitness ∧
       sortDeps k1.deps = sortDeps k2.deps ∧
       k1.macroRoot = k2.macroRoot ∧
       k1.aopSelection = k2.aopSelection ∧
       sortStrs k1.ctEnvInputs = sortStrs k2.ctEnvInputs ∧
       k1.schemaDigest = k2.schemaDigest ∧
       k1.aopSurfaceRoot = k2.aopSurfaceRoot ∧
       sortStrs k1.aopCandidatePartitionRoots = sortStrs k2.aopCandidatePartitionRoots ∧
       k1.aopWeaveRoot = k2.aopWeaveRoot ∧
       sortStrs k1.blockManifestRoots = sortStrs k2.blockManifestRoots ∧
       k1.resultKind = k2.resultKind) := by
  rw [encode_eq_iff_canon]
  simp only [canonKey, CanonKey.mk.injEq]

-- ---------------------------------------------------------------------------
-- 2. AOP soundness over the refined group (plan §2b)
-- ---------------------------------------------------------------------------

/-- v1 statement re-derived verbatim over the v2 key: the coarse pos-13 AOP
    root is still individually visible (it was retained, not replaced). -/
theorem aop_change_visible (k1 k2 : ActionKey)
    (h : k1.aopSelection ≠ k2.aopSelection) : encode k1 ≠ encode k2 :=
  aop_selection_change_visible k1 k2 h

/-- The refined statement: a change in ANY of the four AOP identity carriers —
    the retained coarse root (pos 13) or the split v2 roots (pos 16, 17, 18) —
    is visible in the encoding. -/
theorem aop_group_change_visible (k1 k2 : ActionKey)
    (h : k1.aopSelection ≠ k2.aopSelection ∨
         k1.aopSurfaceRoot ≠ k2.aopSurfaceRoot ∨
         sortStrs k1.aopCandidatePartitionRoots ≠ sortStrs k2.aopCandidatePartitionRoots ∨
         k1.aopWeaveRoot ≠ k2.aopWeaveRoot) :
    encode k1 ≠ encode k2 := by
  rcases h with h | h | h | h
  · exact aop_selection_change_visible k1 k2 h
  · exact aop_surface_root_change_visible k1 k2 h
  · exact aop_candidate_partition_roots_change_visible k1 k2 h
  · exact aop_weave_root_change_visible k1 k2 h

-- ---------------------------------------------------------------------------
-- 3. Cache soundness — no_false_hit over the 21-field key
-- ---------------------------------------------------------------------------

structure Entry where
  key      : ActionKey
  artifact : Nat
  deriving Repr

def WellFormed (realize : CanonKey → Nat) (tbl : List Entry) : Prop :=
  ∀ e ∈ tbl, e.artifact = realize (canonKey e.key)

def lookup (tbl : List Entry) (k : ActionKey) : Option Nat :=
  (tbl.find? (fun e => decide (encode e.key = encode k))).map (·.artifact)

/-- A v2 cache hit returns exactly what re-realising the current canonical key
    would produce — the v1 proof re-established over all 21 fields. -/
theorem no_false_hit (realize : CanonKey → Nat) (tbl : List Entry)
    (k : ActionKey) (a : Nat)
    (hwf : WellFormed realize tbl) (hhit : lookup tbl k = some a) :
    a = realize (canonKey k) := by
  unfold lookup at hhit
  cases hfind : tbl.find? (fun e => decide (encode e.key = encode k)) with
  | none => rw [hfind] at hhit; simp at hhit
  | some e =>
    rw [hfind] at hhit
    simp only [Option.map_some, Option.some.injEq] at hhit
    have hmem : e ∈ tbl := List.mem_of_find?_eq_some hfind
    have hkeq : encode e.key = encode k := by
      have hpred := List.find?_some hfind
      simpa using hpred
    have hcan : canonKey e.key = canonKey k := encode_determines_canon _ _ hkeq
    have hart : e.artifact = realize (canonKey e.key) := hwf e hmem
    rw [← hhit, hart, hcan]

-- ---------------------------------------------------------------------------
-- 4. v1 prefix compatibility (bridge to the PROVEN cache_identity model)
-- ---------------------------------------------------------------------------

/-- Project a v2 key onto the v1 field set (positions 0..14). -/
def convDep (d : Dep) : CacheIdentity.Dep :=
  { moduleId := d.moduleId, ifaceDigest := d.ifaceDigest }

def toV1 (k : ActionKey) : CacheIdentity.ActionKey :=
  { domain := k.domain, compilerExe := k.compilerExe, liveCompilerSrc := k.liveCompilerSrc
  , schemaVersion := k.schemaVersion, targetTriple := k.targetTriple, hostArch := k.hostArch
  , cfgFeatures := k.cfgFeatures, stdlibVariant := k.stdlibVariant
  , runtimeFamily := k.runtimeFamily, sourceContent := k.sourceContent
  , resolutionWitness := k.resolutionWitness, deps := k.deps.map convDep
  , macroRoot := k.macroRoot, aopSelection := k.aopSelection
  , ctEnvInputs := k.ctEnvInputs }

theorem strLe_eq (a b : String) : CacheIdentity.strLe a b = strLe a b := rfl

theorem insStr_eq (a : String) (l : List String) :
    CacheIdentity.insStr a l = insStr a l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [CacheIdentity.insStr, insStr, strLe_eq, ih]

theorem sortStrs_eq (l : List String) : CacheIdentity.sortStrs l = sortStrs l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [CacheIdentity.sortStrs, sortStrs, ih, insStr_eq]

theorem depLe_conv (a b : Dep) :
    CacheIdentity.depLe (convDep a) (convDep b) = depLe a b := rfl

theorem convDep_inj (a b : Dep) (h : convDep a = convDep b) : a = b := by
  cases a; cases b
  simp [convDep, CacheIdentity.Dep.mk.injEq] at h
  simp [h.1, h.2]

theorem map_convDep_inj (l1 l2 : List Dep) (h : l1.map convDep = l2.map convDep) :
    l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => rfl
    | cons b bs => simp at h
  | cons a as ih =>
    cases l2 with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp [convDep_inj a b h.1, ih bs h.2]

theorem insDep_conv (a : Dep) (l : List Dep) :
    CacheIdentity.insDep (convDep a) (l.map convDep) = (insDep a l).map convDep := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, CacheIdentity.insDep, insDep, depLe_conv]
    by_cases h : depLe a b
    · simp [h]
    · simp [h, ih]

theorem sortDeps_conv (l : List Dep) :
    CacheIdentity.sortDeps (l.map convDep) = (sortDeps l).map convDep := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, CacheIdentity.sortDeps, sortDeps, ih, insDep_conv]

/-- The six v2 suffix fields (positions 15..20) agree between k1 and k2. -/
def SuffixFixed (k1 k2 : ActionKey) : Prop :=
  k1.schemaDigest = k2.schemaDigest ∧
  k1.aopSurfaceRoot = k2.aopSurfaceRoot ∧
  sortStrs k1.aopCandidatePartitionRoots = sortStrs k2.aopCandidatePartitionRoots ∧
  k1.aopWeaveRoot = k2.aopWeaveRoot ∧
  sortStrs k1.blockManifestRoots = sortStrs k2.blockManifestRoots ∧
  k1.resultKind = k2.resultKind

/-- PREFIX COMPATIBILITY. When the v2 suffix is held fixed (e.g. all sentinels,
    the pre-rollout state), the v2 encoding discriminates keys exactly as the
    proven v1 encoding does. The v1 safety corpus therefore carries over to the
    v2 deployment unchanged until suffix producers land. -/
theorem v1_prefix_compatible (k1 k2 : ActionKey) (hs : SuffixFixed k1 k2) :
    encode k1 = encode k2 ↔
      CacheIdentity.encode (toV1 k1) = CacheIdentity.encode (toV1 k2) := by
  obtain ⟨s15, s16, s17, s18, s19, s20⟩ := hs
  rw [all_semantic_fields_visible, CacheIdentity.encode_eq_iff_canon]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -, -, -, -, -⟩
    simp [CacheIdentity.canonKey, toV1,
          sortStrs_eq, sortDeps_conv, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h10, h11, h12, h13, h14]
  · intro h
    simp only [CacheIdentity.canonKey, toV1, CacheIdentity.CanonKey.mk.injEq,
               sortStrs_eq, sortDeps_conv] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
    have h11' : sortDeps k1.deps = sortDeps k2.deps := map_convDep_inj _ _ h11
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11', h12, h13, h14,
           s15, s16, s17, s18, s19, s20⟩

-- ---------------------------------------------------------------------------
-- 5. Order-independence of the two new set fields (concrete, machine-checked)
-- ---------------------------------------------------------------------------

private def kBase (aopRoots blockRoots : List String) : ActionKey :=
  { domain := "simple/interpreter-module/v2", compilerExe := "c", liveCompilerSrc := "s"
  , schemaVersion := 2, targetTriple := "x86_64-linux", hostArch := "x86_64"
  , cfgFeatures := [], stdlibVariant := "nogc_async", runtimeFamily := "nogc"
  , sourceContent := "src", resolutionWitness := "rw", deps := []
  , macroRoot := "m", aopSelection := "aop", ctEnvInputs := []
  , schemaDigest := "sd", aopSurfaceRoot := sentinelDigest
  , aopCandidatePartitionRoots := aopRoots, aopWeaveRoot := sentinelDigest
  , blockManifestRoots := blockRoots, resultKind := .interpreter_module }

/-- Reordering pos-17 (aop_candidate_partition_roots) does not change the encoding. -/
theorem aop_roots_reorder_hits :
    encode (kBase ["r2", "r1"] []) = encode (kBase ["r1", "r2"] []) := by decide

/-- Reordering pos-19 (block_manifest_roots) does not change the encoding. -/
theorem block_roots_reorder_hits :
    encode (kBase [] ["b2", "b1"]) = encode (kBase [] ["b1", "b2"]) := by decide

/-- Sanity (negative): a different result kind DOES change the encoding. -/
theorem result_kind_differs_misses :
    encode { kBase [] [] with resultKind := .object_file } ≠ encode (kBase [] []) := by decide

end CacheProtocol
