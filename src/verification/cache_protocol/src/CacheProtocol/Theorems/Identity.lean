/-
  CacheProtocol.Theorems.Identity — DURABLE MANUAL PROOFS.
  Regeneration of Generated/* must NEVER touch this file.

  Re-derivation status of the ten CacheIdentity theorems over the 21-field key
  (c0_schema_freeze_2026-08-09.md §3):

    carried over by regeneration of the same mechanical proof (Generated/):
      encode_determines_canon, canon_determines_encode, encode_eq_iff_canon
      (same tactic pattern, 21 obtain-components instead of 15 — plus one
       genuinely new step: ResultKind.name_inj, because pos 20 is encoded by
       name, so injectivity of the name map is a new proof obligation)
    carried over verbatim as instances of the generic lemma (Generated/):
      source_change_visible → source_content_change_visible
      deps_change_visible, macro_change_visible → macro_root_change_visible,
      resolution_change_visible → resolution_witness_change_visible,
      compiler_change_visible → live_compiler_src_change_visible,
      aop_change_visible → aop_selection_change_visible (retained verbatim:
        while fields 16–18 hold sentinels, pos 13 is the sole AOP identity
        carrier; the new aop_surface/candidate/weave theorems sit BESIDE it)
    really re-proved here over the 21-field key:
      no_false_hit (the v1 proof is the 15-field special case)
      deps_reorder_hits, cfg_reorder_hits (new 21-field witness key), plus the
      two NEW set fields: aop_roots_reorder_hits, block_roots_reorder_hits
    unchanged, still lives in CacheIdentity (orthogonal to field count):
      stamp_fast_eq_strict

  Assumptions (stated, not proved):
    * sha256 collision resistance: digest equality ⇒ encode equality.
    * deterministic build actions: `realize` is a function of the canonical key.
    * the byte-level framing (encodeString) is injective; proven injectivity is
      at the Canon term level. Cross-language agreement: Generated/Golden.lean.
    * trusted CI boundary for promotion is out of scope of this file.

  No sorry, no admit, no axioms.
-/
import CacheProtocol.Generated.Model
import CacheProtocol.Generated.FieldTheorems

namespace CacheProtocol

-- ---------------------------------------------------------------------------
-- Legacy v1 theorem names (kept so callers of CacheIdentity's statements can
-- reference the v2 equivalents under the frozen names)
-- ---------------------------------------------------------------------------

theorem source_change_visible (k1 k2 : ActionKey)
    (h : k1.sourceContent ≠ k2.sourceContent) : encode k1 ≠ encode k2 :=
  source_content_change_visible k1 k2 h

theorem macro_change_visible (k1 k2 : ActionKey)
    (h : k1.macroRoot ≠ k2.macroRoot) : encode k1 ≠ encode k2 :=
  macro_root_change_visible k1 k2 h

theorem resolution_change_visible (k1 k2 : ActionKey)
    (h : k1.resolutionWitness ≠ k2.resolutionWitness) : encode k1 ≠ encode k2 :=
  resolution_witness_change_visible k1 k2 h

theorem compiler_change_visible (k1 k2 : ActionKey)
    (h : k1.liveCompilerSrc ≠ k2.liveCompilerSrc) : encode k1 ≠ encode k2 :=
  live_compiler_src_change_visible k1 k2 h

/-- Retained verbatim (freeze §3): pos 13 stays the complete AOP soundness
    statement while 16–18 carry sentinels. -/
theorem aop_change_visible (k1 k2 : ActionKey)
    (h : k1.aopSelection ≠ k2.aopSelection) : encode k1 ≠ encode k2 :=
  aop_selection_change_visible k1 k2 h

-- ---------------------------------------------------------------------------
-- no_false_hit — re-proved over the 21-field key
-- ---------------------------------------------------------------------------

/-- A cache hit returns exactly what re-realising the current canonical key
    would produce. Uses `WellFormed` + 21-field injectivity. -/
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
-- Prefix compatibility — the v1 fields alone decide identity while the v2
-- suffix fields agree (e.g. both keys carry the fixed sentinels)
-- ---------------------------------------------------------------------------

/-- The v2 suffix (positions 15–20) agrees between two keys — in particular
    true whenever both hold the fixed sentinel values, i.e. before any v2
    producer is wired. -/
def SuffixAgrees (k1 k2 : ActionKey) : Prop :=
  k1.schemaDigest = k2.schemaDigest ∧
  k1.aopSurfaceRoot = k2.aopSurfaceRoot ∧
  sortStrs k1.aopCandidatePartitionRoots = sortStrs k2.aopCandidatePartitionRoots ∧
  k1.aopWeaveRoot = k2.aopWeaveRoot ∧
  sortStrs k1.blockManifestRoots = sortStrs k2.blockManifestRoots ∧
  k1.resultKind = k2.resultKind

/-- The v1 canonical encoding shape over the frozen prefix fields — exactly
    CacheIdentity.encode transported to the v2 record. -/
def encodeV1Prefix (k : ActionKey) : Canon :=
  Canon.tag k.domain <|
    Canon.pair (.tag "compilerExe"       (.str k.compilerExe))       <|
    Canon.pair (.tag "liveCompilerSrc"   (.str k.liveCompilerSrc))   <|
    Canon.pair (.tag "schemaVersion"     (.nat k.schemaVersion))     <|
    Canon.pair (.tag "targetTriple"      (.str k.targetTriple))      <|
    Canon.pair (.tag "hostArch"          (.str k.hostArch))          <|
    Canon.pair (.tag "cfgFeatures"       (.strs (sortStrs k.cfgFeatures))) <|
    Canon.pair (.tag "stdlibVariant"     (.str k.stdlibVariant))     <|
    Canon.pair (.tag "runtimeFamily"     (.str k.runtimeFamily))     <|
    Canon.pair (.tag "sourceContent"     (.str k.sourceContent))     <|
    Canon.pair (.tag "resolutionWitness" (.str k.resolutionWitness)) <|
    Canon.pair (.tag "deps"              (.deps (sortDeps k.deps)))  <|
    Canon.pair (.tag "macroRoot"         (.str k.macroRoot))         <|
    Canon.pair (.tag "aopSelection"      (.str k.aopSelection))      <|
    Canon.tag  "ctEnvInputs"             (.strs (sortStrs k.ctEnvInputs))

/-- PREFIX-COMPATIBILITY. While the v2 suffix fields agree (sentinel era),
    v2 identity coincides exactly with v1 identity: the extended encoder hits
    iff the v1 encoder would hit. So appending fields 15–20 cannot split or
    merge any v1 cache equivalence class until a producer lands. -/
theorem sentinel_prefix_compat (k1 k2 : ActionKey) (hs : SuffixAgrees k1 k2) :
    (encode k1 = encode k2 ↔ encodeV1Prefix k1 = encodeV1Prefix k2) := by
  obtain ⟨hsd, hasr, hacpr, hawr, hbmr, hrk⟩ := hs
  constructor
  · intro h
    have hc := encode_determines_canon k1 k2 h
    have hd    := congrArg CanonKey.domain hc
    have hce   := congrArg CanonKey.compilerExe hc
    have hlcs  := congrArg CanonKey.liveCompilerSrc hc
    have hsv   := congrArg CanonKey.schemaVersion hc
    have htt   := congrArg CanonKey.targetTriple hc
    have hha   := congrArg CanonKey.hostArch hc
    have hcfg  := congrArg CanonKey.cfgFeatures hc
    have hstd  := congrArg CanonKey.stdlibVariant hc
    have hrf   := congrArg CanonKey.runtimeFamily hc
    have hsc   := congrArg CanonKey.sourceContent hc
    have hrw   := congrArg CanonKey.resolutionWitness hc
    have hdeps := congrArg CanonKey.deps hc
    have hmr   := congrArg CanonKey.macroRoot hc
    have haop  := congrArg CanonKey.aopSelection hc
    have hcte  := congrArg CanonKey.ctEnvInputs hc
    simp only [canonKey] at hd hce hlcs hsv htt hha hcfg hstd hrf hsc hrw hdeps hmr haop hcte
    simp only [encodeV1Prefix, hd, hce, hlcs, hsv, htt, hha, hcfg, hstd, hrf,
               hsc, hrw, hdeps, hmr, haop, hcte]
  · intro h
    simp only [encodeV1Prefix, Canon.tag.injEq, Canon.pair.injEq, Canon.str.injEq,
               Canon.nat.injEq, Canon.strs.injEq, Canon.deps.injEq, true_and] at h
    obtain ⟨hd, hce, hlcs, hsv, htt, hha, hcfg, hstd, hrf, hsc, hrw, hdeps, hmr,
            haop, hcte⟩ := h
    simp only [encode, hd, hce, hlcs, hsv, htt, hha, hcfg, hstd, hrf, hsc, hrw,
               hdeps, hmr, haop, hcte, hsd, hasr, hacpr, hawr, hbmr, hrk]

-- ---------------------------------------------------------------------------
-- Order-independence — reordered set fields still hit (concrete, `decide`)
-- ---------------------------------------------------------------------------

private def dA : Dep := { moduleId := "a", ifaceDigest := "11" }
private def dB : Dep := { moduleId := "b", ifaceDigest := "22" }

private def kBase (ds : List Dep) (cfg roots blocks : List String) : ActionKey :=
  { domain := "simple/interpreter-module/v2", compilerExe := "c", liveCompilerSrc := "s"
  , schemaVersion := 2, targetTriple := "x86_64-linux", hostArch := "x86_64"
  , cfgFeatures := cfg, stdlibVariant := "nogc_async", runtimeFamily := "nogc"
  , sourceContent := "src", resolutionWitness := "rw", deps := ds
  , macroRoot := "m", aopSelection := "aop", ctEnvInputs := []
  , schemaDigest := "sd", aopSurfaceRoot := "asr"
  , aopCandidatePartitionRoots := roots, aopWeaveRoot := "awr"
  , blockManifestRoots := blocks, resultKind := .interpreterModule }

theorem deps_reorder_hits :
    encode (kBase [dB, dA] [] [] []) = encode (kBase [dA, dB] [] [] []) := by decide

theorem cfg_reorder_hits :
    encode (kBase [] ["z", "a"] [] []) = encode (kBase [] ["a", "z"] [] []) := by decide

/-- NEW v2 obligation: reordering aop_candidate_partition_roots still hits. -/
theorem aop_roots_reorder_hits :
    encode (kBase [] [] ["r2", "r1"] []) = encode (kBase [] [] ["r1", "r2"] []) := by decide

/-- NEW v2 obligation: reordering block_manifest_roots still hits. -/
theorem block_roots_reorder_hits :
    encode (kBase [] [] [] ["b9", "b1"]) = encode (kBase [] [] [] ["b1", "b9"]) := by decide

/-- Sanity (negative): a different result_kind DOES change the encoding. -/
theorem result_kind_differs_misses :
    encode { kBase [] [] [] [] with resultKind := .mirModule }
      ≠ encode (kBase [] [] [] []) := by decide

end CacheProtocol
