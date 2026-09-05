/-
  CacheIdentity.Theorems — safety proofs for the Option-C cache identity layer.

  All proved without `sorry`.

  Injectivity core
    encode_determines_canon   — encode k1 = encode k2 → canonKey k1 = canonKey k2
    canon_determines_encode   — canonKey k1 = canonKey k2 → encode k1 = encode k2
    encode_eq_iff_canon       — encode factors *exactly* through the canonical key

  Field completeness (no omitted-input false hit) — contrapositives of the above
    source_change_visible, deps_change_visible, aop_change_visible,
    macro_change_visible, resolution_change_visible, compiler_change_visible

  Cache soundness
    no_false_hit              — a hit returns exactly what re-realisation would produce

  C ≡ A bridge
    stamp_fast_eq_strict      — valid stamp ⇒ fast-path SHA = strict-path SHA

  Order-independence (completeness: reordered set-fields still hit)
    deps_reorder_hits, cfg_reorder_hits  (concrete, machine-checked by `decide`)
-/
import CacheIdentity.Model

namespace CacheIdentity

-- ---------------------------------------------------------------------------
-- 1. Injectivity core
-- ---------------------------------------------------------------------------

/-- SAFETY CORE.  If two ActionKeys encode to the same canonical term, their
    canonical keys are equal — every semantic input is recovered from the
    encoding.  A digest collision (encode-equality, under sha256 collision
    resistance) therefore implies the keys are semantically identical: no false
    hit. -/
theorem encode_determines_canon (k1 k2 : ActionKey)
    (h : encode k1 = encode k2) : canonKey k1 = canonKey k2 := by
  simp only [encode, Canon.tag.injEq, Canon.pair.injEq, Canon.str.injEq,
             Canon.nat.injEq, Canon.strs.injEq, Canon.deps.injEq,
             true_and] at h
  obtain ⟨hd, hce, hlcs, hsv, htt, hha, hcfg, hstd, hrf, hsc, hrw, hdeps, hmr, haop, hcte⟩ := h
  simp only [canonKey, hd, hce, hlcs, hsv, htt, hha, hstd, hrf, hsc, hrw, hmr, haop,
             hcfg, hdeps, hcte]

/-- Converse: semantically-equal keys encode identically (so they hit the same
    entry — the completeness side). -/
theorem canon_determines_encode (k1 k2 : ActionKey)
    (h : canonKey k1 = canonKey k2) : encode k1 = encode k2 := by
  have hd   : k1.domain            = k2.domain            := congrArg CanonKey.domain h
  have hce  : k1.compilerExe       = k2.compilerExe       := congrArg CanonKey.compilerExe h
  have hlcs : k1.liveCompilerSrc   = k2.liveCompilerSrc   := congrArg CanonKey.liveCompilerSrc h
  have hsv  : k1.schemaVersion     = k2.schemaVersion     := congrArg CanonKey.schemaVersion h
  have htt  : k1.targetTriple      = k2.targetTriple      := congrArg CanonKey.targetTriple h
  have hha  : k1.hostArch          = k2.hostArch          := congrArg CanonKey.hostArch h
  have hcfg : sortStrs k1.cfgFeatures = sortStrs k2.cfgFeatures := congrArg CanonKey.cfgFeatures h
  have hstd : k1.stdlibVariant     = k2.stdlibVariant     := congrArg CanonKey.stdlibVariant h
  have hrf  : k1.runtimeFamily     = k2.runtimeFamily     := congrArg CanonKey.runtimeFamily h
  have hsc  : k1.sourceContent     = k2.sourceContent     := congrArg CanonKey.sourceContent h
  have hrw  : k1.resolutionWitness = k2.resolutionWitness := congrArg CanonKey.resolutionWitness h
  have hdeps: sortDeps k1.deps     = sortDeps k2.deps     := congrArg CanonKey.deps h
  have hmr  : k1.macroRoot         = k2.macroRoot         := congrArg CanonKey.macroRoot h
  have haop : k1.aopSelection      = k2.aopSelection      := congrArg CanonKey.aopSelection h
  have hcte : sortStrs k1.ctEnvInputs = sortStrs k2.ctEnvInputs := congrArg CanonKey.ctEnvInputs h
  simp only [encode, hd, hce, hlcs, hsv, htt, hha, hcfg, hstd, hrf, hsc, hrw,
             hdeps, hmr, haop, hcte]

/-- encode factors exactly through canonKey: equal encodings ⟺ equal canonical keys. -/
theorem encode_eq_iff_canon (k1 k2 : ActionKey) :
    encode k1 = encode k2 ↔ canonKey k1 = canonKey k2 :=
  ⟨encode_determines_canon k1 k2, canon_determines_encode k1 k2⟩

-- ---------------------------------------------------------------------------
-- 2. Field completeness — every input is observable (contrapositives)
-- ---------------------------------------------------------------------------

private theorem field_change_visible {α} (proj : CanonKey → α) (k1 k2 : ActionKey)
    (h : proj (canonKey k1) ≠ proj (canonKey k2)) : encode k1 ≠ encode k2 := by
  intro he
  exact h (congrArg proj (encode_determines_canon k1 k2 he))

theorem source_change_visible (k1 k2 : ActionKey)
    (h : k1.sourceContent ≠ k2.sourceContent) : encode k1 ≠ encode k2 :=
  field_change_visible CanonKey.sourceContent k1 k2 h

theorem deps_change_visible (k1 k2 : ActionKey)
    (h : sortDeps k1.deps ≠ sortDeps k2.deps) : encode k1 ≠ encode k2 :=
  field_change_visible CanonKey.deps k1 k2 h

theorem aop_change_visible (k1 k2 : ActionKey)
    (h : k1.aopSelection ≠ k2.aopSelection) : encode k1 ≠ encode k2 :=
  field_change_visible CanonKey.aopSelection k1 k2 h

theorem macro_change_visible (k1 k2 : ActionKey)
    (h : k1.macroRoot ≠ k2.macroRoot) : encode k1 ≠ encode k2 :=
  field_change_visible CanonKey.macroRoot k1 k2 h

theorem resolution_change_visible (k1 k2 : ActionKey)
    (h : k1.resolutionWitness ≠ k2.resolutionWitness) : encode k1 ≠ encode k2 :=
  field_change_visible CanonKey.resolutionWitness k1 k2 h

theorem compiler_change_visible (k1 k2 : ActionKey)
    (h : k1.liveCompilerSrc ≠ k2.liveCompilerSrc) : encode k1 ≠ encode k2 :=
  field_change_visible CanonKey.liveCompilerSrc k1 k2 h

-- ---------------------------------------------------------------------------
-- 3. Cache soundness — no false hit
-- ---------------------------------------------------------------------------

/-- A cache hit returns exactly the artifact that re-realising the current
    canonical key would produce.  Depends on `WellFormed` (entries store the
    realisation of their own key) + injectivity (matched entry's key ≡ query). -/
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
    -- hhit : e.artifact = a
    have hmem  : e ∈ tbl := List.mem_of_find?_eq_some hfind
    have hkeq : encode e.key = encode k := by
      have hpred := List.find?_some hfind
      simpa using hpred
    have hcan  : canonKey e.key = canonKey k := encode_determines_canon _ _ hkeq
    have hart  : e.artifact = realize (canonKey e.key) := hwf e hmem
    rw [← hhit, hart, hcan]

-- ---------------------------------------------------------------------------
-- 4. C ≡ A bridge — stamp-fast SHA equals strict SHA when the stamp is valid
-- ---------------------------------------------------------------------------

/-- Option C's fast path returns the stamp's recorded SHA without re-reading;
    Option A (strict mode) recomputes `shaOf f`.  When the stamp is valid the
    two agree — so C is a sound acceleration of A, and CI's `--cache-strict`
    (mode A) can never diverge from a warm C hit on an unchanged file. -/
theorem stamp_fast_eq_strict (st : FileStamp) (f : FileState)
    (h : StampValid st f) : st.contentSha = shaOf f := h

-- ---------------------------------------------------------------------------
-- 5. Order-independence — reordered set fields still hit (concrete checks)
-- ---------------------------------------------------------------------------

private def dA : Dep := { moduleId := "a", ifaceDigest := "11" }
private def dB : Dep := { moduleId := "b", ifaceDigest := "22" }

private def kBase (ds : List Dep) (cfg : List String) : ActionKey :=
  { domain := "simple/interpreter-module/v1", compilerExe := "c", liveCompilerSrc := "s"
  , schemaVersion := 1, targetTriple := "x86_64-linux", hostArch := "x86_64"
  , cfgFeatures := cfg, stdlibVariant := "nogc_async", runtimeFamily := "nogc"
  , sourceContent := "src", resolutionWitness := "rw", deps := ds
  , macroRoot := "m", aopSelection := "aop", ctEnvInputs := [] }

/-- Swapping dependency order yields the same encoding (same set ⇒ same digest ⇒ hit). -/
theorem deps_reorder_hits : encode (kBase [dB, dA] []) = encode (kBase [dA, dB] []) := by
  decide

/-- Swapping cfg-feature order yields the same encoding. -/
theorem cfg_reorder_hits :
    encode (kBase [] ["z", "a"]) = encode (kBase [] ["a", "z"]) := by
  decide

/-- Sanity (negative): a different source content DOES change the encoding. -/
theorem source_differs_misses :
    encode { kBase [dA] [] with sourceContent := "src2" } ≠ encode (kBase [dA] []) := by
  decide

end CacheIdentity
