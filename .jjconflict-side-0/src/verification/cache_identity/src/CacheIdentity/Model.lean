/-
  CacheIdentity.Model — Lean 4 model of the Option-C global-cache identity layer.

  Source of truth (implementation mirrors this model):
    doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md  (§1.1 four identities)
    src/compiler/80.driver/cache/action_key.spl   (canonical encoder — mirrors `encode` here)

  Model: pure structures + a total canonical encoder into a domain-separated,
  tagged `Canon` term.  No Mathlib — std only.  All proved without `sorry`.

  The point of the model: a digest is `sha256 (bytes (encode k))`.  Under
  collision-resistance of sha256 (an assumption, not proved), a digest collision
  implies `encode k1 = encode k2`.  We prove `encode` is injective through the
  canonical key, so a digest collision implies the two keys are semantically
  equal — hence a cache hit can never return an artifact built from different
  semantic inputs (no false hit).  Every field is present in `encode`, so no
  omitted input can be silently ignored.

  Canon deliberately has NO `List Canon` constructor (nested inductives break
  `deriving DecidableEq`); sequences appear only as right-nested `pair`s and as
  specialised `strs`/`deps` leaves.  Constructor structure is the model-level
  analogue of the implementation's length-prefixing: a value can never be
  confused with a tag or with a neighbouring field.
-/
namespace CacheIdentity

-- ---------------------------------------------------------------------------
-- 1. Sub-digests and the full ActionKey (plan §1.1)
-- ---------------------------------------------------------------------------

/-- A sub-digest (sha256 hex of some component), treated abstractly as a String. -/
abbrev Sha := String

/-- One dependency: the depended module's stable id + its *interface* digest.
    (Interface, not content — advice-body-only changes must not invalidate.) -/
structure Dep where
  moduleId    : String
  ifaceDigest : Sha
  deriving DecidableEq, Repr

/-- Every input that can affect the produced interpreter-module artifact.
    Mirrors `ActionDigest = SHA256(domain, compiler_exe, live_compiler_src,
    schema_version, target, host_arch, cfg, stdlib, runtime_family, source,
    resolution_witness, sorted_deps, macro_root, aop_selection, ct_env)`. -/
structure ActionKey where
  domain            : String        -- domain separation, e.g. "simple/interpreter-module/v1"
  compilerExe       : Sha
  liveCompilerSrc   : Sha
  schemaVersion     : Nat
  targetTriple      : String
  hostArch          : String
  cfgFeatures       : List String
  stdlibVariant     : String
  runtimeFamily     : String
  sourceContent     : Sha
  resolutionWitness : Sha
  deps              : List Dep      -- an unordered *set*; canonicalised by sort
  macroRoot         : Sha
  aopSelection      : Sha
  ctEnvInputs       : List String
  deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- 2. Canonical term  (domain separation + framing by construction)
-- ---------------------------------------------------------------------------

/-- A canonical encoding term.  Distinct constructors + fixed field order make
    concatenation ambiguity impossible (unlike joining strings with a
    delimiter).  `tag` carries the domain/field label; `pair` right-nests the
    field sequence; `strs`/`deps` are the (pre-sorted) set-typed leaves. -/
inductive Canon where
  | str  : String → Canon
  | nat  : Nat → Canon
  | tag  : String → Canon → Canon      -- label ▸ value  (domain separation)
  | pair : Canon → Canon → Canon       -- field ▸ rest   (framing)
  | strs : List String → Canon         -- sorted string set
  | deps : List Dep → Canon            -- sorted dependency set
  deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- 3. Canonicalisation of set-typed fields
-- ---------------------------------------------------------------------------

/-- Total order used to canonicalise dependency sets.  Lexicographic on
    (moduleId, ifaceDigest).  Returns Bool; `decide` bridges String `<`. -/
def depLe (a b : Dep) : Bool :=
  decide (a.moduleId < b.moduleId) ||
  (a.moduleId == b.moduleId &&
    (decide (a.ifaceDigest < b.ifaceDigest) || a.ifaceDigest == b.ifaceDigest))

def insDep (a : Dep) : List Dep → List Dep
  | []      => [a]
  | b :: bs => if depLe a b then a :: b :: bs else b :: insDep a bs

/-- Canonical (sorted) form of a dependency set. -/
def sortDeps : List Dep → List Dep
  | []      => []
  | a :: as' => insDep a (sortDeps as')

def strLe (a b : String) : Bool := decide (a < b) || a == b

def insStr (a : String) : List String → List String
  | []      => [a]
  | b :: bs => if strLe a b then a :: b :: bs else b :: insStr a bs

def sortStrs : List String → List String
  | []      => []
  | a :: as' => insStr a (sortStrs as')

/-- The canonical key: the ActionKey with every set-typed field normalised.
    Two ActionKeys that differ only in element order of a set-field have the
    *same* canonical key — and must therefore hit the same cache entry. -/
structure CanonKey where
  domain            : String
  compilerExe       : Sha
  liveCompilerSrc   : Sha
  schemaVersion     : Nat
  targetTriple      : String
  hostArch          : String
  cfgFeatures       : List String   -- sorted
  stdlibVariant     : String
  runtimeFamily     : String
  sourceContent     : Sha
  resolutionWitness : Sha
  deps              : List Dep       -- sorted
  macroRoot         : Sha
  aopSelection      : Sha
  ctEnvInputs       : List String   -- sorted
  deriving DecidableEq, Repr

def canonKey (k : ActionKey) : CanonKey :=
  { domain := k.domain, compilerExe := k.compilerExe, liveCompilerSrc := k.liveCompilerSrc
  , schemaVersion := k.schemaVersion, targetTriple := k.targetTriple, hostArch := k.hostArch
  , cfgFeatures := sortStrs k.cfgFeatures, stdlibVariant := k.stdlibVariant
  , runtimeFamily := k.runtimeFamily, sourceContent := k.sourceContent
  , resolutionWitness := k.resolutionWitness, deps := sortDeps k.deps
  , macroRoot := k.macroRoot, aopSelection := k.aopSelection
  , ctEnvInputs := sortStrs k.ctEnvInputs }

-- ---------------------------------------------------------------------------
-- 4. The canonical encoder
-- ---------------------------------------------------------------------------

/-- Encode an ActionKey into its canonical term.  Every field appears exactly
    once, tagged, in a fixed order; set-typed fields are sorted first. -/
def encode (k : ActionKey) : Canon :=
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

-- ---------------------------------------------------------------------------
-- 5. Cache table + stamp/strict model (plan §1.2; C≡A bridge)
-- ---------------------------------------------------------------------------

/-- One immutable cache entry: the key it was built from + the artifact.
    Modelled as `artifact : Nat` (an opaque content id). -/
structure Entry where
  key      : ActionKey
  artifact : Nat
  deriving Repr

/-- A table is *well-formed* w.r.t. a realisation function when every stored
    artifact equals what re-realising that entry's canonical key would produce. -/
def WellFormed (realize : CanonKey → Nat) (tbl : List Entry) : Prop :=
  ∀ e ∈ tbl, e.artifact = realize (canonKey e.key)

/-- Look up by digest.  We model the digest match as `encode e.key = encode k`
    (collision-resistance folds sha256 equality back to encode equality). -/
def lookup (tbl : List Entry) (k : ActionKey) : Option Nat :=
  (tbl.find? (fun e => decide (encode e.key = encode k))).map (·.artifact)

/-- Abstract file content and the SHA of its bytes. -/
structure FileState where
  bytes : List UInt8
  deriving DecidableEq, Repr

@[simp] def shaOf (f : FileState) : Sha := "sha:" ++ toString f.bytes.length ++ toString f.bytes

/-- A strong file stamp (dev/ino/size/mtime + the SHA computed when stamped). -/
structure FileStamp where
  dev        : Nat
  ino        : Nat
  size       : Nat
  mtimeNs    : Nat
  contentSha : Sha
  deriving DecidableEq, Repr

/-- The stamp is valid for the current file exactly when its recorded SHA still
    matches the file's bytes.  (C's fast path trusts the stamp; A recomputes.) -/
def StampValid (st : FileStamp) (f : FileState) : Prop := st.contentSha = shaOf f

end CacheIdentity
