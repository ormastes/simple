/-
  CacheProtocol.Generated.Golden — GENERATED FILE. Do not edit.
  Cross-language golden vectors: the expected strings below were computed
  by the SIMPLE-side canonical encoder (src/app/gen_cache_model/main.spl,
  mirroring action_key.spl's canon_* framing). `lake build` re-derives
  each via the Lean encoder and proves byte equality — this file IS the
  correspondence check between the two implementations.
-/
import CacheProtocol.Generated.Model

namespace CacheProtocol

def gv1 : ActionKey :=
  { domain := "simple/interpreter-module/v2"
  , compilerExe := "ce1"
  , liveCompilerSrc := "lcs1"
  , schemaVersion := 2
  , targetTriple := "x86_64-unknown-linux-gnu"
  , hostArch := "x86_64"
  , cfgFeatures := []
  , stdlibVariant := "nogc_async"
  , runtimeFamily := "nogc"
  , sourceContent := "sc1"
  , resolutionWitness := "rw1"
  , deps := []
  , macroRoot := "mr1"
  , aopSelection := "aop1"
  , ctEnvInputs := []
  , schemaDigest := "sent"
  , aopSurfaceRoot := "sent"
  , aopCandidatePartitionRoots := []
  , aopWeaveRoot := "sent"
  , blockManifestRoots := []
  , resultKind := .interpreterModule }

-- Simple-side encoder produced this exact byte string.
set_option maxRecDepth 100000 in
theorem golden_vector_1 :
    encodeString gv1 = "F28:simple/interpreter-module/v2Q20:F11:compilerExeS3:ce1F15:liveCompilerSrcS4:lcs1F13:schemaVersionN2;F12:targetTripleS24:x86_64-unknown-linux-gnuF8:hostArchS6:x86_64F11:cfgFeaturesQ0:F13:stdlibVariantS10:nogc_asyncF13:runtimeFamilyS4:nogcF13:sourceContentS3:sc1F17:resolutionWitnessS3:rw1F4:depsQ0:F9:macroRootS3:mr1F12:aopSelectionS4:aop1F11:ctEnvInputsQ0:F12:schemaDigestS4:sentF14:aopSurfaceRootS4:sentF26:aopCandidatePartitionRootsQ0:F12:aopWeaveRootS4:sentF18:blockManifestRootsQ0:F10:resultKindS18:interpreter_module" := by
  decide

def gv2 : ActionKey :=
  { domain := "simple/interpreter-module/v2"
  , compilerExe := "ce2"
  , liveCompilerSrc := "lcs2"
  , schemaVersion := 2
  , targetTriple := "aarch64-unknown-linux-gnu"
  , hostArch := "aarch64"
  , cfgFeatures := ["zeta", "alpha"]
  , stdlibVariant := "common"
  , runtimeFamily := "gc"
  , sourceContent := "sc2"
  , resolutionWitness := "rw2"
  , deps := [Dep.mk "m2" "i2", Dep.mk "m1" "i1"]
  , macroRoot := "mr2"
  , aopSelection := "aop2"
  , ctEnvInputs := ["B=2", "A=1"]
  , schemaDigest := "sd2"
  , aopSurfaceRoot := "asr2"
  , aopCandidatePartitionRoots := ["p2", "p1"]
  , aopWeaveRoot := "awr2"
  , blockManifestRoots := ["b2", "b1"]
  , resultKind := .mirModule }

-- Simple-side encoder produced this exact byte string.
set_option maxRecDepth 100000 in
theorem golden_vector_2 :
    encodeString gv2 = "F28:simple/interpreter-module/v2Q20:F11:compilerExeS3:ce2F15:liveCompilerSrcS4:lcs2F13:schemaVersionN2;F12:targetTripleS25:aarch64-unknown-linux-gnuF8:hostArchS7:aarch64F11:cfgFeaturesQ2:S5:alphaS4:zetaF13:stdlibVariantS6:commonF13:runtimeFamilyS2:gcF13:sourceContentS3:sc2F17:resolutionWitnessS3:rw2F4:depsQ2:Q2:F8:moduleIdS2:m1F11:ifaceDigestS2:i1Q2:F8:moduleIdS2:m2F11:ifaceDigestS2:i2F9:macroRootS3:mr2F12:aopSelectionS4:aop2F11:ctEnvInputsQ2:S3:A=1S3:B=2F12:schemaDigestS3:sd2F14:aopSurfaceRootS4:asr2F26:aopCandidatePartitionRootsQ2:S2:p1S2:p2F12:aopWeaveRootS4:awr2F18:blockManifestRootsQ2:S2:b1S2:b2F10:resultKindS10:mir_module" := by
  decide

def gv3 : ActionKey :=
  { domain := "simple/interpreter-module/v2"
  , compilerExe := "F3:abc"
  , liveCompilerSrc := "Q0:"
  , schemaVersion := 0
  , targetTriple := "S1:x"
  , hostArch := "N7;"
  , cfgFeatures := ["Q1:"]
  , stdlibVariant := ""
  , runtimeFamily := ""
  , sourceContent := ""
  , resolutionWitness := ""
  , deps := [Dep.mk "" ""]
  , macroRoot := ""
  , aopSelection := ""
  , ctEnvInputs := []
  , schemaDigest := ""
  , aopSurfaceRoot := ""
  , aopCandidatePartitionRoots := []
  , aopWeaveRoot := ""
  , blockManifestRoots := []
  , resultKind := .linkProduct }

-- Simple-side encoder produced this exact byte string.
set_option maxRecDepth 100000 in
theorem golden_vector_3 :
    encodeString gv3 = "F28:simple/interpreter-module/v2Q20:F11:compilerExeS6:F3:abcF15:liveCompilerSrcS3:Q0:F13:schemaVersionN0;F12:targetTripleS4:S1:xF8:hostArchS3:N7;F11:cfgFeaturesQ1:S3:Q1:F13:stdlibVariantS0:F13:runtimeFamilyS0:F13:sourceContentS0:F17:resolutionWitnessS0:F4:depsQ1:Q2:F8:moduleIdS0:F11:ifaceDigestS0:F9:macroRootS0:F12:aopSelectionS0:F11:ctEnvInputsQ0:F12:schemaDigestS0:F14:aopSurfaceRootS0:F26:aopCandidatePartitionRootsQ0:F12:aopWeaveRootS0:F18:blockManifestRootsQ0:F10:resultKindS12:link_product" := by
  decide

end CacheProtocol
