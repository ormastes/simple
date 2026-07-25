import ModuleResolution

/-!
# ModuleResolutionConstraints — hand-written constraints and proofs for `ModuleResolution`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `ModuleResolution` live here; the generated model lives in
`ModuleResolution.lean` and may be replaced wholesale by regeneration.
-/

namespace ModuleResolution

theorem both_paths_existing_resolves_ambiguous
    (fs : FileSystem) (root : String) (mp : ModPath)
    (hfile : fs.exists (toFilePath root mp) = true)
    (hdir : fs.exists (toDirPath root mp) = true) :
    resolve fs root mp =
      ResolutionResult.ambiguous (toFilePath root mp) (toDirPath root mp) := by
  unfold resolve
  simp [hfile, hdir]


end ModuleResolution
