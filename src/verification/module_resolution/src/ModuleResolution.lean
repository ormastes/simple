namespace ModuleResolution
/-
  # Module Resolution Model
  
  This model formalizes the module path resolution semantics.
-/
inductive FileKind
  | file
  | directory
deriving DecidableEq, Repr, BEq

inductive ResolutionResult
  | unique : FileKind → String → ResolutionResult
  | ambiguous : String → String → ResolutionResult
  | notFound

structure Segment where
  name : String
deriving DecidableEq, Repr

structure ModPath where
  segments : List Segment
deriving DecidableEq, Repr

structure FileSystem where
  files : List String
deriving Repr

def FileSystem.exists (fs : FileSystem) (path : String) : Bool :=
  fs.files.any (fun p => p == path)

def toFilePath (root : String) (mp : ModPath) : String :=
  root ++ "/" ++ String.intercalate "/" (mp.segments.map (fun (s : Segment) => s.name)) ++ ".spl"

def toDirPath (root : String) (mp : ModPath) : String :=
  root ++ "/" ++ String.intercalate "/" (mp.segments.map (fun (s : Segment) => s.name)) ++ "/__init__.spl"

def resolve (fs : FileSystem) (root : String) (mp : ModPath) : ResolutionResult :=
  let filePath := toFilePath root mp
  let dirPath := toDirPath root mp
  let fileExists := fs.exists filePath
  let dirExists := fs.exists dirPath
  match fileExists, dirExists with
  | true, true => ResolutionResult.ambiguous filePath dirPath
  | true, false => ResolutionResult.unique FileKind.file filePath
  | false, true => ResolutionResult.unique FileKind.directory dirPath
  | false, false => ResolutionResult.notFound

def wellFormed (fs : FileSystem) (root : String) : Prop :=
  ∀ mp : ModPath, ¬(fs.exists (toFilePath root mp) = true ∧ fs.exists (toDirPath root mp) = true)

theorem resolve_deterministic (fs : FileSystem) (root : String) (mp : ModPath) :
  resolve fs root mp = resolve fs root mp := by
  rfl

theorem wellformed_not_ambiguous (fs : FileSystem) (root : String) (mp : ModPath) (hwf : wellFormed fs root) :
  ∀ fp dp, resolve fs root mp ≠ ResolutionResult.ambiguous fp dp := by
  intro fp dp h
  unfold resolve at h
  simp only at h
  cases hfile : fs.exists (toFilePath root mp) <;>
  cases hdir : fs.exists (toDirPath root mp)
  · simp_all
  · simp_all
  · simp_all
  · simp only [hfile, hdir] at h
    obtain ⟨hfp, hdp⟩ := h
    have hwf_mp := hwf mp
    exact hwf_mp (And.intro hfile hdir)

theorem unique_implies_exists (fs : FileSystem) (root : String) (mp : ModPath) (kind : FileKind) (path : String) :
  resolve fs root mp = ResolutionResult.unique kind path → fs.exists path = true := by
  intro h
  unfold resolve at h
  simp only at h
  cases hfile : fs.exists (toFilePath root mp) <;>
  cases hdir : fs.exists (toDirPath root mp) <;>
  simp_all

theorem notfound_means_neither (fs : FileSystem) (root : String) (mp : ModPath) :
  resolve fs root mp = ResolutionResult.notFound → fs.exists (toFilePath root mp) = false ∧ fs.exists (toDirPath root mp) = false := by
  intro h
  unfold resolve at h
  simp only at h
  cases hfile : fs.exists (toFilePath root mp) <;>
  cases hdir : fs.exists (toDirPath root mp) <;>
  simp_all

end ModuleResolution
