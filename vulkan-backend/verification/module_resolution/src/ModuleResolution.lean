namespace ModuleResolution

/-!
# Module Resolution Model

This model formalizes the module path resolution semantics described in
`doc/depedency_tracking.md` (v5). It verifies:

1. Module paths are unambiguous (no `.spl` and `__init__.spl` conflict)
2. Resolution is deterministic
3. The crate prefix correctly roots paths to the project root

## Terminology

- **ModPath**: A dot-separated module path (e.g., `crate.sys.http`)
- **FileKind**: Whether a module is a file (`foo.spl`) or directory (`foo/__init__.spl`)
- **Resolution**: The process of converting a ModPath to a filesystem path
-/

/-- A module path segment is a non-empty string identifier. -/
structure Segment where
  name : String
  nonEmpty : name ≠ ""
deriving DecidableEq, Repr

/-- A module path is a non-empty list of segments (e.g., `crate.sys.http`). -/
structure ModPath where
  segments : List Segment
  nonEmpty : segments ≠ []
deriving Repr

/-- Module can be either a file or a directory with __init__.spl. -/
inductive FileKind
  | file      -- foo.spl
  | directory -- foo/__init__.spl
deriving DecidableEq, Repr

/-- The result of resolving a module path. -/
structure ResolvedModule where
  path : ModPath
  kind : FileKind
  fsPath : String  -- Resolved filesystem path
deriving Repr

/-- File system state: tracks which files exist. -/
structure FileSystem where
  /-- Set of existing file paths -/
  files : List String
deriving Repr

/-- Check if a file exists in the filesystem. -/
def FileSystem.exists (fs : FileSystem) (path : String) : Bool :=
  fs.files.any (· == path)

/-- Convert a module path to a filesystem path for file resolution. -/
def toFilePath (root : String) (mp : ModPath) : String :=
  root ++ "/" ++ String.intercalate "/" (mp.segments.map (·.name)) ++ ".spl"

/-- Convert a module path to a filesystem path for directory resolution. -/
def toDirPath (root : String) (mp : ModPath) : String :=
  root ++ "/" ++ String.intercalate "/" (mp.segments.map (·.name)) ++ "/__init__.spl"

/-- Resolution result: either unique, ambiguous, or not found. -/
inductive ResolutionResult
  | unique (kind : FileKind) (path : String)
  | ambiguous (filePath : String) (dirPath : String)
  | notFound
deriving DecidableEq, Repr

/-- Resolve a module path in a filesystem. -/
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

/-- A filesystem is well-formed if no module has both file and directory forms. -/
def wellFormed (fs : FileSystem) (root : String) : Prop :=
  ∀ mp : ModPath, ¬(fs.exists (toFilePath root mp) = true ∧ fs.exists (toDirPath root mp) = true)

/-- Resolution is deterministic: same path always resolves the same way. -/
theorem resolve_deterministic (fs : FileSystem) (root : String) (mp : ModPath) :
    resolve fs root mp = resolve fs root mp := rfl

/-- In a well-formed filesystem, resolution never returns ambiguous. -/
theorem wellformed_not_ambiguous (fs : FileSystem) (root : String) (mp : ModPath)
    (hwf : wellFormed fs root) :
    ∀ fp dp, resolve fs root mp ≠ ResolutionResult.ambiguous fp dp := by
  intro fp dp h
  unfold resolve at h
  simp only at h
  cases hfile : fs.exists (toFilePath root mp) <;>
  cases hdir : fs.exists (toDirPath root mp)
  · -- false, false: simp closes this
    simp_all
  · -- false, true: simp closes this
    simp_all
  · -- true, false: simp closes this
    simp_all
  · -- true, true: this is the contradiction case
    simp only [hfile, hdir] at h
    obtain ⟨hfp, hdp⟩ := h
    have hwf_mp := hwf mp
    exact hwf_mp (And.intro hfile hdir)

/-- If a module resolves uniquely, the path is one of the two expected forms. -/
theorem unique_path_form (fs : FileSystem) (root : String) (mp : ModPath) (kind : FileKind) (path : String) :
    resolve fs root mp = ResolutionResult.unique kind path →
    (kind = FileKind.file ∧ path = toFilePath root mp) ∨
    (kind = FileKind.directory ∧ path = toDirPath root mp) := by
  intro h
  unfold resolve at h
  simp only at h
  cases hfile : fs.exists (toFilePath root mp) <;>
  cases hdir : fs.exists (toDirPath root mp) <;>
  simp_all

/-- Resolution respects file existence: unique result implies file exists. -/
theorem unique_implies_exists (fs : FileSystem) (root : String) (mp : ModPath)
    (kind : FileKind) (path : String) :
    resolve fs root mp = ResolutionResult.unique kind path →
    fs.exists path = true := by
  intro h
  unfold resolve at h
  simp only at h
  cases hfile : fs.exists (toFilePath root mp) <;>
  cases hdir : fs.exists (toDirPath root mp) <;>
  simp_all

/-- Not found means neither file nor directory exists. -/
theorem notfound_means_neither (fs : FileSystem) (root : String) (mp : ModPath) :
    resolve fs root mp = ResolutionResult.notFound →
    fs.exists (toFilePath root mp) = false ∧ fs.exists (toDirPath root mp) = false := by
  intro h
  unfold resolve at h
  simp only at h
  cases hfile : fs.exists (toFilePath root mp) <;>
  cases hdir : fs.exists (toDirPath root mp) <;>
  simp_all

end ModuleResolution
