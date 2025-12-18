# Formal Verification: Models 5-8

Part of [Formal Verification](formal_verification.md).

### 5. Type Inference Compile Model ✅ VERIFIED

**Lean Model** (`verification/type_inference_compile/src/TypeInferenceCompile.lean`):
```lean
inductive Ty
  | nat
  | bool
  | arrow (a b : Ty)
  deriving DecidableEq, Repr

inductive Expr
  | litNat (n : Nat)
  | litBool (b : Bool)
  | add (a b : Expr)
  | ifElse (c t e : Expr)
  | lam (body : Expr)
  | app (f x : Expr)

def infer : Expr → Option Ty
  | Expr.litNat _ => some Ty.nat
  | Expr.litBool _ => some Ty.bool
  | Expr.add a b => do
      let Ty.nat ← infer a | none
      let Ty.nat ← infer b | none
      pure Ty.nat
  ...
```

**Proven Theorem:**
- `infer_deterministic`: `infer e = some t₁ → infer e = some t₂ → t₁ = t₂`

**Rust Implementation** (`src/type/src/lib.rs`):

| Lean | Rust | Match |
|------|------|-------|
| `Ty.nat` | `LeanTy::Nat` | ✅ Exact |
| `Ty.bool` | `LeanTy::Bool` | ✅ Exact |
| `Ty.arrow a b` | `LeanTy::Arrow(Box<LeanTy>, Box<LeanTy>)` | ✅ Exact |
| `Expr.litNat n` | `LeanExpr::LitNat(u64)` | ✅ Exact |
| `Expr.litBool b` | `LeanExpr::LitBool(bool)` | ✅ Exact |
| `Expr.add a b` | `LeanExpr::Add(Box, Box)` | ✅ Exact |
| `Expr.ifElse c t e` | `LeanExpr::IfElse(Box, Box, Box)` | ✅ Exact |
| `Expr.lam body` | `LeanExpr::Lam(Box)` | ✅ Exact |
| `Expr.app f x` | `LeanExpr::App(Box, Box)` | ✅ Exact |
| `Expr.generic name args` | `LeanExpr::Generic(String, Vec<LeanExpr>)` | ✅ Exact |
| `infer` | `lean_infer()` | ✅ Exact |

The inference model now matches generic constructors, and its `tyEq`/`listTyEq` helpers come with proven `tyEq_spec`/`listTyEq_spec` so the `ifElse` and `app` branches behave exactly like structural equality.

**Code Comparison:**
```lean
| Expr.add a b => do
    let Ty.nat ← infer a | none
    let Ty.nat ← infer b | none
    pure Ty.nat
```
```rust
LeanExpr::Add(a, b) => {
    match (lean_infer(a)?, lean_infer(b)?) {
        (LeanTy::Nat, LeanTy::Nat) => Some(LeanTy::Nat),
        _ => None,
    }
}
```

---

### 6. Module Resolution Model ✅ VERIFIED

**Purpose:** Verifies that module path resolution is unambiguous and deterministic. Based on `doc/depedency_tracking.md` (v5).

**Lean Model** (`verification/module_resolution/src/ModuleResolution.lean`):
```lean
/-- Module can be either a file or a directory with __init__.spl. -/
inductive FileKind
  | file      -- foo.spl
  | directory -- foo/__init__.spl

/-- Resolution result: either unique, ambiguous, or not found. -/
inductive ResolutionResult
  | unique (kind : FileKind) (path : String)
  | ambiguous (filePath : String) (dirPath : String)
  | notFound

/-- Resolve a module path in a filesystem. -/
def resolve (fs : FileSystem) (root : String) (mp : ModPath) : ResolutionResult :=
  let filePath := toFilePath root mp
  let dirPath := toDirPath root mp
  match fs.exists filePath, fs.exists dirPath with
  | true, true => ResolutionResult.ambiguous filePath dirPath
  | true, false => ResolutionResult.unique FileKind.file filePath
  | false, true => ResolutionResult.unique FileKind.directory dirPath
  | false, false => ResolutionResult.notFound

/-- A filesystem is well-formed if no module has both file and directory forms. -/
def wellFormed (fs : FileSystem) (root : String) : Prop :=
  ∀ mp : ModPath, ¬(fs.exists (toFilePath root mp) = true ∧ fs.exists (toDirPath root mp) = true)
```

**Proven Theorems:**
- `wellformed_not_ambiguous`: In a well-formed filesystem, resolution never returns ambiguous
- `unique_path_form`: Unique resolution returns one of the two expected path forms
- `unique_implies_exists`: Unique resolution implies the file exists
- `notfound_means_neither`: Not found means neither file nor directory exists

**Key Properties:**
1. Module paths are unambiguous (no `.spl` and `__init__.spl` conflict)
2. Resolution is deterministic
3. The crate prefix correctly roots paths to the project root

---

### 7. Visibility Export Model ✅ VERIFIED

**Purpose:** Verifies visibility and export rules. A symbol's effective visibility is the intersection of its declaration visibility and all ancestor visibilities. Based on `doc/depedency_tracking.md` (v5).

**Lean Model** (`verification/visibility_export/src/VisibilityExport.lean`):
```lean
/-- Visibility of a declaration or module. -/
inductive Visibility
  | pub   -- public
  | priv  -- private

/-- Effective visibility combines declaration visibility with directory control. -/
def effectiveVisibility (manifest : DirManifest) (moduleName : String)
    (mc : ModuleContents) (sym : SymbolId) : Visibility :=
  match mc.symbolVisibility sym with
  | none => Visibility.priv
  | some Visibility.priv => Visibility.priv
  | some Visibility.pub =>
      if manifest.isChildPublic moduleName then
        if manifest.isExported sym then Visibility.pub
        else Visibility.priv
      else Visibility.priv

/-- Visibility meet operation (intersection). -/
def visibilityMeet (v1 v2 : Visibility) : Visibility :=
  match v1, v2 with
  | Visibility.pub, Visibility.pub => Visibility.pub
  | _, _ => Visibility.priv

/-- Ancestor visibility through a path. -/
def ancestorVisibility (path : List Visibility) : Visibility :=
  path.foldl visibilityMeet Visibility.pub
```

**Proven Theorems:**
- `private_stays_private`: A private symbol cannot become public regardless of directory settings
- `private_module_restricts`: A symbol in a private module cannot become public
- `must_be_exported`: A symbol must be explicitly exported to be visible externally
- `meet_comm`, `meet_assoc`: Visibility meet is commutative and associative
- `any_private_means_private`: If any ancestor is private, result is private
- `all_public_means_public`: All public ancestors means public result

**Key Properties:**
1. Visibility is the **intersection** of declaration visibility and ancestor visibility
2. A directory's public API consists only of child modules declared as `pub mod` and symbols in `export use`
3. Nothing inside a child `.spl` file can make itself "more public" than its directory allows

---

### 8. Macro Auto-Import Model ✅ VERIFIED

**Purpose:** Verifies macro import/export and `auto import` semantics. Macros are NOT included in glob imports by default; only macros listed in `auto import` participate. Based on `doc/depedency_tracking.md` (v5).

**Lean Model** (`verification/macro_auto_import/src/MacroAutoImport.lean`):
```lean
/-- Symbol kind distinguishes macros from other symbols. -/
inductive SymKind
  | valueOrType  -- Functions, types, constants
  | macro        -- Macro definitions

/-- Check if a macro is in the auto-import list. -/
def isAutoImported (m : DirManifest) (sym : Symbol) : Bool :=
  sym.kind == SymKind.macro &&
  m.autoImports.any (fun ai => ai.fromModule == sym.modulePath && ai.macroName == sym.name)

/-- Filter macros that are in auto-import list. -/
def autoImportedMacros (m : DirManifest) (exports : ModuleExports) : List Symbol :=
  exports.macros.filter (isAutoImported m)

/-- Glob import result: non-macros + auto-imported macros only. -/
def globImport (m : DirManifest) (exports : ModuleExports) : List Symbol :=
  exports.nonMacros ++ autoImportedMacros m exports

/-- Explicit import: always works for any public symbol. -/
def explicitImport (exports : ModuleExports) (name : String) : Option Symbol :=
  (exports.nonMacros ++ exports.macros).find? (·.name == name)
```

**Proven Theorems:**
- `glob_doesnt_leak_macros_wf`: Macros not in auto-import are never in glob import result (well-formed exports)
- `nonmacros_always_globbed`: All non-macros are always in glob import
- `auto_imported_in_glob`: Auto-imported macros are in glob import
- `glob_subset`: Glob import preserves well-formedness (result symbols come from exports)
- `empty_auto_import_no_macros`: Empty auto-import means no macros in glob result
- `autoImported_combine`: AutoImported macros from combined exports is the combination

**Key Properties (Invariants):**
1. **Glob doesn't leak**: If macro `m` is not in `auto import`, then `m` is never in the result of `globImport`
2. **Explicit always works**: Explicit `use module.macroName` always imports the macro if it exists and is public
3. **Two-phase visibility**: Macro export happens in Phase 1 (module exports it), glob participation happens in Phase 2 (directory's `autoImports` lists it)

---

## Verification Models

- `verification/gc_manual_borrow/`: models GC + manual borrows. Invariant `safe` states borrowed objects stay in the GC live set; lemmas show borrow/collect steps preserve it.
- `verification/manual_pointer_borrow/`: borrow-discipline model for manual pointers. Valid states forbid mixing exclusive and shared borrows; lemmas show taking/releasing borrows keeps validity.
- `verification/async_compile/`: **async-safety verification**. Verifies that `async` functions (non-blocking) contain no blocking operations (`wait`, `join`, `recv`, `sleep`). The `pipelineSafe` property ensures functions are safe to call from async code. This is preserved by function composition (concatenation).
- `verification/nogc_compile/`: no-GC compile-time check. Programs are instruction lists; property `nogc` asserts absence of `gcAlloc` and composes across concatenation.
- `verification/type_inference_compile/`: miniature type inference. A toy `infer` function on a lambda/if/add language; determinism lemma states inference returns at most one type.
- `verification/module_resolution/`: module path resolution semantics. Verifies that module paths resolve unambiguously (no conflict between `foo.spl` and `foo/__init__.spl` in well-formed filesystems).
- `verification/visibility_export/`: visibility and export rules. Proves that effective visibility is the intersection of declaration and ancestor visibilities; private symbols cannot be made public.
- `verification/macro_auto_import/`: macro auto-import semantics. Proves that glob imports only include macros explicitly listed in `auto import`; explicit imports always work for public macros.

## Rust Implementation Mappings

The Rust codebase has been refactored to provide explicit structures that map directly to the Lean models, simplifying verification:
---

Next: [Rust Implementations](formal_verification_impl.md)
