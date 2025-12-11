Below is a complete rewritten version of doc/import_export_and__init__.md that:

Keeps your current semantics (dot paths, simple.toml, profiles, directory attributes, __init__.spl, explicit macro import/export, auto import in manifests).

Tightens wording and structure.

Adds a Lean model + example Lean code at the end, so the spec has a “formal mode” you can extend later.


You can paste this over the existing file.


---

# Simple Language: Module, Import, Export, and `__init__.spl` Specification (v5)

_Last updated: v5 – includes explicit macro import/export, directory-level `auto import` rules, and a Lean-style formal model section._

---

## 1. Scope

This document defines:

- **Module path syntax** (dot-separated paths).
- The **`simple.toml`** project configuration.
- Rules for resolving **modules and directories**.
- The structure and semantics of **`__init__.spl` directory manifests**.
- **`use`**, **`common use`**, and **`export use`**.
- **Macro import/export** and **directory-level `auto import`**.
- A **Lean model** of the module/import/macro system.

Goals:

- Predictable, static module resolution.
- Explicit and safe macro importing.
- Directory-wide attributes and imports controlled from a single manifest.
- A precise model that can be reasoned about and extended in Lean.

---

## 2. Module Paths

Simple uses **dot-separated** paths for modules and items.

Examples:

```spl
crate.sys.http
crate.core.base
sys.http.router
core.prelude.Option

Rules:

Use . as the only separator in module paths.

Do not use /, ::, or string literals in module paths.

Paths always resolve inside the project root specified in simple.toml (see below).



---

3. simple.toml Project Configuration

simple.toml lives at the project root and controls:

Project metadata.

The source root directory.

Reusable profiles (directory attributes + imports bundles).

Compile-time features.


3.1 Structure

[project]
name = "my_app"
version = "0.1.0"
root = "src"

[profiles.embedded]
attributes = ["no_gc", "strong"]
imports = [
    "crate.core.base.*",
    "crate.core.no_std.*"
]

[profiles.server]
attributes = ["async", "strong"]
imports = [
    "crate.core.base.*",
    "crate.net.http.*",
    "crate.time.*"
]

[features]
strict_null = true
new_async   = true

[project] fields

Key Type    Meaning

name    string  Project identifier
version string  Semantic version
root    string  Directory containing project source files


Example resolution:

root = "src".

crate.sys.http resolves to either:

src/sys/http.spl, or

src/sys/http/__init__.spl.



If both exist → compile-time error (ambiguous module).

[profiles.*]

Each profile is a reusable bundle of:

Directory attributes (e.g. async, no_gc, strong).

Directory-wide imports (used as common use).


Example:

[profiles.server]
attributes = ["async", "strong"]
imports = [
    "crate.core.base.*",
    "crate.net.http.*",
    "crate.time.*"
]

Inside __init__.spl, a profile is applied via:

#[profile("server")]
mod http

This injects:

The profile’s attributes (async, strong) at the directory level.

The profile’s imports as implicit common use lines.


[features]

Features are compile-time toggles.

Declared in simple.toml.

Optionally enabled on directories via:


#[feature("strict_null")]
mod something

The exact set of recognized features is up to the compiler/tooling, but they are treated as compile-time switches for analysis and code generation.


---

4. Directory Manifest: __init__.spl

Any directory containing __init__.spl is a directory-scoped module.

Inside __init__.spl, only these top-level constructs are allowed:

1. Directory header (mod dirname with attributes).


2. Child module declarations (mod / pub mod).


3. Directory prelude imports (common use).


4. Public re-exports (export use).


5. Macro auto-import declarations (auto import).



No normal code (functions, types, variables, etc.) is allowed in __init__.spl.
It is purely a manifest and API/attribute controller.


---

5. Directory Header

5.1 Example

#[no_gc, strong]
#[profile("server")]
#[feature("strict_null")]
mod http

Rules:

The identifier after mod must match the directory name (http here).

Allowed attributes include:

#[no_gc]
#[async]
#[strong]
#[profile("name")]
#[feature("name")]

#[profile("name")]:

Injects that profile’s attributes.

Injects that profile’s imports as implicit common use.


#[feature("name")]:

Marks this directory as compiled with that feature enabled.



5.2 Attribute Inheritance

Attributes on the directory header flow into:

All .spl files directly under the directory.

All subdirectories unless overridden with their own __init__.spl.


Effective attributes for a file or subdirectory are the union of:

1. Attributes on its nearest mod dir header.


2. Attributes from any applied profile on that header.


3. Attributes from ancestor directories (unless shadowed/overridden by profile logic).




---

6. Child Modules in __init__.spl

6.1 Example

pub mod router
mod internal

#[no_gc]
pub mod driver

Resolution within directory http/:

mod router → http/router.spl or http/router/__init__.spl

mod internal → http/internal.spl or http/internal/__init__.spl

mod driver → http/driver.spl or http/driver/__init__.spl


If both X.spl and X/__init__.spl exist for the same X → compile error (ambiguous).

6.2 Visibility

pub mod name
Declares a public child module. It may become part of the directory’s public API, depending on export use rules.

mod name
Declares an internal child module (not public outside the directory).


Attributes on a child mod apply to that child’s entire subtree:

#[no_gc]
pub mod driver  # driver and its submodules inherit #[no_gc]


---

7. Visibility Model

The effective visibility of any module or item is the intersection of:

1. Its own declaration (pub or not).


2. Visibility of its directory (as controlled by __init__.spl).


3. Visibility of its ancestors (up the module tree).



A directory’s public API consists only of:

Child modules declared as pub mod in its __init__.spl, and

Symbols listed in export use inside that same __init__.spl.


Nothing inside a child .spl file can make itself “more public” than its directory’s __init__.spl allows.


---

8. Import System

8.1 Normal Imports: use

Forms:

use crate.core.prelude.Option
use crate.time.Instant
use crate.net.http.{Client, Request}
use crate.net.http.*

Rules:

use module.Name
Imports that single public symbol.

use module.{A, B, C}
Imports multiple public symbols.

use module.*
Imports:

All non-macro public items exported by module, and

Any macros that are listed in auto import in module’s __init__.spl.



8.2 Directory Prelude: common use

common use applies imports to all files directly under the directory and is inherited by subdirectories unless overridden.

Example:

common use crate.core.base.*
common use crate.net.Url

This means:

Every .spl file in this directory implicitly has those use imports.

Subdirectories inherit them unless they redefine their own __init__.spl and change common use.


Per-file opt-out is possible:

#[no_common_imports]
mod somefile

A file marked with #[no_common_imports] does not receive directory-level common use imports.

8.3 Public Re-exports: export use

export use defines what the directory exports to others.

Examples:

export use router.Router
export use router.{Client, Request}
export use router.*      # glob, non-macro items only

Rules:

export use module.Name
Re-exports a single symbol from child module module.

export use module.{A, B, C}
Re-exports multiple symbols.

export use module.*

Exports all non-macro public items from the module.

Macros are not included unless specifically handled via auto import (see below).




---

9. Macro Import/Export and auto import

Macros behave like named values in use / export use, but have stricter glob rules.

9.1 Macro Definitions (normal modules)

Inside e.g. router.spl:

pub macro route(path: Str, handler):
    # ...

pub macro route_get(path: Str, handler):
    # ...

pub struct Router:
    # ...

Notes:

Macros live in normal modules (*.spl).

Macro files do not control glob or auto-import behavior.

Only the directory’s __init__.spl decides auto import.


9.2 Exporting Macros (export use)

Macros must be exported by name:

export use router.route
export use router.route_get
export use router.route_debug

They are never exported by *. That is:

export use router.*

does not export any macros.

9.3 Importing Macros (use)

Macros are imported explicitly just like other symbols:

use crate.sys.http.route
use crate.sys.http.route_get

Rules:

There is no special keyword such as use macro.

Macros are regular named symbols for the purposes of use / export use, with the additional glob restrictions detailed below.


9.4 auto import (One Macro per Line, __init__.spl only)

auto import is a directory-level manifest for macros and is only allowed in __init__.spl.

Example in src/sys/http/__init__.spl:

auto import router.route
auto import router.route_get

Rules:

Each auto import line names exactly one macro.

Paths are resolved like use / export use.

Macros listed in auto import are:

Included in glob imports: use module.*.

Included in directory common use module.*.

Included in export use module.*.



Therefore:

Only macros listed in auto import may appear implicitly in:

use module.*

common use module.*

export use module.*


Macros not listed in auto import:

Must be imported explicitly (use module.name).

Must be exported explicitly (export use module.name).



This ensures glob imports remain predictable and controlled.


---

10. Complete Example

Directory structure:

src/
  sys/
    __init__.spl
    http/
      __init__.spl
      router.spl
simple.toml

simple.toml:

[project]
name    = "my_system"
version = "0.1.0"
root    = "src"

[profiles.server]
attributes = ["async", "strong"]
imports = [
    "crate.core.base.*",
    "crate.net.http.*",
    "crate.time.*"
]

src/sys/__init__.spl:

#[strong]
mod sys

pub mod http

src/sys/http/router.spl:

pub struct Router:
    # ...

pub macro route(path: Str, handler):
    # ...

pub macro route_get(path: Str, handler):
    # ...

pub macro route_debug(path: Str, handler):
    # ...

src/sys/http/__init__.spl:

#[profile("server")]
mod http

pub mod router   # public API surface

# Public re-exports
export use router.Router
export use router.route
export use router.route_get
export use router.route_debug

# Macros that participate in glob imports
auto import router.route
auto import router.route_get
# router.route_debug intentionally NOT auto-imported

In user code:

use crate.sys.http.*          # imports Router, route, route_get
use crate.sys.http.route_debug  # explicit import of route_debug

Behavior summary:

use crate.sys.http.*:

Gains Router (non-macro).

Gains route and route_get (macros in auto import).

Does not gain route_debug (not in auto import).


use crate.sys.http.route_debug:

Explicitly imports the route_debug macro.




---

11. Summary of Macro Behavior

Operation   Default (no auto import)    With auto import

use module.*    Imports non-macro items only    Imports non-macros + listed macros
common use module.* Non-macros only Includes listed macros
export use module.* Exports non-macros only Exports listed macros
use module.name Explicit macro import ok    Always allowed
export use module.name  Explicit macro export ok    Always allowed
auto import location    N/A Only in __init__.spl, one macro per line



---

12. Lean Model (Informal Formalization)

This section provides a Lean-style model of the module/import system.
The goal is to be close enough to real Lean code that you can paste it into lean.md and iterate.

> Note: This models module/import/macro behavior only (not the whole language).



12.1 Core Data Structures

namespace Simple

/-- Module paths are dot-separated identifiers. -/
structure ModPath :=
  (segments : List String)

/-- Directory-level attributes. Extend as needed. -/
inductive Attr
| async
| no_gc
| strong
| profile  (name : String)
| feature  (name : String)

/-- A symbol kind: value/type vs macro. -/
inductive SymKind
| value_or_type
| macro

/-- Fully-qualified symbol in a module. -/
structure Symbol :=
  (module : ModPath)
  (name   : String)
  (kind   : SymKind)

/-- `auto import` declaration: one macro per line in `__init__.spl`. -/
structure AutoImport :=
  (from   : ModPath)  -- module providing the macro
  (macro  : String)   -- macro name

/-- A directory's `__init__.spl` manifest. -/
structure DirManifest :=
  (name        : String)        -- directory name
  (attrs       : List Attr)     -- header attributes
  (children    : List String)   -- child module names (mod / pub mod)
  (publicMods  : List String)   -- subset of children that are `pub`
  (commonUses  : List ModPath)  -- `common use` module paths
  (exports     : List Symbol)   -- explicit `export use` entries
  (autoImports : List AutoImport) -- macros to be auto-imported on glob

end Simple

This captures:

Directory headers and attributes.

Public vs internal child modules.

Directory-level common use.

Public re-exports.

Macro auto import declarations.


12.2 Visibility and Glob Semantics

We can describe the semantics of use module.* in terms of a function that computes the imported symbols.

namespace Simple

/-- Information about what a module publicly exports. -/
structure ModuleExports :=
  (nonMacros : List Symbol)  -- all public non-macro symbols
  (macros    : List Symbol)  -- all public macros, independent of auto-import

/-- Returns the macros that are listed in `auto import` for a given directory. -/
def autoImportedMacros
  (m : DirManifest)
  (exports : ModuleExports) : List Symbol :=
  exports.macros.filter (fun s =>
    m.autoImports.any (fun ai =>
      ai.from = s.module ∧ ai.macro = s.name))

/-- What is brought into scope by `use module.*` given a manifest + exports. -/
def globImport
  (m       : DirManifest)
  (exports : ModuleExports) : List Symbol :=
  exports.nonMacros ++ autoImportedMacros m exports

end Simple

Intuition:

ModuleExports is a snapshot of all public symbols of a module, split into non-macros and macros.

autoImportedMacros picks out the macros listed in autoImports.

globImport implements exactly the spec:

All public non-macros.

Only macros listed in auto import.



12.3 Key Invariants (Stated Informally)

You can encode these as lemmas or theorems:

1. Glob doesn’t leak non-listed macros

If s is a macro not listed in auto import, then s is never in globImport m exports.


2. Explicit import/export always works

For any macro symbol s, use module.s.name and export use module.s.name are valid if its module exports it; these do not rely on auto import.


3. Visibility is directory-controlled

A symbol is visible outside a directory only if:

Its defining module is marked public in the directory’s publicMods, and

It is listed either explicitly in exports or comes from a export use module.* that is allowed to include it.



4. Two-phase macro visibility

Phase 1: A macro is exported by a module as part of ModuleExports.

Phase 2: It participates in glob imports only if the directory’s autoImports lists it.




These invariants align the Lean model with the prose spec.


---

13. Implementation Notes

The compiler’s name resolver should:

Use simple.toml for root/profile/feature resolution.

Parse each __init__.spl into a DirManifest (or a similar internal structure).

Build ModuleExports per module, including _all_ public macros (independent of auto import).

Use globImport logic (or equivalent) for use module.*, common use module.*, and export use module.*.


The Lean model above can be extended to:

Track a dependency graph between modules.

Reason about incremental compilation and dynamic module loading.

Prove properties such as “glob imports only bring in macros explicitly declared in auto import.”



If you want a separate lean.md with a more complete formalization (including dependency tracking and loader behavior), this spec can be used as the module/import layer for that model.

---

If you want, I can now:

- Split this into `import_export_and__init__.md` + `import_export_lean_model.md`, or  
- Expand the Lean section into a full, compilable Lean 4 file that you can drop into `doc/lean/`
