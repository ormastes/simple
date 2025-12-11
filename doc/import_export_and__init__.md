---

Simple Language: Module, Import, Export, and __init__.spl Specification (v4)

Last updated: this version includes explicit macro import/export and directory-level auto import rules.


---

1. Overview

This document defines:

module path syntax (. separators),

the simple.toml project configuration,

rules for resolving modules and directories,

the structure and semantics of __init__.spl directory manifests,

use, common use, and export use,

macro import/export behavior,

directory-level auto import declarations.


The goal is:

predictable static module resolution,

explicit and safe macro importing,

directory-wide attribute and import control,

a single source of truth for each directory’s public API.



---

2. Module Path Syntax

Simple uses dot-separated paths for modules and items:

crate.sys.http
crate.core.base
sys.http.router
core.prelude.Option

Rules:

Never use /, ::, or string literals in module paths.

All paths must resolve inside the project root specified in simple.toml.



---

3. simple.toml Specification

simple.toml resides at the project root and controls:

project metadata,

source root path,

reusable profiles,

compile-time features.


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

[project]

Key	Type	Meaning

name	string	Project identifier
version	string	Semantic version
root	string	Directory containing project source files


Example:
With root = "src", module crate.sys.http resolves to:

src/sys/http.spl, or

src/sys/http/__init__.spl.


[profiles.<name>]

A profile is a reusable bundle of:

directory attributes,

directory-wide common use imports.


Example:

[profiles.server]
attributes = ["async", "strong"]
imports = [
  "crate.core.base.*",
  "crate.net.http.*",
  "crate.time.*"
]

Applied within __init__.spl via:

#[profile("server")]
mod http

[features]

Compile-time feature toggles, optionally enabled in a directory via:

#[feature("strict_null")]
mod something


---

4. Directory Manifest: __init__.spl

Any directory containing __init__.spl is a directory-scoped module.

At top level, only the following constructs are allowed:

1. Directory header


2. Child module declarations


3. Directory prelude imports (common use)


4. Public re-exports (export use)


5. Macro auto-import declarations (auto import)



No functions, types, variables, or normal code definitions belong in __init__.spl.


---

4.1 Directory Header

Example:

#[no_gc, strong]
#[profile("server")]
#[feature("strict_null")]
mod http

Rules:

The identifier after mod must match the directory name.

Attributes may include:

#[no_gc]

#[async]

#[strong]

#[profile("name")]

#[feature("name")]


Profiles inject attributes + common use lines defined in simple.toml.


Attribute inheritance:

Attributes flow into all files and subdirectories unless overridden.



---

4.2 Child Modules

Example:

pub mod router
mod internal
#[no_gc]
pub mod driver

Resolution inside directory http/:

mod router resolves to:

http/router.spl, or

http/router/__init__.spl


If both exist → compile error.


Visibility:

pub mod name = part of public API (if exported).

mod name = internal to directory.


Attributes on mod statements apply to that subtree.


---

5. Visibility Rules

Effective visibility of any module/item is the intersection of:

1. Its declaration (pub or not),


2. Directory visibility,


3. Parent/ancestor visibility.



A directory’s public API consists only of:

child modules declared as pub mod in its __init__.spl,

symbols re-exported via export use in that same manifest.


Nothing inside a child .spl file can bypass __init__.spl visibility controls.


---

6. Import System

6.1 Normal Imports (use)

Forms:

use crate.core.prelude.Option
use crate.time.Instant
use crate.net.http.{Client, Request}
use crate.net.http.*

Rules:

use module.Name imports that single public symbol.

use module.{A, B, C} imports multiple names.

use module.* imports:

all non-macro public items exported by module,

plus any macros listed in auto import in that module’s __init__.spl.



6.2 Directory Prelude (common use)

Example:

common use crate.core.base.*
common use crate.net.Url

Applies these imports to every file directly under the directory.

Inherited by child directories unless overridden.

Per-file opt-out:

#[no_common_imports]
mod somefile

6.3 Public Re-exports (export use)

Example:

export use router.Router
export use router.{Client, Request}
export use router.*         # glob, non-macro items only

Defines what this directory exports to others.

export use module.* exports only non-macros unless macros are explicitly listed via auto import.



---

7. Macro Import/Export and auto import

Macros behave like named values in use / export use, but are not included in glob imports unless explicitly listed in auto import.

7.1 Macro Definitions (normal modules)

Example (router.spl):

pub macro route(path: Str, handler):
    # ...

pub macro route_get(path: Str, handler):
    # ...

pub struct Router:
    # ...

The macro file does not decide auto-import.
Only the directory manifest does.


---

7.2 Exporting Macros (export use)

Macros must be exported by name:

export use router.route
export use router.route_get
export use router.route_debug

They are never exported by *.


---

7.3 Importing Macros

Macros are imported explicitly like any symbol:

use crate.sys.http.route
use crate.sys.http.route_get

There is no special keyword such as use macro.


---

7.4 auto import (One Macro Per Line)

Only allowed in __init__.spl.

Example:

auto import router.route
auto import router.route_get

Rules:

Each line names exactly one macro.

The path is resolved like use / export use.

Macros listed in auto import are included in glob imports:

use crate.sys.http.*


Only macros listed in auto import may appear in use module.*,
common use module.*, or export use module.*.

Macros not listed in auto import must be imported explicitly.


---

8. Complete Example

Directory structure:

src/
  sys/
    __init__.spl
    http/
      __init__.spl
      router.spl

simple.toml

[project]
name = "my_system"
version = "0.1.0"
root = "src"

[profiles.server]
attributes = ["async", "strong"]
imports = [
  "crate.core.base.*",
  "crate.net.http.*",
  "crate.time.*"
]

src/sys/__init__.spl

#[strong]
mod sys

pub mod http

src/sys/http/router.spl

pub struct Router:
    # ...

pub macro route(path: Str, handler):
    # ...

pub macro route_get(path: Str, handler):
    # ...

pub macro route_debug(path: Str, handler):
    # ...

src/sys/http/__init__.spl

#[profile("server")]
mod http

pub mod router

# public API
export use router.Router
export use router.route
export use router.route_get
export use router.route_debug

# which macros are included when glob-importing http.*
auto import router.route
auto import router.route_get
# route_debug intentionally NOT auto-imported

In user code

use crate.sys.http.*        # imports Router, route, route_get
use crate.sys.http.route_debug   # explicit import


---

9. Summary of Macro Behavior

Operation	Default Behavior	With auto import

use module.*	imports non-macros only	imports named macros too
common use module.*	non-macros only	includes listed macros
export use module.*	exports non-macros only	exports listed macros
use module.name	imports macro explicitly	always allowed
export use module.name	exports macro explicitly	always allowed
auto import location	N/A	only in __init__.spl



---

If you want this split into two Markdown files, or you want a formal EBNF grammar, tell me and I’ll generate it.
