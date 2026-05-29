# Simple Language Module System

This guide covers imports, exports, module paths, and the `__init__.spl` directory manifest.

---

## Module Path Syntax

Simple uses dot-separated paths for modules and items:

```
crate.sys.http
std.spec.describe
app.io.file_read
```

Rules:
- Never use `/`, `::`, or string literals in module paths
- All paths resolve inside the project root specified in `simple.sdn`
- `use std.X` and `use lib.X` both resolve from `src/lib/`; prefer `use std.X` in new code

---

## Imports (use)

### Importing Specific Names (Recommended)

```simple
use std.spec.{describe, it, expect}
use app.io.{file_read, file_write, shell}
use std.math.{sin, cos, sqrt}
```

### Parentheses Syntax (Alternative)

```simple
use app.io.mod (env_get, env_set)     # Explicit import from mod.spl
```

Both curly braces and parentheses work identically. Curly braces are preferred for consistency.

### Glob Imports

```simple
use crate.net.http.*                  # Imports all non-macro public items
```

Glob imports include macros only if they are listed in `auto import` in the module's `__init__.spl`.

### Rules

- **Imports must be at module level** (top of file). Imports inside functions or blocks will not work.
- **Use specific names** rather than glob imports for better dependency tracking.
- **Bare imports don't expose functions**: `use app.io` loads the module but does not make its functions callable.

```simple
# Correct
use app.io.{shell}
shell("echo hi")

# Wrong -- shell is not accessible
use app.io
shell("echo hi")                      # function not found
```

---

## Directory Manifests: __init__.spl

Any directory containing `__init__.spl` becomes a directory-scoped module. The manifest controls what the directory exports and what child modules share.

### Allowed Constructs

Only these constructs belong in `__init__.spl`:
1. Directory header (attributes, profile, features)
2. Child module declarations (`mod`)
3. Directory-wide imports (`common use`)
4. Public re-exports (`export use`)
5. Macro auto-import declarations (`auto import`)

No functions, types, variables, or other code belongs here.

### Directory Header

```simple
#[no_gc, strong]
#[profile("server")]
#[deny(primitive_api)]
mod http
```

The identifier after `mod` must match the directory name. Attributes flow into all files and subdirectories unless overridden.

### Child Module Declarations

```simple
pub mod router                        # Public: part of directory's API
mod internal                          # Private: internal only
#[no_gc]
pub mod driver                        # Public with attributes
```

Resolution: `mod router` resolves to either `router.spl` or `router/__init__.spl`. If both exist, the compiler reports an error.

### Directory Prelude (common use)

Imports applied to every file in the directory:

```simple
common use crate.core.base.*
common use crate.net.Url
```

These are inherited by child directories unless overridden. A specific file can opt out:

```simple
#[no_common_imports]
mod somefile
```

### Public Re-exports (export use)

Defines the directory's public API:

```simple
export use router.Router
export use router.{Client, Request}
export use router.*                   # Glob: non-macro items only
```

### Macro Exports (auto import)

Macros are never included in glob imports unless explicitly listed:

```simple
auto import router.route
auto import router.route_get
```

With these declarations, `use crate.sys.http.*` will include `route` and `route_get`. Macros not listed in `auto import` must be imported explicitly.

---

## Visibility Rules

The effective visibility of any item is the intersection of:
1. Its own declaration (`pub` or not)
2. Directory visibility
3. Parent/ancestor visibility

A directory's public API consists only of:
- Child modules declared as `pub mod`
- Symbols re-exported via `export use`

Nothing inside a child `.spl` file can bypass `__init__.spl` visibility controls.

---

## Access Control Policies

Each directory has one of three access policies:

| Policy | Condition | Behavior |
|--------|-----------|----------|
| **Open** | No `__init__.spl` | All public files freely accessible |
| **Boundary** | `__init__.spl` present | Only exported symbols accessible from outside |
| **Bypass** | `__init__.spl` with `#[bypass]` | Directory is transparent (pass-through, no code files allowed) |

---

## Complete Example

```
src/
  sys/
    __init__.spl
    http/
      __init__.spl
      router.spl
```

**src/sys/__init__.spl**
```simple
#[strong]
mod sys

pub mod http
```

**src/sys/http/__init__.spl**
```simple
#[profile("server")]
mod http

pub mod router

export use router.Router
export use router.route
export use router.route_get

auto import router.route
auto import router.route_get
```

**src/sys/http/router.spl**
```simple
pub struct Router:
    # ...

pub macro route(path: Str, handler):
    # ...

pub macro route_get(path: Str, handler):
    # ...
```

**User code**
```simple
use crate.sys.http.*                  # Imports Router, route, route_get
use crate.sys.http.route_debug        # Must be explicit (not in auto import)
```

---

## Project Configuration

The `simple.sdn` (or `simple.toml`) file at the project root controls source resolution and profiles:

```sdn
project:
  name: "my_app"
  version: "0.1.0"
  root: "src"

profiles:
  server:
    attributes: ["async", "strong"]
    imports:
      - "crate.core.base.*"
      - "crate.net.http.*"
```

With `root: "src"`, module `crate.sys.http` resolves to `src/sys/http.spl` or `src/sys/http/__init__.spl`.

Profiles are applied within `__init__.spl` via `#[profile("server")]`.

---

## Macro Behavior Summary

| Operation | Without auto import | With auto import |
|-----------|-------------------|------------------|
| `use module.*` | Non-macros only | Includes listed macros |
| `common use module.*` | Non-macros only | Includes listed macros |
| `export use module.*` | Non-macros only | Includes listed macros |
| `use module.name` | Always allowed | Always allowed |
| `export use module.name` | Always allowed | Always allowed |

---

## Troubleshooting

### "function not found"

Import is likely inside a function block or is a bare module import:

```simple
# Wrong: import inside block
it "test":
    use app.io.{shell}                # Will not work
    shell("echo hi")

# Fix: move to module level
use app.io.{shell}
it "test":
    shell("echo hi")
```

### "module imports as dict type"

You used a bare import without listing specific names:

```simple
# Wrong
use app.io

# Fix
use app.io.{shell, file_read}
```
