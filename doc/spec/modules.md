# Module System Specification

This document specifies the Simple language module system, including imports, exports, visibility, and the `__init__.spl` file behavior.

---

## 1. Module Structure

### 1.1 File-Based Modules

Each `.spl` file is a module. The module name is derived from the file path:

```
src/
├── main.spl              # Module: main
├── utils.spl             # Module: utils
└── models/
    ├── user.spl          # Module: models.user
    └── post.spl          # Module: models.post
```

### 1.2 Package Definition with `__init__.spl`

A directory with `__init__.spl` becomes a **package**:

```
mypackage/
├── __init__.spl          # Package definition
├── api.spl               # mypackage.api
└── internal/
    ├── __init__.spl      # Sub-package definition
    └── helpers.spl       # mypackage.internal.helpers
```

---

## 2. Module Privacy

### 2.1 Privacy Rules

| Condition | Child Visibility |
|-----------|------------------|
| `__init__.spl` present | Children are **PRIVATE** by default |
| No `__init__.spl` | Children are **PUBLIC** |
| Explicit `pub use` in `__init__.spl` | Specific items become **PUBLIC** |

### 2.2 Private-by-Default Behavior

When `__init__.spl` exists, external code **cannot** directly access child modules:

```spl
# mypackage/__init__.spl exists

# From external code:
use mypackage.api          # ERROR: api is private
use mypackage.internal     # ERROR: internal is private
```

### 2.3 Explicit Proxying

To expose child modules, use `pub use` in `__init__.spl`:

```spl
# mypackage/__init__.spl

mod mypackage

# Public exports (explicit proxy)
pub use api.*                    # Export all from api.spl
pub use internal.helpers.format  # Export only format function

# Private (no pub keyword)
use internal.private_stuff       # Internal use only
```

Now external code can access proxied items:

```spl
# From external code:
use mypackage.api.MyClass     # OK - proxied via pub use
use mypackage.format          # OK - proxied via pub use
use mypackage.private_stuff   # ERROR - not proxied
```

---

## 3. Export Syntax

### 3.1 Export Modifiers

| Modifier | Visibility | Description |
|----------|------------|-------------|
| `pub` | Public | Accessible from any module |
| `pub(crate)` | Crate | Accessible within same crate |
| `pub(super)` | Parent | Accessible from parent module |
| `pub(self)` | Self | Private to current module |
| (none) | Private | Only current module |

### 3.2 Export Statements

```spl
# Direct export
pub fn my_function(): ...

# Re-export from child
pub use child_module.SomeType

# Re-export with rename
pub use child_module.LongTypeName as Short

# Re-export all public items
pub use child_module.*

# Selective re-export
pub use child_module.{TypeA, TypeB, function_c}
```

**Note:** The following syntaxes are **semantically identical** (both create re-exports):
- `pub use module.*` - Rust/Python-style syntax
- `export use module.*` - Simple-style syntax

Both are fully supported. Use whichever style fits your team's conventions.

### 3.3 Common Export Patterns

```spl
# Export prelude pattern
export use prelude.*

# Common use pattern (available to all children)
common use core.*

# Conditional export (platform-specific)
#[cfg(target_os = "linux")]
pub use platform.linux.*
```

---

## 4. Import Syntax

### 4.1 Import Statements

```spl
# Import specific item
use mypackage.MyClass

# Import multiple items
use mypackage.{ClassA, ClassB, function_c}

# Import all public items
use mypackage.*

# Import with alias
use mypackage.VeryLongClassName as Short

# Import and re-export
pub use mypackage.MyClass
```

### 4.2 Module Path Resolution

```spl
# Absolute path (from crate root)
use crate::utils.helpers

# Relative path (from current module)
use super::sibling_module
use self::child_module

# External crate
use external_crate.some_module
```

---

## 5. `__init__.spl` Specification

### 5.1 Purpose

The `__init__.spl` file:
1. Defines a directory as a package
2. Controls visibility of child modules
3. Provides package-level initialization
4. Defines the package's public API

### 5.2 Required Content

```spl
# Minimum required content
mod package_name

# Optional: exports, initialization, etc.
```

### 5.3 Complete Example

```spl
# mylib/__init__.spl

mod mylib

# Lint configuration for package
#[deny(primitive_api)]
#[deny(bare_string)]

# Prelude - auto-imported by users of this package
export use prelude.*

# Common imports for all child modules
common use core.*
common use core.option.*

# Public API (explicit proxy)
pub use api.Client
pub use api.Config
pub use models.{User, Post, Comment}

# Internal (not exported)
use internal.*
```

### 5.4 Child Access Prevention

When `__init__.spl` is present, the compiler enforces:

```
+------------------------------------------------------------------+
| ACCESS ATTEMPT                        | RESULT                    |
+------------------------------------------------------------------+
| use mylib.api.Client                  | ERROR (unless proxied)    |
| use mylib.Client                      | OK (if pub use api.Client)|
| use mylib.internal.secret             | ERROR (always)            |
+------------------------------------------------------------------+
```

**Error Message:**
```
error[E0603]: module `api` is private
  --> src/main.spl:3:5
   |
3  | use mylib.api.Client
   |     ^^^^^^^^^^^^^^^^
   |
   = note: module `api` is private to `mylib`
   = help: use `mylib.Client` instead (re-exported at package level)
```

---

## 6. Visibility Inheritance

### 6.1 Rules

1. **Private items** are never visible outside their module
2. **Public items** inherit visibility from parent module
3. **Proxied items** get visibility from the proxy statement

### 6.2 Example

```spl
# pkg/__init__.spl
mod pkg
pub use child.PublicItem    # PublicItem is now pkg.PublicItem

# pkg/child.spl
pub struct PublicItem       # Visible as pkg.PublicItem (proxied)
pub struct OtherItem        # PRIVATE (not proxied)
struct PrivateItem          # PRIVATE (always)
```

---

## 7. Circular Import Prevention

### 7.1 Rules

1. Import cycles are detected at compile time
2. Forward declarations allowed for type references
3. Use interfaces/traits to break cycles

### 7.2 Error Example

```
error[E0391]: cycle detected when computing module graph
  --> src/a.spl:1:1
   |
1  | use b.something
   | ^^^^^^^^^^^^^^^
   |
note: ...which requires module `b`
  --> src/b.spl:1:1
   |
1  | use a.something_else
   | ^^^^^^^^^^^^^^^^^^^^
   |
   = note: cycle: a -> b -> a
```

---

## 8. Best Practices

### 8.1 Package Organization

```
mylib/
├── __init__.spl          # Public API only
├── prelude.spl           # Commonly used items
├── api/                  # Public API modules
│   ├── __init__.spl
│   ├── client.spl
│   └── config.spl
├── internal/             # Implementation details
│   ├── __init__.spl
│   ├── parser.spl
│   └── codec.spl
└── models/               # Data types
    ├── __init__.spl
    └── types.spl
```

### 8.2 `__init__.spl` Guidelines

1. **Keep it minimal** - Only export public API
2. **Use explicit exports** - Avoid `pub use *` for large modules
3. **Document exports** - Add comments explaining public items
4. **Version public API** - Be careful about breaking changes

### 8.3 Import Guidelines

1. **Prefer specific imports** over wildcards
2. **Group imports** by category (std, external, local)
3. **Use aliases** for long names
4. **Avoid deep paths** - rely on package re-exports

---

## 9. See Also

- [doc/features/feature.md](../features/feature.md) - Feature #48-49 (Module Privacy)
- [doc/spec/language.md](language.md) - Language specification
- [doc/spec/syntax.md](syntax.md) - Syntax reference
