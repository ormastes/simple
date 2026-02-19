# MDSOC User Guide - Multi-Dimensional Separation of Concerns

**For:** Simple Language Developers
**Level:** Intermediate to Advanced
**Prerequisites:** Understanding of Simple modules, imports, and basic architecture

---

## Table of Contents

1. [Quick Start](#quick-start)
2. [Capsule Configuration](#capsule-configuration)
3. [Creating Virtual Capsules](#creating-virtual-capsules)
4. [Three-Tier Visibility](#three-tier-visibility)
5. [Layer Enforcement](#layer-enforcement)
6. [Bypass Mechanism](#bypass-mechanism)
7. [Multi-Caret Composition](#multi-caret-composition)
8. [Common Patterns](#common-patterns)
9. [Troubleshooting](#troubleshooting)

---

## Quick Start

### Step 1: Create Capsule Manifest

Create `capsule.sdn` in your project root:

```sdn
capsule:
  name: my-project
  version: 0.1.0

roots:
  - name: main
    path: src/

dimension:
  name: feature
  key_template: feature/{name}
  surface: __init__.spl

  layering:
    order: [api, app, domain, infra]
    direction: upper_to_lower
    allow_same_layer: true
    allow_adjacent_only: false

rules:
  enforce_layering: true
  reject_cycles: true
  forbid_implicit_merge: true
  require_explicit_bind: true
```

### Step 2: Create a Feature Capsule

```
src/feature/auth/
├── __init__.spl        # Surface file (composition point)
├── service.spl         # Business logic (layer: app)
├── repository.spl      # Data access (layer: infra)
└── types.spl          # Domain types (layer: domain)
```

### Step 3: Define Surface Bindings

```simple
# src/feature/auth/__init__.spl

# Import from module-local files
use auth.service.{login_user, logout_user}
use auth.repository.{UserRepository}
use auth.types.{User, Credentials}

# Export with visibility
export login_user      (visibility: Public)
export logout_user     (visibility: Public)
export User            (visibility: Public)
export Credentials     (visibility: Public)
export UserRepository  (visibility: Internal)
```

### Step 4: Use the Capsule

```simple
# src/app/main.spl

use feature.auth.{login_user, User}

fn main():
    val user = login_user("alice", "secret123")
    print "Logged in: {user.name}"
```

---

## Capsule Configuration

### Capsule Metadata

```sdn
capsule:
  name: web-app           # Project name
  version: 1.0.0          # Semantic version
```

### Roots (Carets)

Carets define aspect roots with different directory layouts:

```sdn
roots:
  - name: core
    path: src/compiler_core/       # Business logic

  - name: ui
    path: src/ui/         # User interface

  - name: infra
    path: src/infra/      # Infrastructure
```

Each caret maps to a namespace prefix: `^core`, `^ui`, `^infra`.

### Dimension Configuration

Dimensions define orthogonal decomposition axes:

```sdn
dimension:
  name: feature                       # Dimension name
  key_template: feature/{name}        # Canonical key pattern

  surface: __init__.spl               # Surface file name
  participation: explicit_bind_only   # Requires explicit binding
  intra_capsule_access: via_surface_only  # Access control
  symbol_merge: forbid_implicit       # No implicit merge
  dependency_cycles: reject           # Disallow cycles
```

**Options:**
- `participation`: `explicit_bind_only` (recommended) or `auto_bind`
- `intra_capsule_access`: `via_surface_only` (strict) or `allow_direct`
- `symbol_merge`: `forbid_implicit` (safe) or `allow_override`
- `dependency_cycles`: `reject` (clean) or `allow` (pragmatic)

### Caret Mappings

Map caret-local paths to canonical capsule keys:

```sdn
dimension:
  name: feature
  key_template: feature/{name}

  map:
    - caret: core
      match: feature/**           # ^core/feature/** → feature/{name}

    - caret: ui
      match: ui_feature/**        # ^ui/ui_feature/** → feature/{name}

    - caret: infra
      match: platform/**          # ^infra/platform/** → feature/{name}
```

All three caret paths map to the same `feature/{name}` capsule.

### Layer Configuration

Define architectural layers and dependency rules:

```sdn
dimension:
  name: feature
  key_template: feature/{name}

  layering:
    order: [api, app, domain, infra]  # From high to low
    direction: upper_to_lower          # Dependencies flow down
    allow_same_layer: true             # api can call api
    allow_adjacent_only: false         # api can skip app and call domain
```

**Direction Options:**
- `upper_to_lower`: Traditional (api → app → domain → infra)
- `lower_to_upper`: Clean Architecture (infra → domain → app → api)

### Global Rules

Project-wide enforcement settings:

```sdn
rules:
  enforce_layering: true          # Enable layer checks
  reject_cycles: true             # Forbid circular dependencies
  forbid_implicit_merge: true     # Require explicit binding
  require_explicit_bind: true     # No auto-binding
```

---

## Creating Virtual Capsules

### Directory Structure

**Option 1: Single-Caret (Simple)**

```
src/feature/auth/
├── __init__.spl        # Surface
├── handler.spl         # API layer
├── service.spl         # App layer
├── user.spl            # Domain layer
└── repository.spl      # Infra layer
```

**Option 2: Multi-Caret (Advanced)**

```
src/
  core/feature/auth/
    ├── __init__.spl
    └── service.spl      # Business logic

  ui/ui_feature/auth/
    ├── __init__.spl
    └── login_form.spl   # UI components

  infra/platform/auth/
    ├── __init__.spl
    └── repository.spl   # Data access
```

All three directories compose into one `feature/auth` capsule.

### Surface File (`__init__.spl`)

The surface file defines the capsule's public API:

```simple
# src/feature/auth/__init__.spl

"""Authentication feature capsule.

Provides user login, logout, and session management.
"""

# Import from local modules
use auth.service.{authenticate, create_session}
use auth.types.{User, Session, Credentials}
use auth.repository.{UserRepository}

# Export with visibility levels
export authenticate   (visibility: Public)
export create_session (visibility: Public)
export User          (visibility: Public)
export Session       (visibility: Public)
export Credentials   (visibility: Public)

# Internal: accessible within capsule only
export UserRepository (visibility: Internal)
```

### Layer Assignment

Assign modules to layers using directory structure or metadata:

**Method 1: Directory Convention**

```
feature/auth/
  api/handler.spl          # Automatically layer: api
  app/service.spl          # Automatically layer: app
  domain/user.spl          # Automatically layer: domain
  infra/repository.spl     # Automatically layer: infra
```

**Method 2: Metadata Annotation**

```simple
# service.spl
@layer(app)

class UserService:
    ...
```

---

## Three-Tier Visibility

MDSOC extends Simple's two-tier visibility with a capsule-internal level.

### Public Visibility

Accessible from anywhere (external modules):

```simple
# feature/auth/__init__.spl
export login_user (visibility: Public)
```

```simple
# src/app/main.spl
use feature.auth.{login_user}  # ✅ OK

login_user("alice", "secret")
```

### Internal Visibility

Accessible only within the same capsule:

```simple
# feature/auth/__init__.spl
export UserRepository (visibility: Internal)
```

```simple
# feature/auth/service.spl (same capsule)
use auth.UserRepository  # ✅ OK

# feature/billing/service.spl (different capsule)
use auth.UserRepository  # ❌ ERROR: Internal visibility
```

### Private Visibility

Accessible only within the same caret and physical directory:

```simple
# feature/auth/service.spl
fn _hash_password(pwd: text) -> text:  # Private (no export)
    ...
```

Only `service.spl` can access `_hash_password`.

### Visibility Comparison

| Visibility | Same File | Same Capsule | Different Capsule |
|------------|-----------|--------------|-------------------|
| Public     | ✅         | ✅            | ✅                 |
| Internal   | ✅         | ✅            | ❌                 |
| Private    | ✅         | ❌            | ❌                 |

---

## Layer Enforcement

### Allowed Dependencies

**Configuration:**
```sdn
layering:
  order: [api, app, domain, infra]
  direction: upper_to_lower
```

**Allowed:**
```simple
# api → app
use app.service.{UserService}  # ✅ OK

# app → domain
use domain.user.{User}  # ✅ OK

# api → domain (skipping app)
use domain.user.{User}  # ✅ OK (allow_adjacent_only: false)
```

**Denied:**
```simple
# infra → domain (lower → upper)
use domain.user.{User}  # ❌ ERROR: Layer violation
```

### Compiler Error Example

```
ERROR: Layer violation
  from: src/feature/auth/repository.spl (layer: infra)
  to:   src/feature/auth/user.spl (layer: domain)
  message: layer 'infra' (level 3) cannot depend on 'domain' (level 2), direction=upper_to_lower

HINT: Either:
  1. Refactor to respect layer boundaries
  2. Use @bypass_grant + @bypass_use for exceptional cases
```

### Same-Layer Dependencies

Controlled by `allow_same_layer`:

```sdn
layering:
  order: [api, app, domain, infra]
  direction: upper_to_lower
  allow_same_layer: true  # api can call other api modules
```

```simple
# api/user_handler.spl
use api.auth_handler.{authenticate_request}  # ✅ OK
```

If `allow_same_layer: false`:
```simple
use api.auth_handler.{authenticate_request}  # ❌ ERROR
```

### Adjacent-Only Mode

Restrict dependencies to immediate neighbors:

```sdn
layering:
  order: [api, app, domain, infra]
  direction: upper_to_lower
  allow_adjacent_only: true  # api can only call app, not domain
```

```simple
# api → app
use app.service.{UserService}  # ✅ OK (adjacent)

# api → domain
use domain.user.{User}  # ❌ ERROR: Not adjacent (skips app)
```

---

## Bypass Mechanism

For exceptional cases where strict layering is impractical.

### Step 1: Export-Side Grant

```simple
# infra/database.spl (infra layer)

"""Database connection pool.

WARNING: This exposes low-level database handle for performance-critical
batch operations. Use sparingly.
"""

@bypass_grant(
    symbol: connection_pool,
    edge: "domain->infra",
    reason: "Performance optimization for batch reports"
)
export connection_pool
```

### Step 2: Import-Side Usage

```simple
# domain/reports.spl (domain layer)

"""Report generation service.

Uses direct database access for batch operations (bypasses repository pattern).
See: infra/database.spl for bypass grant.
"""

@bypass_use(
    target: connection_pool,
    edge: "domain->infra",
    reason: "Batch report generation requires connection pooling"
)
use infra.database.{connection_pool}

fn generate_monthly_report():
    val conn = connection_pool.acquire()
    # Direct SQL for performance...
```

### Both Sides Must Match

**Compiler validates:**
1. Grant exists for symbol
2. Edge matches (e.g., `"domain->infra"`)
3. Usage references valid grant

**Error if mismatch:**
```
ERROR: No bypass grant found for symbol 'connection_pool'
  at: src/domain/reports.spl:10
  hint: Add @bypass_grant in infra/database.spl
```

### Audit Report

Generate bypass audit:

```bash
bin/simple build --mdsoc-audit
```

**Output (`bypass_audit.md`):**

```markdown
# MDSOC Bypass Audit Report

## Summary
- Total grants: 1
- Total usages: 1
- Unmatched grants: 0
- Unmatched usages (ERRORS): 0

## Grants

### connection_pool
- Module: infra/database.spl
- Edge: domain->infra
- Reason: Performance optimization for batch reports
- Location: src/infra/database.spl:15

## Usages

### connection_pool
- Using module: domain/reports.spl
- Edge: domain->infra
- Reason: Batch report generation requires connection pooling
- Use site: src/domain/reports.spl:10
- Grant site: src/infra/database.spl:15
```

---

## Multi-Caret Composition

### Use Case: Platform Abstraction

Different platforms need different implementations of the same API.

### Directory Structure

```
src/
  core/platform/filesystem/
    ├── __init__.spl       # Surface (unified API)
    └── interface.spl      # API contract

  posix/platform/filesystem/
    └── posix_impl.spl     # Unix/Linux implementation

  win32/platform/filesystem/
    └── win32_impl.spl     # Windows implementation

  wasm/platform/filesystem/
    └── wasm_impl.spl      # Browser implementation
```

### Manifest Configuration

```sdn
roots:
  - name: core
    path: src/compiler_core/

  - name: posix
    path: src/posix/

  - name: win32
    path: src/win32/

  - name: wasm
    path: src/wasm/

dimension:
  name: platform
  key_template: platform/{name}

  map:
    - caret: core
      match: platform/**

    - caret: posix
      match: platform/**

    - caret: win32
      match: platform/**

    - caret: wasm
      match: platform/**
```

### Surface Composition

```simple
# src/compiler_core/platform/filesystem/__init__.spl

use filesystem.interface.{FileSystem}

# Platform-specific bindings (selected at build time)
if cfg(target_os = "linux"):
    use posix_impl.{PosixFileSystem}
    export PosixFileSystem as FileSystem
elif cfg(target_os = "windows"):
    use win32_impl.{Win32FileSystem}
    export Win32FileSystem as FileSystem
elif cfg(target_arch = "wasm32"):
    use wasm_impl.{WasmFileSystem}
    export WasmFileSystem as FileSystem
```

### Build-Time Selection

```bash
# Linux build
bin/simple build --target=x86_64-unknown-linux-gnu

# Windows build
bin/simple build --target=x86_64-pc-windows-msvc

# WASM build
bin/simple build --target=wasm32-unknown-unknown
```

Compiler selects appropriate caret based on target platform.

---

## Common Patterns

### Pattern 1: Feature Grouping

**Problem:** Feature code scattered across layers

**Solution:** Feature-as-capsule

```
feature/auth/
  ├── __init__.spl
  ├── api/handler.spl
  ├── app/service.spl
  ├── domain/user.spl
  └── infra/repository.spl
```

### Pattern 2: Platform Variants

**Problem:** `#ifdef` clutter in code

**Solution:** Multi-caret platform dimension

```
^posix/platform/network/**
^win32/platform/network/**
^wasm/platform/network/**
```

### Pattern 3: Layered Onion

**Problem:** Clean Architecture dependency inversion

**Solution:** LowerToUpper direction

```sdn
layering:
  order: [infra, domain, app, api]
  direction: lower_to_upper  # Dependencies point inward
```

### Pattern 4: Shared Utilities

**Problem:** Utilities needed across layers

**Solution:** Dedicated utility capsule (no layer enforcement)

```sdn
dimension:
  name: util
  key_template: util/{name}
  # No layering config = unrestricted
```

### Pattern 5: Internal API

**Problem:** Feature needs shared types between layers but hide from outside

**Solution:** Internal visibility

```simple
export FeatureConfig (visibility: Internal)
```

---

## Troubleshooting

### Error: "Capsule not found"

**Symptom:**
```
ERROR: Capsule 'feature/auth' not found
```

**Cause:** No matching caret mapping or surface file missing

**Fix:**
1. Check `capsule.sdn` has mapping for your path:
   ```sdn
   map:
     - caret: main
       match: feature/**
   ```

2. Ensure `__init__.spl` exists:
   ```
   src/feature/auth/__init__.spl
   ```

### Error: "Layer violation"

**Symptom:**
```
ERROR: layer 'infra' (level 3) cannot depend on 'domain' (level 2)
```

**Fix:**

**Option 1:** Refactor (recommended)
```simple
# Move logic to domain layer or use dependency injection
```

**Option 2:** Bypass (exceptional)
```simple
@bypass_grant + @bypass_use annotations
```

### Error: "Symbol conflict"

**Symptom:**
```
ERROR: Symbol 'Config' defined in multiple bindings
```

**Cause:** Multiple carets contribute same-named type without aliasing

**Fix:** Use explicit aliases in surface:
```simple
# __init__.spl
use core_config.Config as CoreConfig
use env_config.Config as EnvConfig

export CoreConfig
export EnvConfig
```

### Error: "Missing bypass grant"

**Symptom:**
```
ERROR: No bypass grant found for symbol 'internal_api'
```

**Fix:** Add @bypass_grant on export side:
```simple
# Export file
@bypass_grant(symbol: internal_api, edge: "api->infra", reason: "...")
export internal_api
```

### Warning: "Unused bypass grant"

**Symptom:**
```
WARN: Unused bypass grant for 'old_function'
```

**Cause:** Grant exists but no matching usage

**Fix:** Remove obsolete grant or add usage

### Error: "Circular dependency"

**Symptom:**
```
ERROR: Dependency cycle detected: auth -> billing -> auth
```

**Fix:**
1. Extract shared code to new capsule
2. Introduce interface/protocol boundary
3. Use dependency injection

---

## Architecture Validation (`check-arch`)

The `check-arch` command validates dependency rules declared in `__init__.spl` `arch {}` blocks.

### Declaring Dependency Rules

Add an `arch {}` block to any `__init__.spl`:

```simple
arch {
    allow = ["core", "std"]
    deny = ["compiler/**"]
}
```

### Running the Check

```bash
bin/simple check-arch              # Check from current directory
bin/simple check-arch src/         # Check src/ subtree
```

The command scans the directory tree, finds all `arch {}` blocks, then checks every `use`/`import`
statement against the nearest applicable rules. Violations are printed with the file path, the
offending import, and the rule file that was breached.

### Complementary Tools

| Tool | Purpose |
|------|---------|
| `bin/simple check-arch` | Import rule validation (allow/deny patterns) |
| `bin/simple build --mdsoc-audit` | Bypass grant/usage audit report |

---

## Port Struct Pattern

The MDSOC design encourages replacing implicit cross-stage imports with typed port structs. A port
struct is a `struct` whose fields are `fn` types -- one field per operation the consumer needs:

```simple
struct ParserPort:
    name: text
    parse_fn: fn([text], text) -> [text]
```

This pattern (implemented in `src/compiler/backend_port.spl` and
`src/compiler/compiler_services.spl`) makes all pipeline dependencies visible from one struct.

### Benefits over String-Keyed DI

| Aspect | String DI (`resolve("X")`) | Port Struct |
|--------|--------------------------|-------------|
| Discoverability | Hidden, requires docs | Visible as struct fields |
| Type safety | Returns `Any` | Typed fn-fields |
| Tooling | No autocomplete | Full IDE support |
| Refactoring | Find-all-string | Rename field |

---

## Best Practices

1. **Start Simple:** Begin with single dimension, add multi-caret later
2. **Document Bypasses:** Always explain why layer violation is necessary
3. **Regular Audits:** Run `bin/simple check-arch` and `--mdsoc-audit` in CI to track violations and bypasses
4. **Public Docs Required:** All Public exports must have docstrings
5. **Layer Assignment:** Use directory conventions over annotations
6. **Explicit Binding:** Always use `explicit_bind_only` for predictability
7. **Reject Cycles:** Enable `reject_cycles: true` to enforce DAG structure
8. **Visibility Default:** Prefer Internal over Public for feature-internal APIs

---

## Next Steps

- **Theory:** Read `doc/research/mdsoc_design.md` for design rationale
- **Examples:** Explore `test/unit/compiler/mdsoc/` for working examples
- **API Reference:** See `src/compiler/mdsoc/mod.spl` for type definitions
- **IDE Support:** Install Simple Language extension for capsule navigation

---

**Document Version:** 1.0
**Last Updated:** 2026-02-17
**Maintainers:** Simple Language Team
