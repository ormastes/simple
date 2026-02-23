# MDSoC Design for Simple (Feature/Entity Dimensions + Transform)

> MDSoC = Multi-Dimensional Separation of Concerns.
>
> This document proposes a **directory- and module-level** MDSoC mechanism for Simple:
> - Allow multiple, overlapping decompositions (feature vs entity vs others)
> - Keep strict compilation-time dependency rules
> - Provide an explicit, auditable bridging mechanism (Transform) for mismatches
>
> For the compiler-level MDSOC implementation (virtual capsules, carets, layer enforcement),
> see `src/compiler/mdsoc/` and `doc/feature/mdsoc_complete.md`.

**Status:** Design complete, application-level patterns documented
**Last Updated:** 2026-02-17

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [Background: Hyper/J and MDSoC](#2-background-hyperj-and-mdsoc)
3. [The Core Requirement: 3-Layer Architecture with 2+ Dimensions](#3-the-core-requirement)
4. [Directory Layout](#4-directory-layout)
5. [Dependency Rules](#5-dependency-rules)
6. [`__init__.spl` as Directory-Local Architecture Config](#6-__initspl-as-directory-local-architecture-config)
7. [Transform Dimension: Explicit from→to Mapping](#7-transform-dimension)
8. [Mirrored Transform Tree](#8-mirrored-transform-tree)
9. [Example: Using Entities in Feature Without Direct Imports](#9-example)
10. [Why Not Allow Direct feature→entity?](#10-why-not-allow-direct-imports)
11. [Hyper/J Comparison Table](#11-hyperj-comparison-table)
12. [Pitfalls and Mitigations](#12-pitfalls-and-mitigations)
13. [Tooling: Required Outputs for Maintainability](#13-tooling)
14. [Principles Summary](#14-principles-summary)
15. [References](#15-references)

---

## 1. Motivation

Most real systems have two "outside worlds":
- **UI/front-end**: user input, rendering, device APIs
- **Back-end/infrastructure**: DB, network, storage, external services

Each side introduces volatility, and both tend to leak complexity inward. A *single* decomposition axis (only "by package", only "by feature", only "by entity") usually creates:
- **scattering** (a concern spread across many files)
- **tangling** (multiple concerns in the same file/module)

MDSoC aims to support **multiple decompositions simultaneously**, so developers can work in the decomposition that matches the change they need.

This proposal adapts MDSoC to Simple at the **module boundary**, not at statement weaving granularity.

### The "Both Ends Touch the Outside World" Problem

The simplest widely-used fix is to treat UI + DB + external services as replaceable edge mechanisms and keep application/core policy isolated behind interfaces (ports).

That family of architectures is usually called Clean Architecture / Hexagonal (Ports & Adapters) / Onion. They differ in presentation, but the core rule is the same: **source-code dependencies must point inward** (toward policy/business logic), never outward (toward frameworks/IO).

---

## 2. Background: Hyper/J and MDSoC

### What Simple Borrows
- **Multiple decompositions are first-class** (feature vs entity, etc.)
- **Symmetry**: the system must not force a single "base" decomposition
- **Explicit mismatch handling**: differences between decompositions are reconciled *declaratively*

### What Simple Intentionally Does NOT Copy
- **Bytecode weaving / method-body slicing**
- **Automatic on-demand remodularization** of arbitrary existing code
- **General-purpose composition operators** at fine granularity (too hard to reason about, too hard to debug)

Instead, Simple does:
- **Coarse-grained MDSoC** at the *module/package boundary*
- With an explicit **Transform** bridge that is easy to audit and enforce

---

## 3. The Core Requirement

We want a simple architecture that supports both:
- **Clean layering** (UI / Business / Entity)
- And **multi-dimensional grouping** (Feature vs Entity)

### 3.1 Layers (policy → mechanism direction)

| Layer | Contents | Dependency Rule |
|-------|----------|-----------------|
| **L1: UI** | Presentation, input, view-models, CLI handlers | Depends on L2 |
| **L2: Business** | Use-cases, application services, orchestration | Depends on L3 |
| **L3: Entity** | Domain entities, value objects, invariants, domain services | Depends on nothing above |

L3 must be **stable and framework-free**.

### 3.2 Dimensions (different ways of grouping the same system)

**Dimension D_feature** — "vertical slice" by feature
- Contains UI + Business (L1 + L2), grouped by feature folders
- Example: `feature/Auth/`, `feature/Checkout/`, `feature/Billing/`

**Dimension D_entity** — "horizontal slice" by domain/entity taxonomy
- Contains Entity layer (L3), grouped by domain model
- Example: `entity/Identity/`, `entity/Order/`, `entity/Money/`

These two decompositions are *inherently mismatched*:
- A feature needs only some parts of the entity model
- But the entity model is not arranged per-feature

So we introduce an explicit bridge:

**Dimension D_transform** — deterministic, auditable mapping from one dimension to another
- Allowed to re-export across dimensions only if configured
- Mirrors the destination dimension's structure

### 3.3 The two arrows (critical distinction)

```
Arrow 1: Runtime control flow (who calls whom)
  User/UI → Controller → Use case → Domain → Port call → Adapter → DB/External

Arrow 2: Source-code dependency (what imports what, compile-time)
  Adapters depend on core-defined ports, NOT the other way around
```

**Clean Architecture's key statement:** Inner circles must not know about outer circles; dependencies point inward.

A "bottom layer" (DB/infrastructure) "depending on upper" (application/core) is actually correct when:
- Core defines `RepositoryPort` interface
- Infrastructure implements `SqlRepository : RepositoryPort`
- Wiring connects them

The bad case is when core imports ORM/HTTP/framework types directly.

---

## 4. Directory Layout

Recommended repository structure:

```
src/
  feature/
    Auth/
      ui/
        __init__.spl
        LoginView.spl
      app/
        __init__.spl
        LoginUseCase.spl
      __init__.spl
    Billing/
      ui/...
      app/...
      __init__.spl

  entity/
    Identity/
      __init__.spl
      User.spl
      Credential.spl
    Money/
      __init__.spl
      Currency.spl
      Amount.spl
    __init__.spl

  transform/
    feature/
      Auth/
        __init__.spl
        entity_view/
          __init__.spl
          AuthModel.spl
      Billing/
        __init__.spl
        entity_view/...
      __init__.spl
    __init__.spl

  shared/
    __init__.spl
    Result.spl
    Errors.spl
```

**Key idea:**
- Feature stays clean and feature-centric
- Entity stays domain-centric
- Transform provides "feature-friendly views" over entities

---

## 5. Dependency Rules

### 5.1 Within layers (UI / Business / Entity)

| Source | May depend on |
|--------|---------------|
| `feature/*/ui/**` | Same feature `app/**`, `shared/**` |
| `feature/*/app/**` | `transform/**`, `shared/**` |
| `entity/**` | Other `entity/**`, `shared/**` — **nothing else** |

### 5.2 Across dimensions (Feature vs Entity)

**Default rule:** `feature/**` **cannot** import `entity/**` directly.

| Allowed edge | Direction |
|-------------|-----------|
| `feature/*/app/**` → `transform/**` | ✅ Feature uses transform |
| `transform/**` → `entity/**` | ✅ Transform reads entity |
| `feature/**` → `entity/**` | ❌ Forbidden (compile error) |
| `transform/**` → `feature/**` | ❌ Forbidden (creates cycle) |

### 5.3 Composition Root (the wiring layer)

The composition root is the **only place allowed to "know everything"**:
- Builds objects
- Binds ports → adapters (DI container or manual wiring)
- Imports both core and adapters

---

## 6. `__init__.spl` as Directory-Local Architecture Config

Every directory carries its own local architecture contract in `__init__.spl`.

The `arch {}` config block is parsed and enforced by the compiler/build tool.

### 6.1 Minimal schema

```simple
arch {
  dimension = "feature" | "entity" | "transform" | "shared"
  layer     = "ui" | "app" | "entity" | "none"

  imports {
    allow = [
      "shared/**",
      "feature/Auth/app/**",
      "transform/**"
    ]
    deny = [
      "entity/**"     # typical for feature
    ]
  }

  exports {
    expose = [
      "./LoginUseCase",
      "./ports/**"
    ]
  }
}
```

### 6.2 Feature dimension mismatch declaration

In `src/feature/Auth/__init__.spl`:

```simple
arch {
  dimension = "feature"
  layer = "none"

  # This feature declares it consumes entities via a transform target
  uses_transform = "transform/feature/Auth"

  imports {
    allow = ["shared/**", "feature/Auth/**", "transform/feature/Auth/**"]
    deny  = ["entity/**"]
  }
}
```

### 6.3 Entity dimension declaration

In `src/entity/Identity/__init__.spl`:

```simple
arch {
  dimension = "entity"
  layer = "entity"

  imports {
    allow = ["entity/**", "shared/**"]
    deny  = ["feature/**", "transform/**"]  # entities know nothing about features
  }

  exports {
    expose = ["./User", "./Credential"]
  }
}
```

---

## 7. Transform Dimension

The Transform dimension exists solely to reconcile mismatches between decompositions.

### 7.1 Global policy at `src/transform/__init__.spl`

```simple
arch {
  dimension = "transform"
  layer = "none"

  # Explicitly list allowed transform pairs
  transform_pairs = [
    { from = "entity", to = "feature" }
    # future: { from="entity", to="infra" }, { from="entity", to="test" }, etc.
  ]

  imports {
    deny = ["feature/**"]   # global deny - transform never depends on features
  }
}
```

### 7.2 Per-transform directory contract

In `src/transform/feature/Auth/__init__.spl`:

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to   = "feature"
    # Constrain what it may pull from the source dimension
    allow_from = ["entity/Identity/**", "entity/Money/**"]
  }

  imports {
    allow = ["entity/**", "shared/**"]
    deny  = ["feature/**"]   # prevents cyclic reasoning
  }

  exports {
    expose = ["./entity_view/**"]
  }
}
```

### 7.3 The one special power: re-export from another dimension

Only directories that:
1. Are `dimension = "transform"`, AND
2. Declare `transform { from = ..., to = ... }`

...may re-export across dimensions.

**Example: `src/transform/feature/Auth/entity_view/__init__.spl`**

```simple
arch {
  dimension = "transform"
  layer = "none"
}

# Re-export creates a feature-friendly surface without allowing feature → entity imports
reexport entity/Identity/User as User
reexport entity/Identity/Credential as Credential
```

**Rule:** If a non-transform module tries `reexport entity/...`, it is a compile error.

### 7.4 Actual code in the entity_view

`src/transform/feature/Auth/entity_view/AuthModel.spl`:

```simple
from entity/Identity/User import User
from entity/Identity/Credential import Credential
from shared/Result import Result

# Feature-specific auth context - aggregates and simplifies entity types
struct AuthContext:
    """
    Feature-friendly view of authentication state.
    Hides credential complexity from the feature layer.
    """
    user_id: text
    username: text
    email: text
    roles: [text]
    is_verified: bool

    static fn from_user(user: User) -> AuthContext:
        AuthContext(
            user_id: user.id,
            username: user.username,
            email: user.email,
            roles: user.roles.map(\r: r.name),
            is_verified: user.email_verified
        )

# Request/response types at the transform boundary
struct LoginRequest:
    username: text
    password: text

struct LoginResult:
    success: bool
    context: AuthContext?
    error_message: text?
```

---

## 8. Mirrored Transform Tree

To keep navigation predictable, Transform mirrors the destination decomposition:

```
Destination:  feature/Auth/...
Transform:    transform/feature/Auth/...

Destination:  feature/Billing/...
Transform:    transform/feature/Billing/...
```

**Benefits:**
- Consistent paths
- Simple tooling (derive transform path from feature path)
- Easy audits ("what does Auth map from entity?" → open one folder)

---

## 9. Example: Using Entities in Feature Without Direct Imports

### 9.1 Business layer imports only transform

`src/feature/Auth/app/LoginUseCase.spl`:

```simple
# ✅ CORRECT: import only through transform
from transform/feature/Auth/entity_view import AuthContext, LoginRequest, LoginResult

fn login(req: LoginRequest) -> LoginResult:
    # Validate credentials via port (not shown)
    val context = AuthContext(
        user_id: "u1",
        username: req.username,
        email: "user@example.com",
        roles: ["user"],
        is_verified: true
    )
    LoginResult(success: true, context: context, error_message: nil)
```

### 9.2 Entity stays clean and domain-centric

`src/entity/Identity/User.spl`:

```simple
# ✅ CORRECT: no feature knowledge here
struct User:
    id: text
    username: text
    email: text
    email_verified: bool
    roles: [Role]
    password_hash: text
    created_at: text

    fn is_active() -> bool:
        self.email_verified

    fn has_role(role_name: text) -> bool:
        self.roles.any(\r: r.name == role_name)
```

### 9.3 UI layer uses transform types via feature app

`src/feature/Auth/ui/LoginView.spl`:

```simple
from feature/Auth/app import LoginUseCase, LoginRequest

fn render_login_form():
    # UI layer knows about LoginRequest (from transform) via app layer
    # It does NOT need to import entity directly
    pass_todo
```

---

## 10. Why Not Allow Direct feature→entity?

Direct `feature → entity` imports destroy the architectural contract:

1. **Cherry-picking entity internals** — features begin to depend on entity implementation details
2. **Expensive entity refactors** — changing an entity field breaks all features that imported it
3. **Entangled decompositions** — the feature decomposition becomes coupled to domain folder structure

**Transform acts like a module-level anti-corruption layer:**
- Limits the surface area (only expose what feature needs)
- Can rename/re-shape for feature usage
- Is the only place where mismatch is handled
- Makes coupling explicit and auditable

### Rule table

| Import direction | Allowed? | Reason |
|-----------------|----------|--------|
| `feature/*/app` → `transform/**` | ✅ Yes | Feature uses transform bridge |
| `transform/**` → `entity/**` | ✅ Yes | Transform maps entity types |
| `feature/**` → `entity/**` | ❌ No | Bypasses transform, tight coupling |
| `entity/**` → `feature/**` | ❌ No | Entity must stay stable |
| `transform/**` → `feature/**` | ❌ No | Creates cycle |

---

## 11. Hyper/J Comparison Table

| Hyper/J / MDSoC Concept | Meaning | Simple MDSoC Analogue |
|------------------------|---------|----------------------|
| **Dimension** | Axis of decomposition | `dimension` in `__init__.spl` + folder roots (`feature/`, `entity/`, `transform/`) |
| **Concern mapping** | Declare what belongs to what concern | Directory + module placement + `arch {}` blocks |
| **Hyperslice** | Module encapsulating a concern | Directory subtree within a dimension (e.g., `feature/Auth`) |
| **Hypermodule** | Explicit composition spec | `transform { from, to }` + controlled re-export |
| **Declarative completeness** | Slice contains stubs for referenced members | (Future) Interface stubs or "required symbols" in `__init__.spl` |
| **Mismatch reconciliation** | Handle differences between decompositions | Transform dimension with explicit `from→to` mapping |

---

## 12. Pitfalls and Mitigations

### 12.1 Transform becomes a dumping ground

**Risk:** Everything gets dumped into transform and it becomes "the new monolith".

**Mitigation:**
- Per-feature transform folder only
- Strict `allow_from` constraints (whitelist entity modules)
- Tooling: "transform surface report" (export list + source origins)

### 12.2 Cycles via transform

**Risk:** `feature` imports `transform`, `transform` imports `feature`, creating a cycle.

**Mitigation:**
- Default `deny feature/**` imports inside transform
- Enforce DAG at build graph level

### 12.3 Duplicate types / semantic drift

**Risk:** Transform re-exports and renames create duplicate meanings.

**Mitigation:**
- Prefer `reexport` (aliasing) over re-definition
- If adaptation is needed, make it explicit: `type FeatureUser = entity.User` vs new struct
- Require docstring on any "shape-changing" adapter type

### 12.4 Hidden mismatch rules

**Risk:** "Magic" mapping rules are hard to debug.

**Mitigation:**
- Only allow mismatch reconciliation in `transform/**`
- Require explicit `transform { from, to }`
- Generate a machine-readable manifest (see next section)

### 12.5 Interface explosion / over-abstraction

**Risk:** Adding ports everywhere "just in case" makes code harder, not easier.

**Mitigation:** Add a port only when:
- (a) You need test isolation, OR
- (b) You expect that technology to change

---

## 13. Tooling: Required Outputs for Maintainability

A build tool (or compiler phase) should emit:

### 13.1 Dimension graph

```
nodes = packages
edges = imports
highlight = forbidden edges (feature → entity, etc.)
```

Accessible via: `bin/simple build --arch-check` (see `src/app/cli/arch_check.spl`)

### 13.2 Transform manifest

For each transform module:
- `(from_dim, to_dim)` pair
- `allow_from` scopes
- Re-export list (destination symbol → source symbol)

### 13.3 Public API surface

For each feature:
- What it exports
- What it consumes (only through transform)

### 13.4 Layer violation report

```
VIOLATION: src/feature/Checkout/app/CheckoutUseCase.spl
  imports entity/Order/Order (direct feature → entity)
  ALLOWED: import via transform/feature/Checkout/entity_view
```

---

## 14. Principles Summary

1. **Multiple decompositions are real, so model them explicitly** (dimensions)
2. **Entities stay stable and domain-centric** (entity dimension)
3. **Features stay vertical and product-centric** (feature dimension)
4. **All mismatch reconciliation goes through Transform** (explicit from→to mapping)
5. **Re-export across dimensions is illegal unless Transform-authorized**
6. **Architecture is locally declared** in directories (`__init__.spl`) and enforced globally
7. **Policy is stable, mechanisms are volatile** (domain + use-cases are "policy"; DB/UI/frameworks are "mechanisms")
8. **Dependency inversion at every IO boundary** (core owns the interfaces; edges implement them)
9. **One-direction dependency graph** (no cycles; treat modules as a DAG)
10. **Composition root is the only "global knowledge"** (only wiring layer imports both core and adapters)

---

## 15. References

**Hyper/J and MDSoC:**
- CACM: "Using Multi-Dimensional Separation of Concerns to (Re)Shape Evolving Software"
- IBM Research: Hyper/J — Multi-Dimensional Separation of Concerns for Java

**Clean Architecture dependency rule:**
- https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html

**Simple implementation:**
- `src/compiler/mdsoc/` — Compiler-level MDSOC (virtual capsules, carets, layer enforcement)
- `doc/feature/mdsoc_complete.md` — Implementation status (105+ tests, production-ready)
- `doc/guide/standard_architecture.md` — Application-level architecture guide
- `doc/guide/dimension_transform_examples.md` — Practical transform examples
- `doc/guide/transform_init_examples.md` — `__init__.spl` config hierarchy examples
- `src/app/cli/arch_check.spl` — CLI architecture checker
