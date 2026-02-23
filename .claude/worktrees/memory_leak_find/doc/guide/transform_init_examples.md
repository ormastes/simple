# Transform `__init__.spl` Configuration Examples

Brief examples showing the hierarchy of `__init__.spl` files in the transform dimension.

---

## Directory Structure

```
src/
  transform/
    __init__.spl                           # Root: global transform policy
    feature/
      __init__.spl                         # Feature transform index
      Auth/
        __init__.spl                       # Auth feature transform config
        entity_view/
          __init__.spl                     # Entity view exports
          AuthModel.spl                    # Actual transform code
      Checkout/
        __init__.spl
        entity_view/
          __init__.spl
          CheckoutModel.spl
      Reporting/
        __init__.spl
        entity_view/
          __init__.spl
          ReportingModel.spl
```

---

## 1. Transform Root: `src/transform/__init__.spl`

**Purpose:** Global transform dimension policy

```simple
"""
Transform dimension root.
Defines allowed transformation pairs and global rules.
"""

arch {
  dimension = "transform"
  layer = "none"

  # Global policy: allowed transformation directions
  transform_pairs = [
    { from = "entity", to = "feature" },
    { from = "entity", to = "adapter" },
    { from = "entity", to = "test" }
  ]

  imports {
    allow = [
      "entity/**",
      "shared/**"
    ]
    deny = [
      "feature/**",    # Prevent cycles
      "adapters/**"
    ]
  }
}

# Re-export all feature transforms
export transform/feature/**
```

---

## 2. Feature Transform Index: `src/transform/feature/__init__.spl`

**Purpose:** Index of all feature transforms

```simple
"""
Feature transforms index.
Each feature has its own transform subdirectory.
"""

arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to = "feature"
  }

  imports {
    allow = [
      "entity/**",
      "shared/**"
    ]
    deny = [
      "feature/**"
    ]
  }
}

# Re-export all feature-specific transforms
export transform/feature/Auth/**
export transform/feature/Checkout/**
export transform/feature/Reporting/**
```

---

## 3. Feature Transform Config: `src/transform/feature/Auth/__init__.spl`

**Purpose:** Auth feature transform configuration

```simple
"""
Auth feature transform.
Provides auth-specific views of Identity and Session entities.
"""

arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to = "feature"

    # Explicit allow list: only these entity modules
    allow_from = [
      "entity/Identity/**",
      "entity/Session/**",
      "entity/Audit/**"
    ]
  }

  imports {
    allow = [
      "entity/Identity/**",
      "entity/Session/**",
      "entity/Audit/**",
      "shared/**"
    ]
    deny = [
      "feature/**",           # No cycles
      "entity/Order/**",      # Not needed for Auth
      "entity/Product/**"     # Not needed for Auth
    ]
  }

  exports {
    # Expose only entity_view
    expose = [
      "./entity_view/**"
    ]
  }

  # Metadata
  feature = "Auth"
  description = "Authentication and authorization entity transforms"
  owner = "security-team"
  tags = ["auth", "security", "identity"]
}

# Re-export entity view
export transform/feature/Auth/entity_view/**
```

---

## 4. Entity View Module: `src/transform/feature/Auth/entity_view/__init__.spl`

**Purpose:** Actual transform exports (what feature imports)

```simple
"""
Auth entity view exports.
This is what feature/Auth/app/** imports from.
"""

arch {
  dimension = "transform"
  layer = "none"
}

# Re-export entities (simple alias)
reexport entity/Identity/User as User
reexport entity/Identity/Credential as Credential
reexport entity/Identity/Role as Role
reexport entity/Session/Session as Session
reexport entity/Session/Token as Token

# Export adapted types
export ./AuthModel.{AuthContext, LoginRequest, LoginResponse}
export ./PermissionModel.{PermissionCheck, AccessControl}
```

---

## 5. Actual Transform Code: `src/transform/feature/Auth/entity_view/AuthModel.spl`

**Purpose:** Feature-specific adaptations

```simple
"""
Auth-specific entity adaptations.
Simplifies complex Identity model for Auth feature.
"""

# These are already re-exported by __init__.spl
# Available: User, Credential, Role, Session, Token

struct AuthContext:
    """
    Simplified auth context for Auth feature.
    Aggregates User + Session + Token.
    """
    user: User
    session: Session
    token: Token

    fn is_authenticated() -> bool:
        self.session.is_active() and self.token.is_valid()

    fn has_role(role_name: text) -> bool:
        self.user.has_role(role_name)

    fn user_id() -> text:
        self.user.id

struct LoginRequest:
    """Feature-specific request model."""
    username: text
    password: text
    remember_me: bool
    mfa_code: text?

struct LoginResponse:
    """Feature-specific response model."""
    success: bool
    token: Token?
    error_message: text?
    requires_mfa: bool
    session_id: text?
```

---

## 6. Feature Uses Transform: `src/feature/Auth/app/LoginUseCase.spl`

**Purpose:** Use case imports ONLY from transform

```simple
"""
Login use case.
Imports ONLY from transform, never directly from entity.
"""

# ✅ CORRECT: import from transform
from transform/feature/Auth/entity_view import AuthContext, LoginRequest, LoginResponse, User, Credential, Token

# ❌ FORBIDDEN: direct entity import
# from entity/Identity/User import User  # ← Compile error!

from shared import Result

fn login(request: LoginRequest) -> Result:
    """
    @tag:api
    Authenticate user and create session.
    Uses transform-provided types only.
    """
    # Use transform types (User, Credential, AuthContext, etc.)
    val user = find_user(request.username)
    if user == nil:
        return Result.error("User not found")

    val cred = fetch_credential(user.id)
    if not verify_password(cred, request.password):
        return Result.error("Invalid password")

    # Create auth context using transform types
    val session = create_session(user)
    val token = generate_token(session)

    val ctx = AuthContext(
        user: user,
        session: session,
        token: token
    )

    Result.ok(LoginResponse(
        success: true,
        token: token,
        error_message: nil,
        requires_mfa: false,
        session_id: session.id
    ))

# Ports (injected)
fn find_user(username: text) -> User?:
    pass_todo

fn fetch_credential(user_id: text) -> Credential:
    pass_todo

fn verify_password(cred: Credential, password: text) -> bool:
    pass_todo

fn create_session(user: User) -> Session:
    pass_todo

fn generate_token(session: Session) -> Token:
    pass_todo
```

---

## 7. Feature Config (for reference): `src/feature/Auth/__init__.spl`

**Purpose:** Feature enforces dependency rules

```simple
"""
Auth feature configuration.
Enforces that app layer uses transform, not entity directly.
"""

arch {
  dimension = "feature"
  layer = "none"

  # Feature declares it uses Auth transform
  uses_transform = "transform/feature/Auth"

  imports {
    allow = [
      "feature/Auth/**",
      "transform/feature/Auth/**",  # ✅ Allow transform
      "shared/**"
    ]
    deny = [
      "entity/**"  # ❌ Block direct entity access
    ]
  }

  exports {
    expose = [
      "./app/LoginUseCase",
      "./app/LogoutUseCase",
      "./app/RefreshTokenUseCase"
    ]
  }

  feature = "Auth"
  description = "Authentication and authorization"
  owner = "security-team"
}

export ./app/**
export ./ui/**
```

---

## Configuration Fields Reference

### `arch {}` Block

| Field | Values | Purpose |
|-------|--------|---------|
| `dimension` | `"transform"`, `"feature"`, `"entity"`, `"shared"` | Declares dimension |
| `layer` | `"ui"`, `"app"`, `"entity"`, `"none"` | Declares layer |
| `transform` | `{ from, to, allow_from }` | Transform-specific config |
| `imports.allow` | `["pattern/**"]` | Allowed import patterns |
| `imports.deny` | `["pattern/**"]` | Forbidden import patterns |
| `exports.expose` | `["./path"]` | Public API surface |
| `uses_transform` | `"transform/feature/Name"` | Feature's transform dependency |
| `transform_pairs` | `[{ from, to }]` | Global allowed pairs (root only) |

### Transform-Specific Fields

| Field | Type | Purpose |
|-------|------|---------|
| `transform.from` | `text` | Source dimension (`"entity"`) |
| `transform.to` | `text` | Target dimension (`"feature"`) |
| `transform.allow_from` | `[text]` | Allowed source modules |

### Metadata Fields (optional)

| Field | Type | Purpose |
|-------|------|---------|
| `feature` | `text` | Feature name |
| `description` | `text` | Module description |
| `owner` | `text` | Team/person responsible |
| `tags` | `[text]` | Classification tags |

---

## Dependency Flow Visualization

```
┌─────────────────────────────────────────────────────────┐
│  feature/Auth/app/LoginUseCase.spl                      │
│  from transform/feature/Auth/entity_view import User    │
└────────────────────┬────────────────────────────────────┘
                     │ (allowed by feature Auth __init__)
                     ↓
┌─────────────────────────────────────────────────────────┐
│  transform/feature/Auth/entity_view/__init__.spl        │
│  reexport entity/Identity/User as User                  │
└────────────────────┬────────────────────────────────────┘
                     │ (allowed by transform Auth __init__)
                     ↓
┌─────────────────────────────────────────────────────────┐
│  entity/Identity/User.spl                               │
│  struct User: ...                                       │
└─────────────────────────────────────────────────────────┘
```

---

## Enforcement (Compiler/Build Tool)

The compiler/build tool should:

1. **Parse all `__init__.spl` files** in dependency order
2. **Check imports** against `allow`/`deny` patterns
3. **Validate transform pairs** against root `transform_pairs`
4. **Verify `reexport` statements** only in `dimension="transform"` modules
5. **Generate warnings** for violations
6. **Fail build** on forbidden imports (unless `--force` flag)

---

## Quick Reference

**Root transform** (`src/transform/__init__.spl`):
- Defines global `transform_pairs`
- Denies `feature/**` and `adapters/**`

**Feature transform index** (`src/transform/feature/__init__.spl`):
- Re-exports all feature transforms
- Declares `transform { from="entity", to="feature" }`

**Specific feature transform** (`src/transform/feature/Auth/__init__.spl`):
- Declares `allow_from` (explicit entity modules)
- Exposes `./entity_view/**` only

**Entity view** (`src/transform/feature/Auth/entity_view/__init__.spl`):
- Re-exports entity types
- Exports adapted types from `AuthModel.spl`

**Feature config** (`src/feature/Auth/__init__.spl`):
- Declares `uses_transform = "transform/feature/Auth"`
- Allows `transform/feature/Auth/**`
- Denies `entity/**`
