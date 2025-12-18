# Simple Query and Persistence (SQP)

**Date:** 2025-12-18
**Status:** Design Document
**Related:** [db.md](./db.md) - Database Abstraction Layer

---

## Overview

SQP is the high-level query and persistence layer for Simple language. It provides an intuitive DSL for database operations while the underlying [DB layer](./db.md) handles backend-specific details.

```
┌─────────────────────────────────────────────────────────┐
│                    Your Simple Code                      │
│   data User: name, email                                │
│   User.where(active: true).limit(10)                    │
├─────────────────────────────────────────────────────────┤
│                    SQP Layer (This Document)            │
│   Data models, Query DSL, Relations, Migrations         │
├─────────────────────────────────────────────────────────┤
│                    DB Layer (db.md)                     │
│   Unified interface, type mapping, connection pool      │
├──────────────────────┬──────────────────────────────────┤
│   PostgreSQL         │     libSQL (SQLite)              │
└──────────────────────┴──────────────────────────────────┘
```

**Key Features:**
- **Casual Mode**: Minimal typing, maximum inference (90% of use cases)
- **Formal Mode**: Explicit control with decorators
- **Backend-Agnostic**: Same code works on PostgreSQL and libSQL

---

## Design Principles (matching Simple's philosophy)

| Goal | Approach |
|------|----------|
| Less typing | Infer types, auto-generate IDs |
| Easy to read | Declarative, no annotations spam |
| Formal when needed | Optional explicit schema mode |
| Backend transparency | SQP never sees database differences |

---

## **1. Casual Mode (Minimal Typing)**

```python
# Automatic: id, created_at, updated_at
data User:
    name: str
    email: str unique
    posts: [Post]      # has_many inferred

data Post:
    title: str
    body: str
    author: User       # belongs_to inferred
    tags: [Tag] many   # many-to-many
```

**What's inferred:**
- `id: i64 primary` (auto)
- `created_at: datetime` (auto)
- Foreign keys from type reference
- Table names from `data` name (snake_case)

---

## **2. Formal Mode (Explicit Schema)**

```python
@table("users")
data User:
    @primary @auto
    id: i64
    
    @unique @index
    email: str(255)
    
    @nullable
    bio: str?
    
    @has_many(Post, foreign: "author_id", cascade: delete)
    posts: [Post]
    
    @timestamps
```

---

## **3. Query DSL (Ruby-inspired, Simple-native)**

```python
# Simple queries - chainable
users = User.where(active: true)
            .order(created_at: desc)
            .limit(10)

# Lambda filters (using Simple's \x syntax)
adults = User.filter \u: u.age >= 18

# Eager loading
posts = Post.include(:author, :tags)
            .where(published: true)

# Raw SQL escape hatch
result = db.query "SELECT * FROM users WHERE id = ?", [user_id]
```

---

## **4. Comparison: Casual vs Formal**

```python
# ========== CASUAL (5 lines) ==========
data User:
    name: str
    email: str unique
    posts: [Post]

# ========== FORMAL (15 lines) ==========
@table("users")
@timestamps
data User:
    @primary @auto
    id: i64
    
    @column("full_name") @index
    name: str(100)
    
    @unique @index
    email: str(255)
    
    @has_many(Post, foreign: "user_id", cascade: delete)
    posts: [Post]
```

---

## **5. Suggested Keywords**

| Keyword | Meaning | Formal Equiv |
|---------|---------|--------------|
| `data` | DB entity (like Prisma `model`) | `@table` |
| `unique` | Unique constraint | `@unique` |
| `[Type]` | Has-many relation | `@has_many` |
| `Type` | Belongs-to relation | `@belongs_to` |
| `Type?` | Nullable | `@nullable` |
| `many` | Many-to-many | `@many_to_many` |

---

## **6. Migration (Auto-inferred)**

```python
# migrations/001_create_users.spl (auto-generated)
migrate "create_users":
    create_table "users":
        id: i64 primary auto
        name: str(255)
        email: str(255) unique index
        created_at: datetime
        updated_at: datetime
```

---

## My Recommendation

For Simple language, I suggest a **layered approach**:

```
┌─────────────────────────────────────┐
│  Casual Mode (default)              │  ← 90% of cases
│  - Minimal keywords                 │
│  - Maximum inference                │
├─────────────────────────────────────┤
│  Formal Mode (@decorators)          │  ← When precision needed
│  - Explicit constraints             │
│  - Full control                     │
├─────────────────────────────────────┤
│  Raw SQL (escape hatch)             │  ← Edge cases
│  - db.query "..."                   │
└─────────────────────────────────────┘
```

**This matches Simple's philosophy**: Easy things should be easy (casual mode), hard things should be possible (formal mode).

---

## **7. Database Backend Integration**

SQP uses the [DB layer](./db.md) for all database operations. The DB layer provides:

| DB Layer Feature | SQP Usage |
|------------------|-----------|
| `Db.connect()` | Connection management (auto-configured) |
| `Db.execute()` | INSERT, UPDATE, DELETE operations |
| `Db.query()` | SELECT operations |
| `Db.transaction()` | Transaction support for `.save()` |
| `DbValue` types | Automatic type mapping |

### Backend Selection

```simple
# Development: embedded libSQL (default)
# Production: PostgreSQL (via DATABASE_URL)

# SQP auto-detects from environment
let users = User.where(active: true)  # Works on both backends!
```

### Type Mapping (SQP → DB)

| SQP Type | DbValue | PostgreSQL | libSQL |
|----------|---------|------------|--------|
| `str` | `Text` | `TEXT` | `TEXT` |
| `str(n)` | `Text` | `VARCHAR(n)` | `TEXT` |
| `i64` | `Int` | `BIGINT` | `INTEGER` |
| `f64` | `Float` | `DOUBLE PRECISION` | `REAL` |
| `bool` | `Bool` | `BOOLEAN` | `INTEGER` |
| `datetime` | `Timestamp` | `TIMESTAMPTZ` | `TEXT` (ISO8601) |
| `[u8]` | `Blob` | `BYTEA` | `BLOB` |

---

## **8. Transaction Support**

```simple
# Explicit transaction
db.transaction \tx:
    let user = User.create(name: "Alice", email: "alice@test.com")
    let post = Post.create(title: "Hello", author: user)
    tx.commit()

# Or use save! for auto-transaction
User.save!(name: "Bob", email: "bob@test.com")  # Implicit transaction
```

---

## **9. Connection Configuration**

SQP reads configuration from `simple.toml` or environment:

```toml
# simple.toml
[database]
backend = "libsql"              # or "postgres"
url = "file:./data/app.db"      # or "postgres://..."

[database.pool]
max = 10
idle_timeout_ms = 300000
```

```bash
# Or via environment
export DATABASE_URL="postgres://user:pass@host/db"
export DB_BACKEND="postgres"
```

---

## **10. Implementation Notes**

### SQP Generates SQL via DB Layer

```simple
# SQP DSL:
User.where(active: true).order(name: asc).limit(10)

# Translates to DB layer call:
db.query(
    "SELECT * FROM users WHERE active = ? ORDER BY name ASC LIMIT ?",
    [true, 10]
)

# DB layer handles:
# - Placeholder syntax (? → $1 for Postgres)
# - Boolean conversion (true → TRUE or 1)
# - Connection pooling
```

### Migration Integration

```simple
# SQP migration uses DB layer's DDL generator
migrate "create_users":
    create_table "users":
        id: i64 primary auto
        name: str(255)
        email: str(255) unique

# DB layer generates backend-specific DDL:
# PostgreSQL: CREATE TABLE users (id BIGSERIAL PRIMARY KEY, ...)
# libSQL: CREATE TABLE users (id INTEGER PRIMARY KEY AUTOINCREMENT, ...)
```

---

## Related Documentation

- [db.md](./db.md) - Database Abstraction Layer (backend-agnostic interface)
- [spec/data_structures.md](./spec/data_structures.md) - Data type specifications
- [feature.md](./feature.md) - Feature status and roadmap
