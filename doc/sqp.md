## Proposed: **Simple  Query and Persisrence**

### Design Principles (matching Simple's philosophy)
| Goal | Approach |
|------|----------|
| Less typing | Infer types, auto-generate IDs |
| Easy to read | Declarative, no annotations spam |
| Formal when needed | Optional explicit schema mode |

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

