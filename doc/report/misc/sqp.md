# Simple Query and Persistence (SQP)

**Version:** 2025-12
**Status:** Implementation
**Features:** #707-#713

---

## Overview

SQP provides a high-level query DSL and ORM-like data modeling for Simple language. It builds on the DB layer to provide:

- **Casual Mode**: Convention-over-configuration, inferred relationships
- **Formal Mode**: Explicit schema control, SQL-like precision
- **Query DSL**: Type-safe, chainable query builder
- **Relations**: has_many, belongs_to, has_one with eager loading
- **Migrations**: Schema versioning and evolution

```
┌─────────────────────────────────────────────────────────────┐
│                    Simple Application                        │
├─────────────────────────────────────────────────────────────┤
│                    SQP Layer (This Document)                 │
│   ┌───────────────┬───────────────┬───────────────────────┐ │
│   │  Data Models  │  Query DSL    │  Migrations           │ │
│   │  (data/model) │  (where/join) │  (up/down)            │ │
│   └───────────────┴───────────────┴───────────────────────┘ │
├─────────────────────────────────────────────────────────────┤
│                    DB Layer                                  │
│   (Connection, Pool, Transaction, Type Mapping)             │
└─────────────────────────────────────────────────────────────┘
```

---

## Feature Summary

| ID | Feature | Status | Description |
|----|---------|--------|-------------|
| #707 | Casual mode | 📋 | Convention-based, inferred relationships |
| #708 | Formal mode | 📋 | Explicit schema control |
| #709 | Query DSL | 📋 | Type-safe chainable queries |
| #710 | Relations | 📋 | has_many, belongs_to, has_one |
| #711 | Migrations | 📋 | Schema versioning |
| #712 | Eager loading | 📋 | N+1 prevention with preload |
| #713 | Raw SQL escape | 📋 | Escape hatch for complex queries |

---

## Casual Mode (#707)

Casual mode uses conventions to minimize boilerplate. Relationships and table names are inferred.

### Data Definition

```simple
use sqp.*

# Casual mode - conventions inferred
data User:
    name: str
    email: str unique
    age: i32 = 0
    created_at: DateTime = now()
    posts: [Post]           # has_many inferred from type

data Post:
    title: str
    body: str
    published: bool = false
    author: User            # belongs_to inferred from type
    tags: [Tag]             # many_to_many via join table

data Tag:
    name: str unique
    posts: [Post]           # many_to_many (bidirectional)
```

### Convention Rules

| Convention | Inferred Behavior |
|------------|-------------------|
| `field: [Model]` | `has_many` relationship |
| `field: Model` | `belongs_to` relationship |
| `field: Model?` | Optional `belongs_to` |
| Table name | Pluralized, snake_case (`User` → `users`) |
| Primary key | `id: i64` auto-generated |
| Foreign key | `{model}_id` (e.g., `user_id`) |
| Join table | `{model1}_{model2}` alphabetically |

### Generated Schema

```sql
-- Inferred from data User
CREATE TABLE users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    email TEXT NOT NULL UNIQUE,
    age INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL
);

-- Inferred from data Post
CREATE TABLE posts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    title TEXT NOT NULL,
    body TEXT NOT NULL,
    published INTEGER NOT NULL DEFAULT 0,
    user_id INTEGER NOT NULL REFERENCES users(id)
);

-- Join table for many-to-many
CREATE TABLE posts_tags (
    post_id INTEGER NOT NULL REFERENCES posts(id),
    tag_id INTEGER NOT NULL REFERENCES tags(id),
    PRIMARY KEY (post_id, tag_id)
);
```

---

## Formal Mode (#708)

Formal mode provides explicit control over schema, column names, and relationships.

### Model Definition

```simple
use sqp.*

# Formal mode - explicit schema
model User:
    table: "app_users"
    primary_key: "user_id"

    columns:
        user_id: i64 auto_increment
        full_name: str column("name") not_null
        email_address: str column("email") unique not_null
        account_status: str column("status") default("active")
        login_count: i32 default(0)

    relations:
        posts: has_many(Post, foreign_key: "author_id")
        profile: has_one(Profile, foreign_key: "user_id")

    indexes:
        idx_email: unique(email_address)
        idx_status: index(account_status)

model Post:
    table: "blog_posts"

    columns:
        id: i64 auto_increment
        title: str not_null
        content: str column("body")
        author_id: i64 not_null
        created_at: DateTime default(now())
        updated_at: DateTime

    relations:
        author: belongs_to(User, foreign_key: "author_id")

    constraints:
        check_title: check("length(title) > 0")
```

### Formal Mode Features

| Feature | Syntax | Description |
|---------|--------|-------------|
| Custom table | `table: "name"` | Override table name |
| Custom column | `column("name")` | Override column name |
| Primary key | `primary_key: "col"` | Custom primary key |
| Foreign key | `foreign_key: "col"` | Explicit FK column |
| Indexes | `indexes:` block | Define indexes |
| Constraints | `constraints:` block | CHECK, UNIQUE, etc. |
| Auto increment | `auto_increment` | Auto-generated ID |

---

## Query DSL (#709)

Type-safe, chainable query builder.

### Basic Queries

```simple
use sqp.*

# Find all
let users = User.all()

# Find by ID
let user = User.find(42)

# Find with condition
let active_users = User.where(status: "active")

# Multiple conditions
let results = User
    .where(status: "active")
    .where(age: gt(18))
    .order(name: asc)
    .limit(10)
```

### Query Methods

```simple
# Comparison operators
User.where(age: eq(25))      # age = 25
User.where(age: ne(25))      # age != 25
User.where(age: gt(18))      # age > 18
User.where(age: gte(18))     # age >= 18
User.where(age: lt(65))      # age < 65
User.where(age: lte(65))     # age <= 65
User.where(age: between(18, 65))  # age BETWEEN 18 AND 65

# String matching
User.where(name: like("%Alice%"))
User.where(email: starts_with("admin"))
User.where(email: ends_with("@example.com"))

# NULL checks
User.where(deleted_at: is_null())
User.where(verified_at: is_not_null())

# IN clause
User.where(status: in_(["active", "pending"]))
User.where(id: not_in([1, 2, 3]))

# Logical operators
User.where(or_(
    status: eq("admin"),
    role: eq("superuser")
))

User.where(and_(
    status: eq("active"),
    age: gte(18)
))
```

### Ordering and Pagination

```simple
# Order by
User.order(name: asc)
User.order(created_at: desc)
User.order(name: asc, created_at: desc)

# Pagination
User.limit(10)
User.offset(20)
User.page(3, per_page: 10)  # page 3, 10 per page

# Count
let total = User.where(active: true).count()
```

### Aggregations

```simple
# Count
let count = User.count()
let active_count = User.where(active: true).count()

# Sum, Avg, Min, Max
let total_age = User.sum(:age)
let avg_age = User.avg(:age)
let min_age = User.min(:age)
let max_age = User.max(:age)

# Group by
let counts = User
    .group(:status)
    .select(:status, count: count())
```

### Select and Pluck

```simple
# Select specific columns
let names = User.select(:id, :name)

# Pluck single column
let emails = User.pluck(:email)  # returns [str]

# Pluck multiple columns
let pairs = User.pluck(:id, :name)  # returns [(i64, str)]
```

---

## Relations (#710)

### Relationship Types

```simple
# has_many: User has many Posts
data User:
    posts: [Post]  # Casual: inferred has_many

# belongs_to: Post belongs to User
data Post:
    author: User   # Casual: inferred belongs_to

# has_one: User has one Profile
data User:
    profile: Profile?  # Optional has_one

# many_to_many: Posts have many Tags
data Post:
    tags: [Tag]

data Tag:
    posts: [Post]  # Bidirectional many-to-many
```

### Accessing Relations

```simple
let user = User.find(1)

# Access has_many (lazy loaded by default)
for post in user.posts:
    print(post.title)

# Access belongs_to
let post = Post.find(1)
print(post.author.name)

# Access has_one
print(user.profile?.bio)
```

### Eager Loading (#712)

Prevent N+1 queries with `preload`:

```simple
# N+1 problem (bad)
let users = User.all()
for user in users:
    print(user.posts.count)  # Executes query for each user!

# Eager loading (good)
let users = User.preload(:posts).all()
for user in users:
    print(user.posts.count)  # No extra queries

# Nested preload
let users = User
    .preload(:posts, :profile)
    .preload(posts: [:tags, :comments])
    .all()

# Preload with conditions
let users = User
    .preload(posts: Post.where(published: true))
    .all()
```

### Joins

```simple
# Inner join
let results = User
    .join(:posts)
    .where(posts.published: true)
    .select(:id, :name, posts.title)

# Left join
let results = User
    .left_join(:posts)
    .select(:id, :name, posts.title)

# Join with conditions
let results = User
    .join(:posts, posts.published: true)
    .all()
```

---

## Migrations (#711)

### Migration Files

```simple
# migrations/001_create_users.spl

migration "001_create_users":
    up:
        create_table :users:
            id: i64 primary_key auto_increment
            name: str not_null
            email: str not_null unique
            created_at: DateTime default(now())

        create_index :users, :email, unique: true

    down:
        drop_table :users
```

### Migration Operations

```simple
# Create table
create_table :posts:
    id: i64 primary_key auto_increment
    title: str not_null
    body: str
    user_id: i64 not_null references(:users, :id)

# Alter table
alter_table :users:
    add_column :bio, str
    add_column :avatar_url, str
    drop_column :legacy_field
    rename_column :name, :full_name
    change_column :age, i64, null: true

# Create index
create_index :posts, :user_id
create_index :posts, [:user_id, :created_at], name: "idx_user_posts"
create_unique_index :users, :email

# Drop
drop_table :users
drop_index :posts, :idx_user_posts

# Foreign keys
add_foreign_key :posts, :user_id, references: :users, on_delete: :cascade
remove_foreign_key :posts, :user_id
```

### Running Migrations

```bash
# Run pending migrations
simple db migrate

# Rollback last migration
simple db rollback

# Rollback N migrations
simple db rollback --steps 3

# Reset (rollback all, migrate all)
simple db reset

# Migration status
simple db status
```

---

## Raw SQL Escape (#713)

For complex queries not expressible in the DSL:

```simple
# Raw SQL query
let results = Db.raw("""
    SELECT u.*, COUNT(p.id) as post_count
    FROM users u
    LEFT JOIN posts p ON p.user_id = u.id
    WHERE u.status = ?
    GROUP BY u.id
    HAVING COUNT(p.id) > ?
""", ["active", 5])

# Raw SQL in query chain
let users = User
    .where(active: true)
    .where_raw("created_at > DATE_SUB(NOW(), INTERVAL 30 DAY)")
    .order_raw("FIELD(status, 'admin', 'user', 'guest')")
    .all()

# Raw SQL for updates
Db.execute_raw("""
    UPDATE users
    SET login_count = login_count + 1,
        last_login = NOW()
    WHERE id = ?
""", [user_id])
```

---

## CRUD Operations

### Create

```simple
# Create single record
let user = User.create(
    name: "Alice",
    email: "alice@example.com"
)

# Create with relations
let post = Post.create(
    title: "Hello",
    body: "World",
    author: user,
    tags: [Tag.find_or_create(name: "intro")]
)

# Bulk create
let users = User.create_many([
    { name: "Bob", email: "bob@example.com" },
    { name: "Carol", email: "carol@example.com" }
])
```

### Read

```simple
# Find by ID
let user = User.find(1)           # Raises if not found
let user = User.find_by_id(1)     # Returns Option

# Find by attribute
let user = User.find_by(email: "alice@example.com")

# Find or create
let tag = Tag.find_or_create(name: "rust")

# First/Last
let first = User.first()
let last = User.order(created_at: desc).first()

# Exists check
if User.exists(email: "alice@example.com"):
    print("User exists")
```

### Update

```simple
# Update single record
user.update(name: "Alice Smith")

# Update with save
user.name = "Alice Smith"
user.save()

# Bulk update
User.where(status: "inactive")
    .update_all(deleted_at: now())

# Increment/Decrement
user.increment(:login_count)
user.decrement(:credits, by: 10)
```

### Delete

```simple
# Delete single record
user.delete()

# Delete with relations (cascade)
user.delete(cascade: true)

# Bulk delete
User.where(status: "spam").delete_all()

# Soft delete (if supported)
user.soft_delete()
User.with_deleted().where(id: 1)  # Include soft-deleted
```

---

## Transactions

```simple
# Transaction block
Db.transaction(|tx|
    let user = User.create(name: "Alice", email: "alice@example.com")
    let post = Post.create(title: "First Post", author: user)

    if not valid_post?(post):
        tx.rollback()

    # Auto-commits at end
)

# Nested transactions (savepoints)
Db.transaction(|tx|
    User.create(name: "Outer")

    tx.savepoint("inner", |sp|
        User.create(name: "Inner")
        if error:
            sp.rollback()  # Only rolls back inner
    )
)
```

---

## Validation

```simple
data User:
    name: str
    email: str
    age: i32

    validate:
        name: required, min_length(2), max_length(100)
        email: required, email_format, unique
        age: optional, range(0, 150)

# Custom validation
data Post:
    title: str
    body: str

    validate:
        title: required, |t| t.len() <= 200
        body: required

    fn validate_custom(self) -> Result[(), str]:
        if self.title.contains("spam"):
            return Err("Title contains spam")
        Ok(())
```

---

## Schema Introspection (#706)

```simple
# Get table info
let schema = Db.schema()

for table in schema.tables:
    print(f"Table: {table.name}")
    for col in table.columns:
        print(f"  {col.name}: {col.type} {col.constraints}")

# Check if table exists
if schema.table_exists("users"):
    print("Users table exists")

# Get column info
let cols = schema.columns("users")
for col in cols:
    print(f"{col.name}: {col.type}, nullable: {col.nullable}")
```

---

## Configuration

```toml
# simple.toml

[database]
# Default connection
url = "sqlite:./data.db"

# Named connections
[database.connections.primary]
url = "postgres://user:pass@localhost/app"
pool_min = 2
pool_max = 10

[database.connections.replica]
url = "postgres://user:pass@replica/app"
readonly = true

[database.migrations]
directory = "migrations"
table = "schema_migrations"
```

---

## Related Documents

- [db.md](db.md) - Database Abstraction Layer
- [feature.md](feature.md) - Feature tracking
- [spec/stdlib.md](../spec/stdlib.md) - Standard library spec
