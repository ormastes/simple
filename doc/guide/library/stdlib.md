# Standard Library Guide

Covers SDN format, string utilities, database access (DB + SQP), and atomic text databases.

---

## SDN (Simple Data Notation)

SDN is Simple's native configuration format, replacing TOML. It is 30-50% more token-efficient and integrates natively with Simple tooling.

### Syntax

```sdn
# Comments start with #

# Key-value pairs
name: my-project
version: 1.0.0
enabled: true
count: 42
ratio: 3.14

# Arrays
features: [auth, logging, metrics]

# Nested objects
server:
  database:
    host: localhost
    port: 5432

# Tables (structured data)
users |id, name, role|
  1, Alice, admin
  2, Bob, user
```

### Package Manifest (simple.sdn)

```sdn
package:
  name: my-project
  version: 1.0.0
  license: MIT
  description: A useful library

dependencies:
  http: 2.0
  json:
    version: 1.5
    features: [serde]
```

### Migration from TOML

| TOML | SDN |
|------|-----|
| `[section]` | `section:` |
| `key = "value"` | `key: value` |
| `[section.nested]` | Indented under parent |
| `features = ["a", "b"]` | `features: [a, b]` |

Both formats are supported during transition. `simple.sdn` is checked first; `simple.toml` is a fallback.

```bash
# Verify SDN works
simple check
simple test --list
```

---

## String Core Module

**Module:** `std.text_core`

### Basic Operations

```simple
use std.text_core.{str_len, str_concat, str_eq}

str_len("hello")              # 5
str_concat("hello", " world") # "hello world"
str_eq("test", "test")        # true
```

### Slicing and Access

```simple
use std.text_core.{str_slice, str_char_at, str_safe_slice}

str_slice("hello", 0, 3)       # "hel"
str_char_at("hello", 1)        # "e"
str_char_at("hello", 99)       # "" (safe, returns empty)
str_safe_slice("hi", -1, 100)  # "hi" (bounds-safe)
```

### Search

```simple
use std.text_core.{str_contains, str_starts_with, str_ends_with}
use std.text_core.{str_index_of, str_last_index_of}

str_contains("hello world", "world")  # true
str_index_of("hello", "l")            # 2
str_last_index_of("hello", "l")       # 3
str_index_of("hello", "x")            # -1
```

### Trimming, Replacement, Split/Join

```simple
use std.text_core.{str_trim, str_replace_all, str_split, str_join}

str_trim("  hello  ")                  # "hello"
str_replace_all("hello", "l", "L")    # "heLLo"
str_split("a,b,c", ",")               # ["a", "b", "c"]
str_join(["x", "y", "z"], "-")        # "x-y-z"
```

### Case Conversion and Manipulation

```simple
use std.text_core.{str_to_lower, str_to_upper, str_capitalize}
use std.text_core.{str_reverse, str_repeat, str_pad_left}

str_to_lower("HELLO")      # "hello"
str_to_upper("hello")      # "HELLO"
str_capitalize("hello")    # "Hello"
str_reverse("hello")       # "olleh"
str_repeat("ab", 3)        # "ababab"
str_pad_left("42", 5, "0") # "00042"
```

**Note:** Case conversion is ASCII only (A-Z, a-z). Use intermediate `var` instead of chained method calls (runtime limitation).

### When to Use Which Module

| Need | Module |
|------|--------|
| Basic string ops (length, concat, trim, split) | `std.text_core` |
| ASCII lookup, platform newlines, hashing | `std.text` |
| HTML/URL/JS/CSS escaping, hex conversion | `std.template.utilities` |

---

## Database Abstraction (DB Layer)

The DB layer provides a backend-agnostic interface for SQL databases. SQP (below) builds on top of it.

```
SQP Layer (Query DSL, Data Models, Migrations)
DB Layer (Unified Interface)
PostgreSQL Driver  |  libSQL Driver
```

### Connecting

```simple
use db.*

val config = DbConfig(
    backend: DbBackend.LibSql,
    connection_string: "file:./data/app.db"
)

val db = Db.connect(config)?
```

**Backends:**

| Backend | Connection String |
|---------|------------------|
| PostgreSQL | `postgres://user:pass@host:5432/dbname` |
| libSQL (local) | `file:./data/app.db` or `:memory:` |
| libSQL (Turso) | `libsql://db-name.turso.io?authToken=...` |

### Queries

```simple
# Execute (INSERT, UPDATE, DELETE)
val result = db.execute(
    "INSERT INTO users (name, email) VALUES (?, ?)",
    ["Alice", "alice@example.com"]
)?
print "Inserted {result.rows_affected} row(s)"

# Query
val users = db.query(
    "SELECT id, name FROM users WHERE active = ?",
    [true]
)?

for row in users:
    val id: i64 = row.get("id")?
    val name: str = row.get("name")?
    print "User {id}: {name}"
```

### Transactions

```simple
with_transaction(db) \tx:
    tx.execute("UPDATE accounts SET balance = balance - ? WHERE id = ?", [100, 1])?
    tx.execute("UPDATE accounts SET balance = balance + ? WHERE id = ?", [100, 2])?
    Ok(())
```

### Type Mapping

| Simple Type | PostgreSQL | libSQL (SQLite) |
|-------------|------------|-----------------|
| `bool` | `BOOLEAN` | `INTEGER` (0/1) |
| `i64` | `BIGINT` | `INTEGER` |
| `f64` | `DOUBLE PRECISION` | `REAL` |
| `str` | `TEXT` | `TEXT` |
| `datetime` | `TIMESTAMPTZ` | `TEXT` (ISO8601) |
| `[u8]` | `BYTEA` | `BLOB` |

### Switching Backends

```simple
# Development
val dev_config = DbConfig(
    backend: DbBackend.LibSql,
    connection_string: "file:./dev.db"
)

# Production
val prod_config = DbConfig(
    backend: DbBackend.Postgres,
    connection_string: "postgres://user:pass@prod-db:5432/app"
)

# Same code works with both
val db = Db.connect(if is_production: prod_config else dev_config)?
```

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `DATABASE_URL` | Connection string | `file:./data/app.db` |
| `DB_BACKEND` | Backend type | `libsql` |
| `DB_POOL_MAX` | Max pool connections | `10` |
| `DB_TIMEOUT_MS` | Connection timeout | `5000` |

---

## SQP (Simple Query and Persistence)

SQP is the high-level query and persistence DSL built on the DB layer.

### Casual Mode (Default)

```simple
data User:
    name: str
    email: str unique
    posts: [Post]          # has_many inferred

data Post:
    title: str
    body: str
    author: User           # belongs_to inferred
    tags: [Tag] many       # many-to-many
```

Auto-generated fields: `id: i64 primary`, `created_at: datetime`, `updated_at: datetime`. Foreign keys inferred from type references.

### Formal Mode

```simple
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

### Query DSL

```simple
users = User.where(active: true)
            .order(created_at: desc)
            .limit(10)

adults = User.filter \u: u.age >= 18

posts = Post.include(:author, :tags)
            .where(published: true)

# Raw SQL escape hatch
result = db.query "SELECT * FROM users WHERE id = ?", [user_id]
```

### Transactions

```simple
db.transaction \tx:
    val user = User.create(name: "Alice", email: "alice@test.com")
    val post = Post.create(title: "Hello", author: user)
    tx.commit()
```

### Migrations

```simple
# Auto-generated from data definitions
migrate "create_users":
    create_table "users":
        id: i64 primary auto
        name: str(255)
        email: str(255) unique index
        created_at: datetime
        updated_at: datetime
```

---

## Atomic Text Database

**Module:** `std.db_atomic`

Thread-safe, atomic database operations for SDN-formatted text files with file locking, atomic writes, and backup management.

### Basic Operations

```simple
use std.db_atomic.{atomic_read, atomic_write, atomic_update, DbConfig}

# Read
val content = atomic_read("data.sdn", DbConfig.defaults())?

# Write
atomic_write("data.sdn", "new content", DbConfig.defaults())?

# Atomic update (read-modify-write with locking)
atomic_update("data.sdn", |content| {
    content + "\n    new_row, value1, value2"
}, DbConfig.defaults())?
```

### AtomicTable

```simple
use std.db_atomic.{AtomicTable, DbConfig}

# Create table
val table = AtomicTable.create(
    "todos.sdn", "todos",
    ["id", "title", "status"],
    DbConfig.defaults()
)?

# Add row
table.add_row(["1", "Fix bug", "done"])?

# Load existing
val existing = AtomicTable.load("todos.sdn", "todos", DbConfig.defaults())?
```

### Configuration Profiles

| Profile | Lock Timeout | Size Limit | Backups |
|---------|-------------|------------|---------|
| `DbConfig.defaults()` | 10s | 500 MB | 5 kept |
| `DbConfig.no_backups()` | 10s | 500 MB | None |
| `DbConfig.strict()` | 30s | 100 MB | 10 kept |

### Atomic Write Pattern

1. Acquire exclusive file lock
2. Create backup (if configured)
3. Write to temporary file
4. Rename temp to target (atomic)
5. Release lock

### Batch Operations

```simple
# Single lock acquisition for multiple rows
table.update(|content| {
    var new_content = content
    for item in items:
        new_content = new_content + format_row(item)
    new_content
})?
```

---

## SMF note.sdn Metadata

The `note.sdn` section in SMF files tracks generic instantiation metadata for lazy instantiation, circular dependency detection, and hot-reload support.

### Tracking Instantiations

```simple
use simple/compiler/monomorphize/note_sdn.*

var note = NoteSdnMetadata.new()

note.add_instantiation(InstantiationEntry.new(
    template: "List",
    type_args: [ConcreteType.Named("Int", [])],
    mangled_name: "List$Int",
    from_file: "app.spl",
    from_loc: "app.spl:10:5",
    to_obj: "app.o",
    status: InstantiationStatus.Compiled
))

note.add_dependency(DependencyEdge.new(
    from_inst: "List$Int",
    to_inst: "Int",
    dep_kind: DependencyKind.TypeParam
))

val sdn_text = note.to_sdn()
```

### Instantiation Status

| Status | Meaning |
|--------|---------|
| `Compiled` | Compiled to native code |
| `Deferred` | Deferred for lazy compilation |
| `JitCompiled` | JIT-compiled at runtime |

---

## Related Files

- SDN syntax reference: `doc/guide/sdn_syntax_guide.md`
- String core: `src/lib/common/string_core.spl`
- DB & SQP: `doc/guide/apps/database.md`
- Atomic DB: `src/lib/nogc_sync_mut/db_atomic.spl`
- Note SDN: `src/compiler/40.mono/note_sdn.spl`
