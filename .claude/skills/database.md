# Database Library Skill

**Purpose:** Guide for using the unified database library (BugDatabase, TestDatabase, FeatureDatabase)

---

## Overview

The unified database library provides production-ready infrastructure for managing structured data with:
- **String interning** for memory efficiency (O(1) operations)
- **Atomic file operations** with locking
- **Query builder** with fluent API
- **SDN file format** for human-readable storage

**Status:** 100% complete, 27/27 tests passing + 80+ integration tests

---

## Architecture

```
Domain Databases (Bug, Test, Feature)
         ↓
   Query Builder (fluent API)
         ↓
  Core Database (SdnDatabase)
         ↓
  Atomic Operations (FileLock)
         ↓
    SDN File Format
```

---

## Core Components

### StringInterner

**Purpose:** Deduplicate strings for memory efficiency

```simple
use lib.database.mod.{StringInterner}

var interner = StringInterner.empty()

# Intern strings (same string → same ID)
id1 = interner.intern("test")
id2 = interner.intern("test")
assert id1 == id2

# Bidirectional lookup
str = interner.lookup(id1)?  # "test"
id = interner.get_id("test")? # id1
```

**Key Features:**
- O(1) intern, lookup, and get_id operations
- Bidirectional mapping (string ↔ ID)
- Export/import to SDN format

### SdnRow

**Purpose:** Store field-value pairs

```simple
use lib.database.mod.{SdnRow}

var row = SdnRow.empty()
row.set("name", "Alice")
row.set("age", "30")
row.set("active", "true")

# Get values
name = row.get("name")?  # "Alice"
age = row.get_i64("age")? # 30
active = row.get_bool("active")? # true
```

### SdnTable

**Purpose:** Store rows with schema

```simple
use lib.database.mod.{SdnTable, SdnRow}

var table = SdnTable.new("users", ["id", "name", "email"])

# Add rows
var row = SdnRow.empty()
row.set("id", "user_1")
row.set("name", "Alice")
row.set("email", "alice@example.com")
table.add_row(row)

# Get row by ID
user = table.get_row("user_1")?

# Soft delete
table.mark_deleted("user_1")

# Get all valid rows
validrows = table.valid_rows()
```

### SdnDatabase

**Purpose:** Multi-table database with persistence

```simple
use lib.database.mod.{SdnDatabase, SdnTable}

# Create new database
var db = SdnDatabase.new("/path/to/db.sdn")

# Add tables
table = SdnTable.new("users", ["id", "name"])
db.set_table("users", table)

# Get table
users = db.get_table("users")?

# Get mutable table (must put back!)
var mut_table = db.get_table_mut("users")?
# ... modify table ...
db.set_table("users", mut_table)  # MUST PUT BACK!

# Save to disk
db.save()

# Load from disk
loaded = SdnDatabase.load("/path/to/db.sdn")?
```

---

## Query Builder

**Purpose:** Fluent API for filtering, sorting, and limiting results

```simple
use lib.database.query.{QueryBuilder, CompareOp}

query = QueryBuilder(db: db, table_name: "users")

# Filter by field
results = query
    .filter_by("status", CompareOp.Eq, "active")
    .filter_by("age", CompareOp.Gt, "18")
    .only_valid()
    .order_by("created_at", desc: true)
    .take(10)
    .execute()
```

**Comparison Operators:**
- `CompareOp.Eq` - Equality
- `CompareOp.Gt` - Greater than
- `CompareOp.Lt` - Less than
- `CompareOp.Contains` - Substring match

**Methods:**
- `.filter_by(field, op, value)` - Filter by condition
- `.filter_in(field, values)` - Filter by list membership
- `.only_valid()` - Exclude soft-deleted rows
- `.order_by(field, desc)` - Sort results
- `.take(n)` - Limit results

---

## BugDatabase

**Purpose:** High-level bug tracking database

```simple
use lib.database.bug.{create_bug_database, Bug, BugSeverity, BugStatus}

# Create database
var bugdb = create_bug_database("/path/to/bugs.sdn")

# Add bug
bug = Bug(
    id: "bug_001",
    severity: BugSeverity.P0,
    status: BugStatus.Open,
    title: "Critical bug",
    description: ["Bug details", "More info"],
    file: "main.spl",
    line: 42,
    reproducible_by: "test_critical",
    fix_strategy: ["Step 1", "Step 2"],
    investigation_log: ["Log entry"],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(bug)

# Query bugs
all = bugdb.all_bugs()
val open = bugdb.open_bugs()  # Open + Investigating + Confirmed
val critical = bugdb.critical_bugs()  # P0 + P1
val p0 = bugdb.bugs_by_severity(BugSeverity.P0)
val investigating = bugdb.bugs_by_status(BugStatus.Investigating)

# Get statistics
val stats = bugdb.stats()
print "Total: {stats.total}, Open: {stats.open}, Health: {stats.health}"

# Validate data
val test_errors = bugdb.validate_test_links()
val fix_errors = bugdb.validate_fix_strategy()

# Save
bugdb.save()

# Load
val loaded = load_bug_database("/path/to/bugs.sdn")?
```

**Bug Severities:**
- `P0` - Critical (blocks release)
- `P1` - High (must fix soon)
- `P2` - Medium (should fix)
- `P3` - Low (nice to fix)
- `Important` - Not a bug, but important

**Bug Statuses:**
- `Open` - Just reported
- `Investigating` - Looking into it
- `Confirmed` - Reproduced and understood
- `Fixed` - Code fixed
- `Closed` - Verified fixed
- `Wontfix` - Won't be fixed

---

## Atomic Operations

**Purpose:** Thread-safe file operations with locking

```simple
use lib.database.atomic.{atomic_read, atomic_write, atomic_append, FileLock}

# Atomic write
atomic_write("/path/to/file.txt", "content")

# Atomic read
val content = atomic_read("/path/to/file.txt")?

# Atomic append
atomic_append("/path/to/log.txt", "new line\n")

# File locking
val lock = FileLock(
    resource: "/path/to/resource.txt",
    lock_path: "/path/to/resource.txt.lock",
    locked_at: rt_timestamp_now()
)

if lock.acquire():
    # ... do work ...
    lock.release()
```

**Lock Features:**
- Stale lock detection (2 hour timeout)
- Automatic cleanup on release
- Timestamp-based locking

---

## Testing

### Unit Tests

```bash
# Run database library tests (27 tests)
./bin/simple_runtime test/lib/database_spec.spl
```

### Integration Tests

```bash
# MCP integration
./bin/simple_runtime test/integration/mcp_bugdb_spec.spl

# Atomic operations
./bin/simple_runtime test/integration/database_atomic_spec.spl

# Query builder
./bin/simple_runtime test/integration/database_query_spec.spl

# End-to-end workflows
./bin/simple_runtime test/integration/database_e2e_spec.spl

# Core components
./bin/simple_runtime test/integration/database_core_spec.spl
```

---

## File Format (SDN)

**Example:**

```sdn
bugs |id, severity, status, title, file, line, created_at, valid|
    bug_001, P0, Open, "Critical bug", main.spl, 42, 2026-02-05, true
    bug_002, P1, Fixed, "High priority", lib.spl, 100, 2026-02-05, true

bug_descriptions |bug_id, line_num, content|
    bug_001, 0, "First line of description"
    bug_001, 1, "Second line of description"
```

---

## Common Patterns

### Create, Add, Save

```simple
var db = create_bug_database("/tmp/bugs.sdn")
db.add_bug(bug)
db.save()
```

### Load, Query, Update, Save

```simple
var db = load_bug_database("/tmp/bugs.sdn")?
val bugs = db.open_bugs()
# ... process bugs ...
db.save()
```

### Atomic File Operations

```simple
# Always use atomic operations for thread safety
atomic_write(path, content)
val data = atomic_read(path)?
```

### Table Mutation Pattern

```simple
# CRITICAL: Must put table back after mutation
var table_opt = db.get_table_mut("users")
if table_opt.?:
    var table = table_opt?
    # ... modify table ...
    db.set_table("users", table)  # MUST PUT BACK!
```

---

## Known Limitations

1. **Module Import:** Module-level functions have import issues in interpreter
2. **Concurrency:** Last-write-wins (no merge conflict resolution)
3. **Performance:** No indexes yet (linear scan for queries)
4. **Transactions:** No ACID transactions (atomic file ops only)

---

## See Also

- **Implementation:** `src/lib/database/`
- **Tests:** `test/lib/database_spec.spl`, `test/integration/`
- **Reports:** `doc/report/mcp_database_integration_2026-02-05.md`
- **MCP Integration:** See `/mcp` skill
