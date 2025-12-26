# Simple Database Abstraction Layer (DB)

**Date:** 2025-12-18
**Status:** Design Document
**Purpose:** Unified database interface for SQP (Simple Query and Persistence)

---

## Executive Summary

The DB layer provides a **backend-agnostic interface** that enables SQP to work identically across different database engines. SQP sees only a uniform API; it cannot distinguish between PostgreSQL and libSQL.

**Supported Backends:**
- **PostgreSQL** - Production server database
- **libSQL** (embedded) - Local/embedded SQLite-compatible database

```
┌─────────────────────────────────────────────────────────┐
│                    SQP Layer                             │
│   (Query DSL, Data Models, Migrations, Relations)       │
├─────────────────────────────────────────────────────────┤
│                    DB Layer                              │
│   (Unified Interface - This Document)                   │
├──────────────────────┬──────────────────────────────────┤
│   PostgreSQL Driver  │     libSQL Driver                │
│   (tokio-postgres)   │     (libsql-client)              │
└──────────────────────┴──────────────────────────────────┘
```

---

## 1. Design Principles

| Principle | Description |
|-----------|-------------|
| **Backend Transparency** | SQP layer is completely unaware of which backend is active |
| **Common SQL Subset** | Use SQL features available in both PostgreSQL and SQLite |
| **Type Mapping** | Unified type system with automatic backend translation |
| **Connection Pooling** | Transparent pooling for both backends |
| **Transaction Semantics** | Consistent ACID guarantees across backends |
| **Migration Compatibility** | Same migration scripts work on both backends |

---

## 2. Core Interface

### 2.1 Database Connection

```simple
# Database configuration
data DbConfig:
    backend: DbBackend          # postgres | libsql
    connection_string: str      # Backend-specific connection URL
    pool_size: i32 = 10         # Connection pool size
    timeout_ms: i64 = 5000      # Connection timeout

enum DbBackend:
    Postgres                    # PostgreSQL server
    LibSql                      # Embedded libSQL (SQLite-compatible)
    LibSqlRemote                # Remote libSQL (Turso)

# Connection URL formats:
# PostgreSQL:  "postgres://user:pass@host:5432/dbname"
# libSQL:      "file:./data/app.db" or ":memory:"
# libSQL (Turso): "libsql://db-name.turso.io?authToken=..."
```

### 2.2 Database Handle

```simple
# Main database handle (opaque to SQP)
class Db:
    # Connect to database
    @static
    fn connect(config: DbConfig) -> Db | DbError

    # Execute query with parameters
    fn execute(sql: str, params: [DbValue]) -> DbResult | DbError

    # Query with result set
    fn query(sql: str, params: [DbValue]) -> [DbRow] | DbError

    # Query single row
    fn query_one(sql: str, params: [DbValue]) -> DbRow? | DbError

    # Begin transaction
    fn transaction() -> DbTransaction | DbError

    # Prepare statement (for repeated execution)
    fn prepare(sql: str) -> DbStatement | DbError

    # Get backend type (for SQP internal use only)
    fn backend() -> DbBackend

    # Close connection
    fn close() -> () | DbError
```

### 2.3 Transaction API

```simple
class DbTransaction:
    # Execute within transaction
    fn execute(sql: str, params: [DbValue]) -> DbResult | DbError
    fn query(sql: str, params: [DbValue]) -> [DbRow] | DbError

    # Savepoint support
    fn savepoint(name: str) -> () | DbError
    fn rollback_to(name: str) -> () | DbError

    # Commit or rollback
    fn commit() -> () | DbError
    fn rollback() -> () | DbError

# Transaction helper (auto-commit/rollback)
fn with_transaction[T](db: Db, f: (DbTransaction) -> T | DbError) -> T | DbError:
    let tx = db.transaction()?
    match f(tx):
        case Ok(result):
            tx.commit()?
            return result
        case Err(e):
            tx.rollback()?
            return Err(e)
```

### 2.4 Prepared Statements

```simple
class DbStatement:
    # Execute prepared statement
    fn execute(params: [DbValue]) -> DbResult | DbError

    # Query with prepared statement
    fn query(params: [DbValue]) -> [DbRow] | DbError

    # Deallocate (optional - auto on drop)
    fn close() -> ()
```

---

## 3. Type System

### 3.1 Unified Types

The DB layer uses a unified type system that maps to both PostgreSQL and SQLite types.

```simple
enum DbValue:
    Null
    Bool(bool)
    Int(i64)                    # Maps to BIGINT/INTEGER
    Float(f64)                  # Maps to DOUBLE/REAL
    Text(str)                   # Maps to TEXT/VARCHAR
    Blob([u8])                  # Maps to BYTEA/BLOB
    Timestamp(datetime)         # Maps to TIMESTAMP/TEXT (ISO8601)
    Json(JsonValue)             # Maps to JSONB/TEXT (JSON string)
    Uuid(Uuid)                  # Maps to UUID/TEXT
    Decimal(Decimal)            # Maps to NUMERIC/TEXT
```

### 3.2 Type Mapping Table

| Simple Type | DbValue | PostgreSQL | libSQL (SQLite) |
|-------------|---------|------------|-----------------|
| `bool` | `Bool` | `BOOLEAN` | `INTEGER` (0/1) |
| `i32`, `i64` | `Int` | `BIGINT` | `INTEGER` |
| `f32`, `f64` | `Float` | `DOUBLE PRECISION` | `REAL` |
| `str` | `Text` | `TEXT` / `VARCHAR(n)` | `TEXT` |
| `[u8]` | `Blob` | `BYTEA` | `BLOB` |
| `datetime` | `Timestamp` | `TIMESTAMP WITH TIME ZONE` | `TEXT` (ISO8601) |
| `JsonValue` | `Json` | `JSONB` | `TEXT` |
| `Uuid` | `Uuid` | `UUID` | `TEXT` |
| `Decimal` | `Decimal` | `NUMERIC` | `TEXT` |

### 3.3 Type Conversion

```simple
trait FromDbValue:
    fn from_db(value: DbValue) -> Self | DbError

trait ToDbValue:
    fn to_db(self) -> DbValue

# Auto-implemented for standard types
impl ToDbValue for str:
    fn to_db(self) -> DbValue:
        DbValue.Text(self)

impl FromDbValue for str:
    fn from_db(value: DbValue) -> str | DbError:
        match value:
            case Text(s): Ok(s)
            case _: Err(DbError.TypeMismatch("expected Text"))
```

---

## 4. Result Types

### 4.1 Query Results

```simple
# Result of execute (INSERT, UPDATE, DELETE)
data DbResult:
    rows_affected: i64
    last_insert_id: i64?        # Available for INSERT with auto-increment

# Row from query result
data DbRow:
    columns: [str]              # Column names
    values: [DbValue]           # Column values

    # Get value by column name
    fn get[T: FromDbValue](name: str) -> T | DbError

    # Get value by index
    fn get_idx[T: FromDbValue](idx: i32) -> T | DbError

    # Check if column exists
    fn has(name: str) -> bool

    # Get all column names
    fn column_names() -> [str]
```

### 4.2 Error Types

```simple
enum DbError:
    # Connection errors
    ConnectionFailed(msg: str)
    ConnectionTimeout
    PoolExhausted

    # Query errors
    SyntaxError(msg: str, position: i32?)
    ConstraintViolation(constraint: str, msg: str)
    UniqueViolation(column: str)
    ForeignKeyViolation(table: str, column: str)
    NotNullViolation(column: str)
    CheckViolation(constraint: str)

    # Data errors
    TypeMismatch(msg: str)
    DataTruncation(column: str)

    # Transaction errors
    TransactionFailed(msg: str)
    DeadlockDetected
    SerializationFailure

    # Other
    NotFound
    Timeout
    Internal(msg: str)

impl DbError:
    fn is_retriable() -> bool:
        match self:
            case DeadlockDetected | SerializationFailure | Timeout:
                true
            case _:
                false
```

---

## 5. SQL Dialect Abstraction

### 5.1 Query Builder (Internal)

The DB layer internally translates common SQL patterns to backend-specific syntax.

```simple
# Internal query builder (used by DB layer, not exposed to SQP)
class SqlBuilder:
    backend: DbBackend

    # Placeholder syntax: ? (positional) -> backend-specific
    fn translate_placeholders(sql: str) -> str:
        match self.backend:
            case Postgres:
                # Convert ? to $1, $2, $3...
                self.convert_to_numbered(sql)
            case LibSql | LibSqlRemote:
                # Keep ? as-is (SQLite style)
                sql

    # RETURNING clause support
    fn supports_returning() -> bool:
        match self.backend:
            case Postgres: true
            case LibSql | LibSqlRemote: true  # libSQL supports RETURNING

    # UPSERT syntax
    fn upsert_syntax() -> UpsertStyle:
        match self.backend:
            case Postgres:
                UpsertStyle.OnConflict  # ON CONFLICT DO UPDATE
            case LibSql | LibSqlRemote:
                UpsertStyle.OnConflict  # SQLite 3.24+ style

    # Boolean literal
    fn bool_literal(b: bool) -> str:
        match self.backend:
            case Postgres:
                if b: "TRUE" else "FALSE"
            case LibSql | LibSqlRemote:
                if b: "1" else "0"
```

### 5.2 SQL Compatibility Subset

The DB layer enforces a **common SQL subset** that works on both backends:

| Feature | PostgreSQL | libSQL | Supported |
|---------|------------|--------|-----------|
| Basic CRUD | Yes | Yes | **Yes** |
| JOINs (all types) | Yes | Yes | **Yes** |
| Subqueries | Yes | Yes | **Yes** |
| CTEs (WITH) | Yes | Yes | **Yes** |
| Window Functions | Yes | Yes (3.25+) | **Yes** |
| RETURNING | Yes | Yes (3.35+) | **Yes** |
| UPSERT (ON CONFLICT) | Yes | Yes (3.24+) | **Yes** |
| JSON functions | JSONB | JSON1 | **Partial** |
| Full-text search | tsvector | FTS5 | **No** (use raw SQL) |
| Arrays | ARRAY[] | No | **No** |
| Stored Procedures | Yes | No | **No** |
| LISTEN/NOTIFY | Yes | No | **No** |

### 5.3 Unsupported Feature Handling

```simple
# Features that differ between backends
enum DbFeature:
    Arrays
    StoredProcedures
    ListenNotify
    FullTextSearch
    Sequences

impl Db:
    # Check if feature is supported
    fn supports(feature: DbFeature) -> bool:
        match (self.backend(), feature):
            case (Postgres, _): true
            case (LibSql, Arrays): false
            case (LibSql, StoredProcedures): false
            case (LibSql, ListenNotify): false
            case _: false

    # Get backend-specific raw connection (escape hatch)
    fn raw_postgres() -> PostgresConnection? | DbError
    fn raw_libsql() -> LibSqlConnection? | DbError
```

---

## 6. Connection Management

### 6.1 Connection Pool

```simple
# Pool configuration
data PoolConfig:
    min_connections: i32 = 1
    max_connections: i32 = 10
    idle_timeout_ms: i64 = 300000      # 5 minutes
    max_lifetime_ms: i64 = 1800000     # 30 minutes
    connection_timeout_ms: i64 = 5000

# Pool statistics
data PoolStats:
    total_connections: i32
    idle_connections: i32
    active_connections: i32
    waiting_requests: i32

impl Db:
    fn pool_stats() -> PoolStats
    fn resize_pool(min: i32, max: i32) -> () | DbError
```

### 6.2 Health Checks

```simple
impl Db:
    # Ping database
    fn ping() -> () | DbError

    # Check connection health
    fn is_healthy() -> bool:
        self.ping().is_ok()

    # Get server version
    fn version() -> str | DbError
```

---

## 7. Migration Support

### 7.1 Schema Information

```simple
# Table metadata
data TableInfo:
    name: str
    columns: [ColumnInfo]
    primary_key: [str]
    indexes: [IndexInfo]
    foreign_keys: [ForeignKeyInfo]

data ColumnInfo:
    name: str
    db_type: str                # Raw database type
    simple_type: DbValue        # Mapped Simple type
    nullable: bool
    default: str?
    is_primary: bool
    is_auto_increment: bool

data IndexInfo:
    name: str
    columns: [str]
    unique: bool

data ForeignKeyInfo:
    name: str
    columns: [str]
    ref_table: str
    ref_columns: [str]
    on_delete: ForeignKeyAction
    on_update: ForeignKeyAction

enum ForeignKeyAction:
    NoAction
    Restrict
    Cascade
    SetNull
    SetDefault
```

### 7.2 Schema Operations

```simple
impl Db:
    # List tables
    fn tables() -> [str] | DbError

    # Get table info
    fn table_info(name: str) -> TableInfo? | DbError

    # Check if table exists
    fn table_exists(name: str) -> bool | DbError

    # Raw DDL execution (for migrations)
    fn execute_ddl(sql: str) -> () | DbError
```

### 7.3 DDL Translation

```simple
# DDL generator for migrations
class DdlGenerator:
    backend: DbBackend

    fn create_table(name: str, columns: [ColumnDef]) -> str

    fn add_column(table: str, column: ColumnDef) -> str

    fn drop_column(table: str, column: str) -> str

    fn create_index(table: str, name: str, columns: [str], unique: bool) -> str

    fn drop_index(name: str) -> str

    fn add_foreign_key(table: str, fk: ForeignKeyDef) -> str

data ColumnDef:
    name: str
    type: DbType
    nullable: bool = true
    primary: bool = false
    auto_increment: bool = false
    unique: bool = false
    default: DbValue? = None
    check: str? = None

enum DbType:
    Integer
    BigInt
    Float
    Double
    Text
    Text(max_length: i32)
    Blob
    Boolean
    Timestamp
    Json
    Uuid
    Decimal(precision: i32, scale: i32)
```

---

## 8. Backend Implementations

### 8.1 PostgreSQL Backend

```simple
# PostgreSQL-specific configuration
data PostgresConfig:
    host: str = "localhost"
    port: i32 = 5432
    database: str
    user: str
    password: str
    ssl_mode: SslMode = SslMode.Prefer
    application_name: str? = None

enum SslMode:
    Disable
    Allow
    Prefer
    Require
    VerifyCa
    VerifyFull

# PostgreSQL driver (internal)
class PostgresDriver impl DbDriver:
    fn connect(config: PostgresConfig) -> PostgresConnection | DbError
    fn execute(conn: PostgresConnection, sql: str, params: [DbValue]) -> DbResult | DbError
    fn query(conn: PostgresConnection, sql: str, params: [DbValue]) -> [DbRow] | DbError
```

### 8.2 libSQL Backend

```simple
# libSQL-specific configuration
data LibSqlConfig:
    path: str                       # File path or ":memory:"
    flags: LibSqlFlags = LibSqlFlags.default()
    encryption_key: str? = None     # SQLCipher encryption

# Remote libSQL (Turso) configuration
data LibSqlRemoteConfig:
    url: str                        # libsql://...
    auth_token: str
    sync_interval_ms: i64? = None   # For embedded replicas

data LibSqlFlags:
    read_only: bool = false
    create: bool = true
    wal_mode: bool = true           # WAL journal mode
    foreign_keys: bool = true       # Enable FK constraints

# libSQL driver (internal)
class LibSqlDriver impl DbDriver:
    fn connect(config: LibSqlConfig) -> LibSqlConnection | DbError
    fn connect_remote(config: LibSqlRemoteConfig) -> LibSqlConnection | DbError
    fn execute(conn: LibSqlConnection, sql: str, params: [DbValue]) -> DbResult | DbError
    fn query(conn: LibSqlConnection, sql: str, params: [DbValue]) -> [DbRow] | DbError

    # Embedded replica sync (Turso)
    fn sync() -> () | DbError
```

---

## 9. Usage Examples

### 9.1 Basic Usage (Backend-Agnostic)

```simple
use db.*

# Configuration (could come from environment)
let config = DbConfig(
    backend: DbBackend.LibSql,
    connection_string: "file:./data/app.db"
)

# Connect
let db = Db.connect(config)?

# Execute query
let result = db.execute(
    "INSERT INTO users (name, email) VALUES (?, ?)",
    ["Alice", "alice@example.com"]
)?

print(f"Inserted {result.rows_affected} row(s)")

# Query
let users = db.query(
    "SELECT id, name, email FROM users WHERE active = ?",
    [true]

---

**Continued in:** [Part 2](./db_part2.md)
