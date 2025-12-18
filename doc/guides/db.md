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
)?

for row in users:
    let id: i64 = row.get("id")?
    let name: str = row.get("name")?
    print(f"User {id}: {name}")

# Transaction
with_transaction(db) \tx:
    tx.execute("UPDATE accounts SET balance = balance - ? WHERE id = ?", [100, 1])?
    tx.execute("UPDATE accounts SET balance = balance + ? WHERE id = ?", [100, 2])?
    Ok(())
```

### 9.2 SQP Integration

```simple
# SQP uses DB layer internally
# User sees only SQP API, never DB directly

data User:
    name: str
    email: str unique

# SQP internally generates:
# - CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT, email TEXT UNIQUE, ...)
# - Uses Db.execute() for all operations

# User query (SQP DSL)
let users = User.where(active: true).limit(10)

# SQP translates to:
# db.query("SELECT * FROM users WHERE active = ? LIMIT ?", [true, 10])
```

### 9.3 Switching Backends

```simple
# Development: Use embedded libSQL
let dev_config = DbConfig(
    backend: DbBackend.LibSql,
    connection_string: "file:./dev.db"
)

# Production: Use PostgreSQL
let prod_config = DbConfig(
    backend: DbBackend.Postgres,
    connection_string: "postgres://user:pass@prod-db:5432/app"
)

# Same code works with both!
let db = Db.connect(if is_production: prod_config else dev_config)?

# SQP doesn't know or care which backend is used
let users = User.all()
```

### 9.4 Embedded Replica (Turso)

```simple
# Local SQLite with Turso cloud sync
let config = DbConfig(
    backend: DbBackend.LibSqlRemote,
    connection_string: "libsql://mydb.turso.io?authToken=xxx"
)

# Or embedded replica (local + sync)
let replica_config = LibSqlRemoteConfig(
    url: "libsql://mydb.turso.io",
    auth_token: "xxx",
    sync_interval_ms: 60000  # Sync every minute
)

let db = Db.connect_libsql_remote(replica_config)?

# Queries hit local replica (fast!)
# Writes sync to cloud
```

---

## 10. Design Patterns

### 10.1 Repository Pattern Integration

```simple
# Generic repository (used by SQP)
trait Repository[T]:
    fn find_by_id(id: i64) -> T? | DbError
    fn find_all() -> [T] | DbError
    fn save(entity: T) -> T | DbError
    fn delete(entity: T) -> () | DbError

# SQP generates repository implementations
class UserRepository impl Repository[User]:
    db: Db

    fn find_by_id(id: i64) -> User? | DbError:
        let row = self.db.query_one(
            "SELECT * FROM users WHERE id = ?",
            [id]
        )?
        match row:
            case Some(r): Some(User.from_row(r))
            case None: None

    fn save(user: User) -> User | DbError:
        if user.id == 0:
            # INSERT
            let result = self.db.execute(
                "INSERT INTO users (name, email) VALUES (?, ?) RETURNING id",
                [user.name, user.email]
            )?
            user.id = result.last_insert_id?
        else:
            # UPDATE
            self.db.execute(
                "UPDATE users SET name = ?, email = ? WHERE id = ?",
                [user.name, user.email, user.id]
            )?
        Ok(user)
```

### 10.2 Connection Factory

```simple
# Factory for creating database connections
class DbFactory:
    @static
    fn from_env() -> Db | DbError:
        let backend = env("DB_BACKEND") ?? "libsql"
        let url = env("DATABASE_URL") ?? "file:./data/app.db"

        let config = DbConfig(
            backend: match backend:
                case "postgres": DbBackend.Postgres
                case "libsql": DbBackend.LibSql
                case _: DbBackend.LibSql,
            connection_string: url
        )

        Db.connect(config)

    @static
    fn in_memory() -> Db | DbError:
        Db.connect(DbConfig(
            backend: DbBackend.LibSql,
            connection_string: ":memory:"
        ))

    @static
    fn for_testing() -> Db | DbError:
        # Use in-memory SQLite for tests
        DbFactory.in_memory()
```

### 10.3 Query Builder Pattern

```simple
# Internal query builder (DB layer uses this)
class QueryBuilder:
    table: str
    columns: [str] = ["*"]
    where_clauses: [(str, DbValue)] = []
    order_by: [(str, Order)]? = None
    limit_val: i32? = None
    offset_val: i32? = None

    fn select(cols: [str]) -> Self:
        self.columns = cols
        self

    fn where(column: str, value: DbValue) -> Self:
        self.where_clauses.push((column, value))
        self

    fn order(column: str, order: Order) -> Self:
        if self.order_by == None:
            self.order_by = []
        self.order_by?.push((column, order))
        self

    fn limit(n: i32) -> Self:
        self.limit_val = Some(n)
        self

    fn offset(n: i32) -> Self:
        self.offset_val = Some(n)
        self

    fn build() -> (str, [DbValue]):
        let sql = f"SELECT {self.columns.join(', ')} FROM {self.table}"
        let params: [DbValue] = []

        if self.where_clauses.len() > 0:
            let conditions = self.where_clauses.map \(col, _):
                params.push(self.where_clauses[_].1)
                f"{col} = ?"
            sql += f" WHERE {conditions.join(' AND ')}"

        if let Some(orders) = self.order_by:
            let order_strs = orders.map \(col, ord):
                f"{col} {ord}"
            sql += f" ORDER BY {order_strs.join(', ')}"

        if let Some(lim) = self.limit_val:
            sql += f" LIMIT {lim}"

        if let Some(off) = self.offset_val:
            sql += f" OFFSET {off}"

        (sql, params)

enum Order:
    Asc
    Desc
```

---

## 11. Error Handling Strategy

### 11.1 Retry Logic

```simple
# Retry configuration
data RetryConfig:
    max_attempts: i32 = 3
    base_delay_ms: i64 = 100
    max_delay_ms: i64 = 5000
    exponential_backoff: bool = true

# Retry wrapper
fn with_retry[T](
    config: RetryConfig,
    f: () -> T | DbError
) -> T | DbError:
    let mut attempt = 0
    let mut delay = config.base_delay_ms

    loop:
        attempt += 1
        match f():
            case Ok(result):
                return Ok(result)
            case Err(e):
                if !e.is_retriable() || attempt >= config.max_attempts:
                    return Err(e)

                sleep_ms(delay)

                if config.exponential_backoff:
                    delay = min(delay * 2, config.max_delay_ms)
```

### 11.2 Error Mapping

```simple
# Map backend-specific errors to DbError
impl DbError:
    @static
    fn from_postgres(e: PostgresError) -> DbError:
        match e.code():
            case "23505": DbError.UniqueViolation(e.column())
            case "23503": DbError.ForeignKeyViolation(e.table(), e.column())
            case "23502": DbError.NotNullViolation(e.column())
            case "23514": DbError.CheckViolation(e.constraint())
            case "40001": DbError.SerializationFailure
            case "40P01": DbError.DeadlockDetected
            case _: DbError.Internal(e.message())

    @static
    fn from_libsql(e: LibSqlError) -> DbError:
        match e.code():
            case 19:  # SQLITE_CONSTRAINT
                if e.message().contains("UNIQUE"):
                    DbError.UniqueViolation(e.extract_column())
                else if e.message().contains("FOREIGN KEY"):
                    DbError.ForeignKeyViolation("", "")
                else:
                    DbError.ConstraintViolation("", e.message())
            case 5:   # SQLITE_BUSY
                DbError.DeadlockDetected
            case _:
                DbError.Internal(e.message())
```

---

## 12. Testing Support

### 12.1 Test Utilities

```simple
# Test database helpers
module db.testing:
    # Create isolated test database
    fn test_db() -> Db:
        DbFactory.in_memory()

    # Create test database with schema
    fn test_db_with_schema(schema: str) -> Db:
        let db = test_db()
        db.execute_ddl(schema)?
        db

    # Transaction rollback wrapper (for test isolation)
    fn with_test_transaction[T](db: Db, f: (DbTransaction) -> T) -> T:
        let tx = db.transaction()?
        let result = f(tx)
        tx.rollback()?  # Always rollback in tests
        result

    # Seed test data
    fn seed(db: Db, table: str, rows: [[DbValue]]) -> ():
        for row in rows:
            let placeholders = row.map(\_: "?").join(", ")
            db.execute(f"INSERT INTO {table} VALUES ({placeholders})", row)?
```

### 12.2 Test Examples

```simple
use db.testing.*

describe "UserRepository":
    let db = test_db_with_schema("
        CREATE TABLE users (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            email TEXT UNIQUE
        )
    ")

    it "finds user by id":
        seed(db, "users", [[1, "Alice", "alice@test.com"]])

        let repo = UserRepository(db)
        let user = repo.find_by_id(1)?

        expect(user?.name).to_equal("Alice")

    it "saves new user":
        let repo = UserRepository(db)
        let user = User(name: "Bob", email: "bob@test.com")

        let saved = repo.save(user)?

        expect(saved.id).to_be_greater_than(0)
```

---

## 13. Performance Considerations

### 13.1 Prepared Statement Caching

```simple
# Statement cache (per connection)
class StatementCache:
    cache: Dict[str, DbStatement]
    max_size: i32 = 100

    fn get_or_prepare(db: Db, sql: str) -> DbStatement | DbError:
        if let Some(stmt) = self.cache.get(sql):
            return Ok(stmt)

        let stmt = db.prepare(sql)?

        if self.cache.len() >= self.max_size:
            # LRU eviction
            self.evict_oldest()

        self.cache.set(sql, stmt)
        Ok(stmt)
```

### 13.2 Batch Operations

```simple
impl Db:
    # Batch insert (single transaction)
    fn batch_insert(
        table: str,
        columns: [str],
        rows: [[DbValue]]
    ) -> DbResult | DbError:
        let tx = self.transaction()?

        let placeholders = columns.map(\_: "?").join(", ")
        let sql = f"INSERT INTO {table} ({columns.join(', ')}) VALUES ({placeholders})"
        let stmt = tx.prepare(sql)?

        let mut total = 0
        for row in rows:
            let result = stmt.execute(row)?
            total += result.rows_affected

        tx.commit()?
        Ok(DbResult(rows_affected: total, last_insert_id: None))

    # Batch execute with different statements
    fn batch_execute(statements: [(str, [DbValue])]) -> [DbResult] | DbError:
        let tx = self.transaction()?
        let results: [DbResult] = []

        for (sql, params) in statements:
            let result = tx.execute(sql, params)?
            results.push(result)

        tx.commit()?
        Ok(results)
```

---

## 14. Configuration Reference

### 14.1 Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `DATABASE_URL` | Connection string | `file:./data/app.db` |
| `DB_BACKEND` | Backend type (`postgres`, `libsql`) | `libsql` |
| `DB_POOL_MIN` | Minimum pool connections | `1` |
| `DB_POOL_MAX` | Maximum pool connections | `10` |
| `DB_TIMEOUT_MS` | Connection timeout | `5000` |
| `DB_SSL_MODE` | PostgreSQL SSL mode | `prefer` |

### 14.2 Simple.toml Configuration

```toml
[database]
backend = "libsql"  # or "postgres"
url = "file:./data/app.db"

[database.pool]
min = 1
max = 10
idle_timeout_ms = 300000

[database.postgres]
ssl_mode = "require"
application_name = "my-app"

[database.libsql]
wal_mode = true
foreign_keys = true
```

---

## 15. Future Considerations

### 15.1 Potential Additions

- **Read Replicas**: Automatic read/write splitting
- **Sharding**: Horizontal partitioning support
- **Query Logging**: Structured query logging with timing
- **Metrics**: Connection pool and query metrics
- **Schema Versioning**: Built-in migration versioning

### 15.2 Backend Candidates

- **DuckDB**: Analytics/OLAP workloads
- **ClickHouse**: Time-series data
- **CockroachDB**: Distributed PostgreSQL

---

## References

- [libSQL Documentation](https://libsql.org/docs)
- [Turso (libSQL Cloud)](https://turso.tech/docs)
- [PostgreSQL Documentation](https://www.postgresql.org/docs/)
- [SQLite Documentation](https://sqlite.org/docs.html)
- [SQP Specification](./sqp.md)
