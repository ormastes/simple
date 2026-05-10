# Database Abstraction Layer (DB)

**Version:** 2025-12
**Status:** Implementation
**Features:** #700-#706

---

## Overview

The DB layer provides a unified interface for database operations across multiple backends. It abstracts away driver-specific details while providing high-performance access to:

- **libSQL** (SQLite-compatible, local and remote)
- **PostgreSQL** (via native protocol)

```
┌─────────────────────────────────────────────────────────────┐
│                    SQP Layer (Query DSL)                     │
│   (Data Models, Relations, Migrations, Query Builder)        │
├─────────────────────────────────────────────────────────────┤
│                    DB Layer (This Document)                  │
│   (Unified Interface - Backend Agnostic)                     │
├─────────────────────┬───────────────────────────────────────┤
│   libSQL Driver     │     PostgreSQL Driver                 │
│   (local + Turso)   │     (tokio-postgres)                  │
└─────────────────────┴───────────────────────────────────────┘
```

---

## Feature Summary

| ID | Feature | Status | Description |
|----|---------|--------|-------------|
| #700 | PostgreSQL driver | 📋 | Native PostgreSQL protocol |
| #701 | libSQL driver | 📋 | SQLite-compatible (libsql crate) |
| #702 | libSQL Remote (Turso) | 📋 | Turso edge database support |
| #703 | Connection pooling | 📋 | Pool management and health checks |
| #704 | Transaction API | 📋 | BEGIN/COMMIT/ROLLBACK with savepoints |
| #705 | Type mapping | 📋 | Simple types ↔ SQL types |
| #706 | Schema introspection | 📋 | Runtime schema discovery |

---

## Crate Structure

```
src/db/
├── Cargo.toml
├── src/
│   ├── lib.rs              # Re-exports and traits
│   ├── connection.rs       # Connection trait and types
│   ├── pool.rs             # Connection pooling
│   ├── transaction.rs      # Transaction management
│   ├── types.rs            # Type mapping
│   ├── error.rs            # Error types
│   ├── row.rs              # Row abstraction
│   ├── drivers/
│   │   ├── mod.rs
│   │   ├── libsql.rs       # libSQL driver
│   │   └── postgres.rs     # PostgreSQL driver
│   └── ffi.rs              # FFI for Simple language
└── tests/
    ├── libsql_tests.rs
    ├── postgres_tests.rs
    └── pool_tests.rs
```

---

## Core Traits

### Connection Trait

```rust
/// Database connection trait - implemented by all drivers
pub trait Connection: Send + Sync {
    /// Execute a query that returns rows
    fn query(&self, sql: &str, params: &[Value]) -> Result<Rows>;

    /// Execute a query that doesn't return rows (INSERT, UPDATE, DELETE)
    fn execute(&self, sql: &str, params: &[Value]) -> Result<u64>;

    /// Begin a transaction
    fn begin(&self) -> Result<Transaction>;

    /// Prepare a statement for repeated execution
    fn prepare(&self, sql: &str) -> Result<Statement>;

    /// Check if connection is alive
    fn ping(&self) -> Result<()>;

    /// Close the connection
    fn close(self) -> Result<()>;
}

/// Transaction with commit/rollback
pub trait Transaction: Connection {
    /// Commit the transaction
    fn commit(self) -> Result<()>;

    /// Rollback the transaction
    fn rollback(self) -> Result<()>;

    /// Create a savepoint
    fn savepoint(&self, name: &str) -> Result<Savepoint>;
}

/// Prepared statement for efficient repeated queries
pub trait Statement: Send + Sync {
    /// Execute with parameters
    fn execute(&self, params: &[Value]) -> Result<u64>;

    /// Query with parameters
    fn query(&self, params: &[Value]) -> Result<Rows>;
}
```

### Row Abstraction

```rust
/// A row from a query result
pub trait Row {
    /// Get value by column index
    fn get<T: FromSql>(&self, index: usize) -> Result<T>;

    /// Get value by column name
    fn get_by_name<T: FromSql>(&self, name: &str) -> Result<T>;

    /// Get nullable value
    fn get_opt<T: FromSql>(&self, index: usize) -> Result<Option<T>>;

    /// Number of columns
    fn len(&self) -> usize;

    /// Column names
    fn columns(&self) -> &[String];
}

/// Iterator over rows
pub struct Rows {
    inner: Box<dyn Iterator<Item = Result<Box<dyn Row>>> + Send>,
    columns: Vec<String>,
}
```

---

## Type Mapping (#705)

### Simple ↔ SQL Type Correspondence

| Simple Type | SQLite/libSQL | PostgreSQL |
|-------------|---------------|------------|
| `i64` | INTEGER | BIGINT |
| `i32` | INTEGER | INTEGER |
| `f64` | REAL | DOUBLE PRECISION |
| `f32` | REAL | REAL |
| `bool` | INTEGER (0/1) | BOOLEAN |
| `str` | TEXT | TEXT / VARCHAR |
| `[u8]` | BLOB | BYTEA |
| `Option[T]` | NULL or T | NULL or T |
| `DateTime` | TEXT (ISO8601) | TIMESTAMP |
| `Date` | TEXT (YYYY-MM-DD) | DATE |
| `Uuid` | TEXT / BLOB | UUID |
| `Json` | TEXT | JSONB |

### Rust Traits

```rust
/// Convert from SQL value to Rust type
pub trait FromSql: Sized {
    fn from_sql(value: &SqlValue) -> Result<Self>;
}

/// Convert from Rust type to SQL value
pub trait ToSql {
    fn to_sql(&self) -> SqlValue;
}

/// SQL value enum
#[derive(Debug, Clone)]
pub enum SqlValue {
    Null,
    Integer(i64),
    Real(f64),
    Text(String),
    Blob(Vec<u8>),
}
```

---

## Connection Pooling (#703)

### Pool Configuration

```rust
/// Connection pool configuration
#[derive(Debug, Clone)]
pub struct PoolConfig {
    /// Minimum connections to keep open
    pub min_connections: u32,
    /// Maximum connections allowed
    pub max_connections: u32,
    /// Connection timeout (acquire from pool)
    pub acquire_timeout: Duration,
    /// Idle timeout before closing connection
    pub idle_timeout: Duration,
    /// Max lifetime of a connection
    pub max_lifetime: Duration,
    /// Health check interval
    pub health_check_interval: Duration,
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self {
            min_connections: 1,
            max_connections: 10,
            acquire_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(600),
            max_lifetime: Duration::from_secs(1800),
            health_check_interval: Duration::from_secs(30),
        }
    }
}

/// Connection pool
pub struct Pool {
    driver: DriverType,
    config: PoolConfig,
    connections: Arc<Mutex<VecDeque<PooledConnection>>>,
    available: Semaphore,
}

impl Pool {
    /// Create a new connection pool
    pub fn new(url: &str, config: PoolConfig) -> Result<Self>;

    /// Acquire a connection from the pool
    pub fn acquire(&self) -> Result<PooledConnection>;

    /// Get pool statistics
    pub fn stats(&self) -> PoolStats;

    /// Close all connections
    pub fn close(&self) -> Result<()>;
}
```

---

## Transaction API (#704)

### Transaction Usage

```rust
/// Transaction with automatic rollback on drop
pub struct Transaction<'a> {
    conn: &'a dyn Connection,
    committed: bool,
}

impl<'a> Transaction<'a> {
    /// Commit the transaction
    pub fn commit(mut self) -> Result<()> {
        self.conn.execute("COMMIT", &[])?;
        self.committed = true;
        Ok(())
    }

    /// Rollback the transaction
    pub fn rollback(mut self) -> Result<()> {
        self.conn.execute("ROLLBACK", &[])?;
        self.committed = true;  // Prevent double rollback
        Ok(())
    }

    /// Create a savepoint
    pub fn savepoint(&self, name: &str) -> Result<Savepoint> {
        self.conn.execute(&format!("SAVEPOINT {}", name), &[])?;
        Ok(Savepoint { name: name.to_string(), conn: self.conn })
    }
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        if !self.committed {
            // Auto-rollback on drop if not committed
            let _ = self.conn.execute("ROLLBACK", &[]);
        }
    }
}

/// Savepoint within a transaction
pub struct Savepoint<'a> {
    name: String,
    conn: &'a dyn Connection,
}

impl Savepoint<'_> {
    pub fn release(self) -> Result<()> {
        self.conn.execute(&format!("RELEASE SAVEPOINT {}", self.name), &[])
    }

    pub fn rollback(self) -> Result<()> {
        self.conn.execute(&format!("ROLLBACK TO SAVEPOINT {}", self.name), &[])
    }
}
```

---

## Driver Implementations

### libSQL Driver (#701, #702)

```rust
use libsql::{Database, Connection as LibsqlConn};

/// libSQL driver supporting local and remote (Turso)
pub struct LibsqlDriver {
    db: Database,
}

impl LibsqlDriver {
    /// Connect to local SQLite file
    pub fn open_local(path: &str) -> Result<Self> {
        let db = Database::open(path)?;
        Ok(Self { db })
    }

    /// Connect to in-memory database
    pub fn open_memory() -> Result<Self> {
        let db = Database::open(":memory:")?;
        Ok(Self { db })
    }

    /// Connect to Turso (remote libSQL)
    pub fn open_remote(url: &str, auth_token: &str) -> Result<Self> {
        let db = Database::open_remote(url, auth_token)?;
        Ok(Self { db })
    }

    /// Connect with embedded replica (local cache + remote sync)
    pub fn open_replica(path: &str, url: &str, auth_token: &str) -> Result<Self> {
        let db = Database::open_with_remote_sync(path, url, auth_token)?;
        Ok(Self { db })
    }
}

impl Connection for LibsqlDriver {
    fn query(&self, sql: &str, params: &[Value]) -> Result<Rows> {
        let conn = self.db.connect()?;
        let stmt = conn.prepare(sql)?;
        let rows = stmt.query(params)?;
        Ok(Rows::from_libsql(rows))
    }

    fn execute(&self, sql: &str, params: &[Value]) -> Result<u64> {
        let conn = self.db.connect()?;
        Ok(conn.execute(sql, params)?)
    }

    fn begin(&self) -> Result<Transaction> {
        self.execute("BEGIN", &[])?;
        Ok(Transaction::new(self))
    }

    fn ping(&self) -> Result<()> {
        self.execute("SELECT 1", &[])?;
        Ok(())
    }

    fn close(self) -> Result<()> {
        Ok(())
    }
}
```

### PostgreSQL Driver (#700)

```rust
use tokio_postgres::{Client, NoTls};

/// PostgreSQL driver
pub struct PostgresDriver {
    client: Client,
}

impl PostgresDriver {
    /// Connect to PostgreSQL
    pub async fn connect(url: &str) -> Result<Self> {
        let (client, connection) = tokio_postgres::connect(url, NoTls).await?;

        // Spawn connection handler
        tokio::spawn(async move {
            if let Err(e) = connection.await {
                tracing::error!("PostgreSQL connection error: {}", e);
            }
        });

        Ok(Self { client })
    }
}

impl Connection for PostgresDriver {
    fn query(&self, sql: &str, params: &[Value]) -> Result<Rows> {
        let pg_params = params.iter().map(to_pg_param).collect::<Vec<_>>();
        let rows = self.client.query(sql, &pg_params)?;
        Ok(Rows::from_postgres(rows))
    }

    fn execute(&self, sql: &str, params: &[Value]) -> Result<u64> {
        let pg_params = params.iter().map(to_pg_param).collect::<Vec<_>>();
        Ok(self.client.execute(sql, &pg_params)?)
    }

    fn begin(&self) -> Result<Transaction> {
        self.execute("BEGIN", &[])?;
        Ok(Transaction::new(self))
    }

    fn ping(&self) -> Result<()> {
        self.execute("SELECT 1", &[])?;
        Ok(())
    }

    fn close(self) -> Result<()> {
        Ok(())
    }
}
```

---

## FFI Interface for Simple

### FFI Functions

```rust
// Connection management
#[no_mangle]
pub extern "C" fn rt_db_open_libsql(path_ptr: i64, path_len: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_open_turso(url_ptr: i64, url_len: i64,
                                    token_ptr: i64, token_len: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_open_postgres(url_ptr: i64, url_len: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_close(conn: i64) -> i64;

// Query execution
#[no_mangle]
pub extern "C" fn rt_db_execute(conn: i64, sql_ptr: i64, sql_len: i64,
                                 params: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_query(conn: i64, sql_ptr: i64, sql_len: i64,
                               params: i64) -> i64;

// Row access
#[no_mangle]
pub extern "C" fn rt_db_row_next(rows: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_row_get_int(row: i64, col: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_row_get_float(row: i64, col: i64) -> f64;

#[no_mangle]
pub extern "C" fn rt_db_row_get_str(row: i64, col: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_row_get_bool(row: i64, col: i64) -> i64;

// Transactions
#[no_mangle]
pub extern "C" fn rt_db_begin(conn: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_commit(tx: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_rollback(tx: i64) -> i64;

// Pool management
#[no_mangle]
pub extern "C" fn rt_db_pool_create(url_ptr: i64, url_len: i64,
                                     min_conn: i64, max_conn: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_pool_acquire(pool: i64) -> i64;

#[no_mangle]
pub extern "C" fn rt_db_pool_release(pool: i64, conn: i64) -> i64;
```

---

## Simple Language API

### Connection

```simple
use db.*

# Local SQLite/libSQL
let conn = Db.open("./data.db")

# In-memory database
let mem_db = Db.open(":memory:")

# Turso (remote libSQL)
let turso = Db.open_turso(
    url: "libsql://your-db.turso.io",
    token: env("TURSO_TOKEN")
)

# PostgreSQL
let pg = Db.open_postgres("postgres://user:pass@localhost/db")
```

### Queries

```simple
# Execute (returns affected rows)
let count = conn.execute(
    "INSERT INTO users (name, email) VALUES (?, ?)",
    ["Alice", "alice@example.com"]
)

# Query (returns rows)
let rows = conn.query("SELECT * FROM users WHERE active = ?", [true])
for row in rows:
    let id = row.get_int(0)
    let name = row.get_str("name")
    print(f"{id}: {name}")

# Single row
let user = conn.query_one("SELECT * FROM users WHERE id = ?", [42])
```

### Transactions

```simple
# Transaction with auto-rollback on error
conn.transaction(|tx|
    tx.execute("UPDATE accounts SET balance = balance - ? WHERE id = ?", [100, 1])
    tx.execute("UPDATE accounts SET balance = balance + ? WHERE id = ?", [100, 2])
    # Auto-commits if no exception
)

# Manual transaction control
let tx = conn.begin()
try:
    tx.execute("INSERT INTO logs (msg) VALUES (?)", ["Starting"])
    tx.execute("UPDATE counters SET value = value + 1")
    tx.commit()
except e:
    tx.rollback()
    raise e
```

### Connection Pool

```simple
# Create pool
let pool = Db.pool(
    url: "./data.db",
    min_connections: 2,
    max_connections: 10
)

# Acquire and use
pool.with_connection(|conn|
    conn.query("SELECT * FROM users")
)

# Or manual acquire/release
let conn = pool.acquire()
try:
    conn.execute("UPDATE ...", [])
finally:
    pool.release(conn)
```

---

## Error Handling

```rust
#[derive(Debug)]
pub enum DbError {
    /// Connection failed
    ConnectionFailed(String),
    /// Query execution failed
    QueryFailed(String),
    /// Type conversion failed
    TypeMismatch { expected: String, got: String },
    /// Transaction error
    TransactionFailed(String),
    /// Pool exhausted
    PoolExhausted,
    /// Connection closed
    ConnectionClosed,
    /// Timeout
    Timeout,
    /// Driver-specific error
    Driver(Box<dyn std::error::Error + Send + Sync>),
}
```

---

## Dependencies

```toml
[dependencies]
# libSQL (SQLite-compatible)
libsql = "0.6"

# PostgreSQL
tokio-postgres = "0.7"

# Connection pooling utilities
parking_lot = "0.12"

# Async runtime (for PostgreSQL)
tokio = { version = "1", features = ["rt-multi-thread", "sync"] }
```

---

## Related Documents

- [sqp.md](sqp.md) - Simple Query and Persistence (Query DSL)
- [feature.md](feature.md) - Feature tracking
- [spec/stdlib.md](../spec/stdlib.md) - Standard library spec
