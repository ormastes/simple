# Database Access - Part 2: Patterns & Implementation

**Part of:** [Database Access Guide](./db_part1.md)

---

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
