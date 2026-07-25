# Application Writing Guide

How to build Simple applications: project structure, lifecycle, and DI.

---

## Project Structure

```
my_app/
├── __init__.spl       # Module manifest
├── main.spl           # Entry point
├── config.spl         # Configuration
├── services.spl       # Service registry (DI wiring)
├── domain/            # Domain types
└── test/              # Tests
```

## Entry Point & Lifecycle

```simple
fn main():
    init()
    start_server(services.app_config)

fn init():
    # Register/wire services (lazy — not created yet)
    pass_do_nothing

fn reset():
    # Tear down state — used in tests only
    pass_do_nothing
```

| Function | Purpose | Called by |
|----------|---------|-----------|
| `main()` | Entry; calls `init()` then starts work | Runtime |
| `init()` | Wire DI; register services (lazy) | `main()` or test setup |
| `reset()` | Re-init state for test isolation | `before_each` / `after_each` |

---

## Dependency Injection

### Manual Composition

```simple
fn main():
    val db = Database(config: DatabaseConfig(url: env_var("DB_URL"), pool_size: 10))
    val user_svc = UserService(db: db)
    run(user_svc)
```

### Service Registry

```simple
# services.spl
val app_config = load_config()
val db = Database(DatabaseConfig(url: app_config.db_url, pool_size: app_config.db_pool_size))
val user_service = UserService(repo: UserRepository(db: db), log: ConsoleLogger(level: app_config.log_level))
```

### Lazy Init (Proposed)

```simple
lazy val db = Database(DatabaseConfig(url: app_config.db_url, pool_size: app_config.db_pool_size))
# Created on first access; subsequent accesses return cached value
```

### Test Override

```simple
before_each:
    services.db = MockDatabase()
after_each:
    services.reset()   # clear lazy vals back to uninitialized
```

---

## Application Types

### CLI

```simple
fn main():
    cmd = Command.new("myapp")
        .flag(Flag.new("verbose").short("v"))
        .arg(Arg.new("input").required())
    args = cmd.parse()
    process(args.get("input"))
```

### Web

```simple
router = Router.new()
    .get("/") \req: Response.html("<h1>Hello!</h1>")
    .post("/api/users") \req:
        user = req.json[CreateUser]()
        Response.json(UserService.create(user)).status(201)

fn main():
    Server.new(router).listen(8080)
```

### Database

```simple
fn main():
    db = Database.connect("postgres://localhost/myapp")
    migrate(db, "migrations/")
    users = db.query("SELECT * FROM users WHERE active = $1", [true])
        .map(User.from_row).collect()
```

### Configuration

```simple
fn load_config() -> AppConfig:
    ConfigLoader.new()
        .with_defaults(AppConfig.new())
        .with_file("config.toml")
        .with_env_prefix("APP_")
        .with_cli_args()
        .load()
```

---

## See Also

- [design_writing.md](design_writing.md) - Design with diagrams
- [architecture_writing.md](architecture_writing.md) - Architecture patterns
- [../coding_style.md](../coding_style.md) - Coding conventions
- [../test/spipe_writing.md](../test/spipe_writing.md) - Test writing
