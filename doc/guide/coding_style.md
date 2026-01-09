# Simple Language Coding Style Guide

**Purpose:** Standardized coding conventions for Simple language projects.

---

## File Organization

### Line Limits
- **Max 800 lines per file** - Split larger files into modules
- If file exceeds 800 lines, refactor into:
  - `module/__init__.spl` - exports and module docs
  - `module/types.spl` - type definitions
  - `module/impl.spl` - implementations
  - `module/utils.spl` - helper functions

### Module Structure
```simple
# module/__init__.spl
mod my_module

# Core types first
export use types.*

# Configuration
export use config.*

# Implementations
export use impl.*
```

---

## Public Interfaces

### No Primitives in Public APIs

**Bad:**
```simple
fn create_user(name: String, age: Int, active: Bool) -> User
fn set_timeout(ms: Int)
fn process(data: List[u8])
```

**Good:**
```simple
fn create_user(name: UserName, age: Age, status: UserStatus) -> User
fn set_timeout(timeout: Duration)
fn process(data: Payload)
```

### Domain Type Wrappers
```simple
# Define meaningful domain types
struct UserId:
    value: u64

struct Email:
    value: String

    fn new(value: String) -> Result[Email, ValidationError]:
        if not value.contains("@"):
            Err(ValidationError.invalid_email(value))
        else:
            Ok(Email { value })

struct Temperature:
    celsius: f64

    fn from_fahrenheit(f: f64) -> Temperature:
        Temperature { celsius: (f - 32) * 5 / 9 }
```

### Exceptions
Primitives allowed in:
- Internal helper functions (private)
- Performance-critical hot paths (with `@inline`)
- Interop/FFI boundaries

---

## Defaults Everywhere

### Constructor Pattern
```simple
struct ServerConfig:
    host: String
    port: u16
    timeout: Duration
    max_connections: u32
    tls_enabled: Bool

    # Default constructor required
    fn new() -> ServerConfig:
        ServerConfig {
            host: "localhost",
            port: 8080,
            timeout: Duration.seconds(30),
            max_connections: 100,
            tls_enabled: false
        }

    # Builder pattern for customization
    fn with_host(mut self, host: String) -> ServerConfig:
        self.host = host
        self

    fn with_port(mut self, port: u16) -> ServerConfig:
        self.port = port
        self
```

### Usage
```simple
# Use defaults
config = ServerConfig.new()

# Customize with builder
config = ServerConfig.new()
    .with_host("0.0.0.0")
    .with_port(443)
    .with_tls(true)
```

---

## Configuration Patterns

### 1. `__init__.spl` Module Config
```simple
# myapp/__init__.spl
mod myapp

# Module-level configuration
let _config: Option[AppConfig] = None

fn configure(config: AppConfig):
    _config = Some(config)

fn get_config() -> AppConfig:
    _config.unwrap_or(AppConfig.new())

export use core.*
export use services.*
```

### 2. Application Config (main.spl)
```simple
# main.spl
import myapp.{configure, AppConfig}
import std.env

fn main():
    # Load from environment
    config = AppConfig.new()
        .with_host(env.get("HOST").unwrap_or("localhost"))
        .with_port(env.get("PORT").map(|p| p.parse_u16()).unwrap_or(8080))

    configure(config)
    run_app()
```

### 3. Hierarchical Config
```simple
# Config hierarchy: Default → File → Env → CLI
struct ConfigLoader:
    fn load() -> AppConfig:
        base = AppConfig.new()                           # Defaults
        from_file = load_config_file("config.toml")      # File
        from_env = load_from_env()                       # Environment
        from_cli = parse_cli_args()                      # CLI args

        base.merge(from_file).merge(from_env).merge(from_cli)
```

### 4. Context-Based Config
```simple
# Per-request or per-scope configuration
struct RequestContext:
    config: RequestConfig
    logger: Logger
    user: Option[User]

fn with_context[T](ctx: RequestContext, f: fn() -> T) -> T:
    _current_context.set(ctx)
    result = f()
    _current_context.clear()
    result
```

---

## Type Inference Rules

### Application Code: Inference Preferred
```simple
# app/handlers/user.spl - inference OK

fn handle_create_user(req: Request) -> Response:
    # Type inference - cleaner app code
    body = req.json()
    name = body.get("name")
    user = UserService.create(name)
    Response.json(user)
```

### Library Code: Explicit Types Required
```simple
# std_lib/src/http/client.spl - explicit types

pub fn get(url: Url, headers: Headers) -> Result[Response, HttpError]:
    conn: Connection = Connection.new(url.host())
    request: Request = Request.get(url).with_headers(headers)
    response: Response = conn.send(request)?
    Ok(response)
```

### Guidelines
| Context | Type Annotations |
|---------|------------------|
| Public function signatures | **Required** |
| Struct/class fields | **Required** |
| Local variables (lib) | **Recommended** |
| Local variables (app) | **Optional** |
| Lambda parameters | **Contextual** |
| Generic constraints | **Required** |

---

## Keyword Omission

### Remove `let` When Unambiguous
```simple
# Omit 'let' for simple assignments
x = 42
name = "Alice"
config = ServerConfig.new()

# Keep 'let' for:
# - Mutable bindings
let mut counter = 0

# - Pattern destructuring
let (first, second) = tuple

# - Explicit type annotation
let value: SomeComplexType = compute()
```

### Remove `return` for Final Expressions
```simple
# Return is implicit for final expression
fn add(a: Int, b: Int) -> Int:
    a + b

fn create_user(name: String) -> User:
    User { name, created_at: now() }

# Keep 'return' for:
# - Early returns
fn validate(input: String) -> Result[Data, Error]:
    if input.is_empty():
        return Err(Error.empty_input())

    Ok(parse(input))

# - Explicit void returns
fn log_and_continue():
    logger.info("Continuing...")
    return  # Explicit early exit
```

### Other Optional Keywords
```simple
# Omit 'self' when unambiguous
impl Counter:
    fn increment():
        count += 1  # Implicit self.count

# Omit parentheses for single-argument calls
print "Hello"
push item

# Omit braces for single-expression blocks
items.map |x| x * 2
users.filter |u| u.active
```

---

## Lean Verification

### When to Use
- **Complex domain logic** - Financial calculations, state machines
- **Safety-critical code** - Memory management, concurrency
- **Algorithm correctness** - Sorting, searching, data structures

### Verification Decorators
```simple
@verify(lean)
@invariant("balance >= 0")
struct BankAccount:
    balance: Money

    @pre("amount > 0")
    @post("balance == old(balance) + amount")
    fn deposit(mut self, amount: Money):
        self.balance += amount

    @pre("amount > 0 and amount <= balance")
    @post("balance == old(balance) - amount")
    fn withdraw(mut self, amount: Money) -> Result[Money, InsufficientFunds]:
        if amount > self.balance:
            Err(InsufficientFunds)
        else:
            self.balance -= amount
            Ok(amount)
```

### Generate Lean Proofs
```bash
./target/debug/simple --gen-lean banking.spl --verify all
```

### Verification Levels
| Level | Use Case |
|-------|----------|
| `types` | Type correctness only |
| `memory` | Borrow checker proofs |
| `effects` | Effect system verification |
| `all` | Full formal verification |

---

## AOP Logging

### Automatic Logging via Aspects
```simple
# Define logging aspect
@aspect
struct LoggingAspect:

    @around("execution(pub fn *(..))")
    fn log_public_calls(jp: JoinPoint) -> Any:
        logger.debug("Entering {jp.signature}")
        start = now()

        result = jp.proceed()

        elapsed = now() - start
        logger.debug("Exiting {jp.signature} in {elapsed}")
        result

    @after_throwing("execution(fn *(..))")
    fn log_errors(jp: JoinPoint, error: Error):
        logger.error("Error in {jp.signature}: {error}")
```

### Apply to Modules
```simple
# In __init__.spl
@apply_aspect(LoggingAspect)
mod my_service
```

### Logging Levels
```simple
@log(level: "debug")  # Method-level logging
fn process_item(item: Item):
    ...

@log(level: "info", include_args: true)
fn handle_request(req: Request) -> Response:
    ...
```

### Structured Logging
```simple
@log(structured: true)
fn create_order(user_id: UserId, items: List[Item]) -> Order:
    # Automatically logs:
    # { "method": "create_order", "user_id": 123, "items_count": 5 }
    ...
```

---

## Additional Rules

### 1. Error Handling
```simple
# Use Result types, not exceptions
fn parse_config(path: Path) -> Result[Config, ConfigError]:
    content = fs.read(path)?
    parse_toml(content)

# Propagate with ?
fn load_and_validate() -> Result[Data, Error]:
    config = parse_config(path)?
    validate(config)?
    Ok(config.data)
```

### 2. Immutability by Default
```simple
# Immutable by default
user = User.new("Alice")

# Explicit mutability
let mut counter = 0
counter += 1
```

### 3. Prefer Composition
```simple
# Prefer traits over inheritance
trait Renderable:
    fn render(self) -> String

trait Saveable:
    fn save(self) -> Result[(), Error]

struct Document:
    impl Renderable, Saveable
```

### 4. Naming Conventions
| Item | Convention | Example |
|------|------------|---------|
| Types | PascalCase | `UserAccount` |
| Functions | snake_case | `get_user` |
| Constants | SCREAMING_CASE | `MAX_RETRIES` |
| Modules | snake_case | `user_service` |
| Private | `_` prefix | `_internal_state` |

### 5. Documentation
```simple
## Public API documentation (required for lib)
# Short description on first line.
#
# Longer description if needed.
#
# @param name - User's display name
# @returns Created user instance
# @throws ValidationError - If name is empty
fn create_user(name: UserName) -> Result[User, ValidationError]:
    ...
```

### 6. Test Organization
```simple
# test/unit/service_spec.spl
describe "UserService":
    context "create_user":
        it "creates user with valid name":
            user = UserService.create(UserName.new("Alice"))
            expect(user.name).to_eq("Alice")

        it "rejects empty name":
            result = UserService.create(UserName.new(""))
            expect(result).to_be_err()
```

---

## Quick Reference

| Rule | App Code | Lib Code |
|------|----------|----------|
| Type annotations | Optional | Required |
| `let` keyword | Omit if unambiguous | Keep for clarity |
| `return` keyword | Omit final expression | Omit final expression |
| Domain types | Recommended | Required |
| Defaults | Required | Required |
| Lean verification | Complex logic | Safety-critical |
| AOP logging | @log decorator | @aspect patterns |
| Max file lines | 800 | 800 |

---

## Related Documentation

- [coding.md](../../.claude/skills/coding.md) - Additional coding rules
- [test.md](test.md) - Testing conventions
- [module_system.md](module_system.md) - Module organization
- [doc/spec/types.md](../spec/types.md) - Type system specification
