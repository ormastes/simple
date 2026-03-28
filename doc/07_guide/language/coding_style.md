# Simple Language Coding Style Guide

This guide covers coding conventions, naming rules, and common mistakes to avoid.

---

## File Organization

### Line Limits

- **Max 800 lines per file** -- split larger files into modules
- Refactor large files into:
  - `module/__init__.spl` -- exports and module docs
  - `module/types.spl` -- type definitions
  - `module/impl.spl` -- implementations
  - `module/utils.spl` -- helper functions

### Import Organization

Group imports by source, with standard library first:

```simple
use std.spec.{describe, it, expect}
use std.math.{sin, cos}

use app.io.{file_read, file_write}
use app.cli.dispatch.{find_command}
```

---

## Naming Conventions

| Item | Convention | Example |
|------|------------|---------|
| Types, Structs, Enums | PascalCase | `UserAccount`, `HttpClient` |
| Functions, Methods | snake_case | `get_user`, `parse_config` |
| Constants | SCREAMING_CASE | `MAX_RETRIES`, `DEFAULT_PORT` |
| Modules | snake_case | `user_service`, `http_client` |
| Private items | `_` prefix | `_internal_state` |
| Variables | snake_case | `user_count`, `total_score` |

---

## Variables and Immutability

Prefer immutable bindings by default:

```simple
val x = 5                            # Immutable (preferred)
var counter = 0                      # Mutable (only when needed)
```

Use `val` unless mutation is genuinely required.

---

## Type Annotations

### Application Code: Inference Preferred

```simple
fn handle_request(req: Request) -> Response:
    val body = req.json()             # Type inferred
    val user = UserService.create(body.get("name"))
    Response.json(user)
```

### Library Code: Explicit Types Required

```simple
pub fn get(url: Url, headers: Headers) -> Result<Response, HttpError>:
    val conn: Connection = Connection.new(url.host())
    val request: Request = Request.get(url).with_headers(headers)
    val response: Response = conn.send(request)?
    Ok(response)
```

### Guidelines Summary

| Context | Type Annotations |
|---------|------------------|
| Public function signatures | Required |
| Struct/class fields | Required |
| Generic constraints | Required |
| Local variables (library code) | Recommended |
| Local variables (application code) | Optional |

---

## Public API Design

### Use Domain Types in Public APIs

```simple
# Avoid bare primitives in public interfaces
fn create_user(name: UserName, age: Age, status: UserStatus) -> User
fn set_timeout(timeout: Duration)

# Primitives acceptable in:
# - Internal helper functions (private)
# - Performance-critical hot paths
# - FFI boundaries
```

### Provide Defaults

```simple
struct ServerConfig:
    host: text
    port: i64
    timeout: i64

impl ServerConfig:
    fn default() -> ServerConfig:
        return ServerConfig(
            host: "localhost",
            port: 8080,
            timeout: 30
        )

    me with_host(host: text) -> ServerConfig:
        self.host = host
        return self
```

---

## Functions and Methods

### Implicit Return

The last expression in a function is its return value:

```simple
fn add(a: i64, b: i64) -> i64:
    a + b                             # Implicit return

fn create_user(name: text) -> User:
    User(name: name, created_at: now())
```

Use explicit `return` only for early exits:

```simple
fn validate(input: text) -> Result<Data, Error>:
    if input.is_empty():
        return Err(Error.empty_input())
    Ok(parse(input))
```

### Method Self Parameter

In methods, `self` is implicit. Do not write it as a parameter:

```simple
impl Point:
    fn get_x() -> i64:
        return self.x                 # self is available implicitly

    me set_x(new_x: i64):            # 'me' for mutable methods
        self.x = new_x
```

### Omit Return Type for Void

```simple
fn log_message(msg: text):            # No return type = void
    print msg
```

---

## Error Handling Style

Use `Result` types and `?` propagation, not exceptions:

```simple
fn parse_config(path: text) -> Result<Config, ConfigError>:
    val content = file_read(path)?
    parse_toml(content)
```

---

## Documentation

### Docstrings

All public APIs should include documentation with examples:

```simple
## Calculate the factorial of a non-negative integer.
#
# ## Examples
#
# >>> factorial(0)
# 1
# >>> factorial(5)
# 120
#
# @param n - Non-negative integer
# @returns n! (n factorial)
fn factorial(n: i64) -> i64:
    if n <= 1: 1
    else: n * factorial(n - 1)
```

### Test Organization

```simple
describe "UserService":
    context "create_user":
        it "creates user with valid name":
            val user = UserService.create(UserName.new("Alice"))
            expect(user.name).to_equal("Alice")

        it "rejects empty name":
            val result = UserService.create(UserName.new(""))
            expect(result).to_be_err()
```

---

## Composition Over Inheritance

Simple does not support class inheritance (`class Child(Parent)` is not allowed). Use traits, composition, or mixins:

```simple
trait Renderable:
    fn render() -> text

trait Saveable:
    fn save() -> Result<(), Error>

struct Document:
    content: text

impl Renderable for Document:
    fn render() -> text: self.content

impl Saveable for Document:
    fn save() -> Result<(), Error>:
        file_write("doc.txt", self.content)
```

---

## Common Mistakes by Source Language

### Python Developers

| Mistake | Correct |
|---------|---------|
| `def foo():` | `fn foo():` |
| `None` | `nil` |
| `True` / `False` | `true` / `false` |
| `self.x` in method body | `self.x` works, but `self` parameter is implicit |
| `class Child(Parent)` | Not supported; use traits |

### Rust Developers

| Mistake | Correct |
|---------|---------|
| `let mut x` | `var x` |
| `fn foo(&mut self)` | `me foo()` |
| `Type::new()` | `Type.new()` (dot, not `::`) |
| `::<T>` turbofish | `<T>` directly |
| Lifetime annotations | Not needed; use reference capabilities |

### Java/C++ Developers

| Mistake | Correct |
|---------|---------|
| `public class Foo` | `pub struct Foo:` or `pub class Foo:` |
| `void foo()` | `fn foo():` (omit return type) |
| `new Point(1, 2)` | `Point(1, 2)` |
| `this.x` | `self.x` (implicit self) |
| `template<T>` | `struct Name<T>:` |
| `namespace foo` | `mod foo:` |

### TypeScript/JavaScript Developers

| Mistake | Correct |
|---------|---------|
| `function foo()` | `fn foo():` |
| `const x = 5` | `val x = 5` |
| `let x = 5` | `val x = 5` (immutable) or `var x = 5` (mutable) |
| `interface Named` | `trait Named:` |
| `(a, b) => a + b` | `\a, b: a + b` or `fn(a, b): a + b` |

### General Syntax Mistakes

| Mistake | Correct |
|---------|---------|
| `List[T]` | `List<T>` (angle brackets for generics) |
| `fn foo(self)` | `fn foo()` (self is implicit) |
| `fn foo() -> ()` | `fn foo():` (omit void return type) |
| Missing `:` before body | `fn foo():` and `if x > 0:` need colons |
| Semicolons at line ends | Not needed (only for multiple statements on one line) |

---

## Tips for Success

1. **Embrace immutability**: Use `val` by default, `var` only when mutation is needed.

2. **Trust type inference**: Specify types only when needed for clarity or disambiguation.

3. **Remember implicit self**: In methods, do not write `self` as a parameter.

4. **Use `<>` for generics**: `List<T>` not `List[T]`.

5. **Colons matter**: Function and block definitions need `:` before the body.

6. **Use `fn` for functions**: Not `def`, `function`, or any other keyword.

7. **Use `nil` for null**: Not `None`, `null`, or `undefined`.

8. **Use `val`/`var` for variables**: Not `let`, `const`, or type-first declarations.

9. **No inheritance**: Use composition, traits, or mixins.

10. **Use `Result`/`Option`**: Not try/catch for error handling.
