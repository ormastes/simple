# Simple Language Error Handling

This guide covers error handling with `Result<T, E>`, `Option<T>`, the `?` operator, and the compiler's error recovery system.

---

## Result and Option Types

Simple uses `Result<T, E>` for operations that can fail and `Option<T>` for values that may be absent. There are no `try`/`catch`/`throw` keywords -- this is by design.

### Result

```simple
enum Result<T, E>:
    Ok(T)
    Err(E)

fn divide(a: i64, b: i64) -> Result<i64, text>:
    if b == 0:
        return Err("division by zero")
    Ok(a / b)
```

### Option

```simple
enum Option<T>:
    Some(T)

fn find_user(id: i64) -> Option<User>:
    if id == 0:
        return nil
    Some(lookup(id))
```

---

## The ? Operator

The `?` operator propagates errors up the call stack. If the value is `Err` or `nil`, it returns early from the current function:

```simple
fn load_config(path: text) -> Result<Config, text>:
    val content = file_read(path)?            # Returns Err if file_read fails
    val parsed = parse_toml(content)?         # Returns Err if parsing fails
    Ok(parsed)

fn load_and_validate() -> Result<Data, Error>:
    val config = parse_config(path)?
    val data = validate(config)?
    Ok(data)
```

The `?` operator only works inside functions that return `Result` or `Option`.

---

## Pattern Matching on Errors

Handle errors explicitly with `match`:

```simple
match divide(10, 0):
    Ok(value): print "Result: {value}"
    Err(msg): print "Error: {msg}"

match find_user(42):
    Some(user): process(user)
    nil: print "User not found"
```

---

## Optional Chaining

Use `?.` for safe navigation through potentially nil values, and `??` for providing defaults:

```simple
val name = user?.profile?.name        # Option<text>
val display = name ?? "Anonymous"     # text, with fallback

if user.?:
    process(user)
```

---

## Error Design Patterns

### Custom Error Types

```simple
enum ConfigError:
    FileNotFound(text)
    ParseError(text)
    ValidationError(text)

fn parse_config(path: text) -> Result<Config, ConfigError>:
    if not file_exists(path):
        return Err(ConfigError.FileNotFound(path))
    val content = file_read(path)
    match parse_toml(content):
        Ok(config): Ok(config)
        Err(msg): Err(ConfigError.ParseError(msg))
```

### Validated Construction

Return `Option` or `Result` from constructors that can fail:

```simple
struct Age:
    value: i64

impl Age:
    fn new(value: i64) -> Option<Age>:
        if value >= 0 and value <= 150:
            return Some(Age(value))
        nil

struct Email:
    value: text

impl Email:
    fn new(value: text) -> Result<Email, text>:
        if not value.contains("@"):
            return Err("invalid email: {value}")
        Ok(Email(value: value))
```

### Chaining with ? and map

```simple
fn process_user_email(id: i64) -> Result<text, Error>:
    val user = find_user(id)?
    val email = user.email?
    val validated = Email.new(email)?
    Ok(validated.value)
```

---

## Error Recovery (Compiler)

The Simple compiler detects common syntax mistakes from other languages and provides helpful suggestions during parsing.

### How It Works

When the parser encounters a token that looks like a mistake from another language, it emits a contextual hint with:
- The error severity (Error, Warning, Info, Hint)
- A suggested fix
- Side-by-side examples showing the wrong and correct syntax

### Common Detected Mistakes

| From | Wrong | Correct | Severity |
|------|-------|---------|----------|
| Python | `def foo():` | `fn foo():` | Error |
| Python | `None` | `nil` | Error |
| Python | `True`/`False` | `true`/`false` | Error |
| Rust | `let mut x` | `var x` | Error |
| Rust | `::<T>` | `<T>` | Hint |
| Java | `public class` | `pub struct` | Error |
| Java | `void foo()` | `fn foo():` | Error |
| Java | `new Type()` | `Type(...)` | Error |
| TypeScript | `function foo()` | `fn foo():` | Error |
| TypeScript | `const x` | `val x` | Error |
| TypeScript | `interface I` | `trait I:` | Error |
| Any | `Type[T]` | `Type<T>` | Warning |

### Example Output

```
error: Common mistake detected: Replace 'def' with 'fn'
  --> line 1:1
   |
 1 | def calculate(x):
   | ^

Suggestion: Replace 'def' with 'fn'

Help:
Use 'fn' to define functions in Simple, not 'def'.

Python:  def add(a, b):
Simple:  fn add(a, b):
```

---

## Best Practices

1. **Use Result for operations that can fail** -- file I/O, parsing, network calls
2. **Use Option for values that may be absent** -- lookups, search results
3. **Propagate with ?** instead of matching at every level
4. **Create domain-specific error types** for libraries and complex modules
5. **Handle errors at the appropriate level** -- propagate low, handle high
6. **Use validated constructors** (`fn new() -> Result<T, E>`) to prevent invalid state
7. **Prefer `??` for defaults** over matching on `Option` when you just need a fallback value
8. **Use `nil` in user code** -- `None` may appear in parser diagnostics or compatibility notes, but it is not the canonical public syntax
