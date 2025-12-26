# Simple Language Metaprogramming

This document covers macros, DSL features, decorators, attributes, comprehensions, and context managers.

## Macros

Macro specification has moved to `doc/spec/macro.md` (contract-first, parser-friendly macros).

---

## DSL Features

Simple is designed to build internal Domain-Specific Languages (DSLs). Two key features enable DSL creation: context blocks and `method_missing`.

### Context Blocks

A context block changes the method lookup context for a section of code:

```simple
class HTMLBuilder:
    fn tag(name: String, content: String):
        print "<{name}>{content}</{name}>"

    fn method_missing(meth: Symbol, args: [Any], block: Fn):
        let tag_name = meth.name
        if block != nil:
            print "<{tag_name}>"
            block()
            print "</{tag_name}>"
        else:
            let content = args.size > 0 ? args[0] : ""
            print "<{tag_name}>{content}</{tag_name}>"

let html = HTMLBuilder()
context html:
    tag("h1", "Welcome")
    p "This is a DSL example."
    div:
        p "Inside a div."
        span "Nice!"
```

Inside `context html:`, calls like `p "..."` are looked up on the `html` object.

### Method Missing

If an object receives a call for a method it doesn't have, it can override `method_missing`:

```simple
class ConfigDSL:
    data: Map[String, String] = {}

    fn method_missing(key: Symbol, args: [Any], block: Fn):
        if args.size == 1:
            data[key.name] = toString(args[0])
        elif args.size == 0 and block != nil:
            block()

let config = ConfigDSL()
context config:
    database "postgres"
    host "localhost"
    port 5432
```

### DSL Support Summary

| Feature | Purpose |
|---------|---------|
| No-parentheses calls | Cleaner DSL syntax |
| Named arguments | Keyword-like parameters |
| Blocks as lambdas | Tree-like DSL instructions |
| Context / implicit receiver | No repeated DSL object references |
| Fluent interfaces | Method chaining |

---

## Decorators and Attributes

### Decorators

Decorators are functions that transform other functions at compile time:

```simple
@cached
fn expensive_calculation(x: i64) -> i64:
    return result

@logged
@retry(attempts: 3)
fn fetch_data(url: str) -> Data:
    return http_get(url)

@timeout(seconds: 30)
fn slow_operation():
    # ...
```

Decorators are applied bottom-up. Common built-in decorators:

| Decorator | Purpose |
|-----------|---------|
| `@cached` | Memoize function results |
| `@logged` | Log function calls |
| `@deprecated(message)` | Mark as deprecated |
| `@async_handler` | Convert to async handler |

### Attributes

Attributes are passive metadata:

```simple
#[inline]
fn hot_path(x: i64) -> i64:
    return x * 2

#[deprecated(since: "0.2", reason: "Use new_api instead")]
fn old_api():
    # ...

#[derive(Debug, Clone, Eq)]
struct Point:
    x: f64
    y: f64

#[test]
fn test_addition():
    assert_eq(1 + 1, 2)
```

Common attributes:

| Attribute | Purpose |
|-----------|---------|
| `#[inline]` | Inlining hints |
| `#[deprecated(...)]` | Deprecation warning |
| `#[derive(...)]` | Auto-generate trait implementations |
| `#[test]` | Mark as test function |
| `#[cfg(...)]` | Conditional compilation |
| `#[allow(...)]` / `#[deny(...)]` | Lint control |

### Lint Control Attributes

The `#[allow(...)]` and `#[deny(...)]` attributes control compiler lint behavior:

```simple
# Directory-level (in __init__.spl, inherits to all children)
#[deny(primitive_api)]
mod my_strict_module

# Item-level
#[allow(primitive_api)]
pub fn low_level_function(x: i64) -> i64:   # No warning
    ...

#[deny(primitive_api)]
pub fn strict_function(x: i64) -> i64:      # Error
    ...
```

Lint attributes placed in `__init__.spl` propagate to all files and subdirectories.

Common lints:

| Lint | Default | Description |
|------|---------|-------------|
| `primitive_api` | warn | Bare primitives in public APIs |
| `bare_bool` | warn | Bool parameters (prefer enums) |
| `unused_variable` | warn | Unused variables |
| `dead_code` | warn | Unreachable code |

**Note:** Implicit `nil` (nullable without `Option[T]`) is always an error and cannot be suppressed with lint attributes.

### Decorators vs Attributes

| Aspect | Decorator (`@`) | Attribute (`#[...]`) |
|--------|-----------------|---------------------|
| Behavior | Active - transforms code | Passive - attaches metadata |
| Execution | Compile-time function call | Compiler directive |
| User-defined | Yes, any function | Limited to compiler-known |

---

## Comprehensions

Simple supports Python-style comprehensions for concise collection construction.

### List Comprehension

```simple
# Basic
let squares = [x * x for x in 0..10]

# With filter
let evens = [x for x in 0..20 if x % 2 == 0]

# Nested
let pairs = [(x, y) for x in 0..3 for y in 0..3]

# Complex
let names = [user.name.upper() for user in users if user.active]
```

### Dict Comprehension

```simple
let squares = {x: x * x for x in 0..10}
let active_users = {u.id: u for u in users if u.active}
let inverted = {v: k for k, v in original}
```

---

## Slicing and Indexing

### Negative Indexing

```simple
let items = [1, 2, 3, 4, 5]
items[-1]     # 5 (last element)
items[-2]     # 4 (second to last)
```

### Slicing

```simple
let items = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

items[2:5]      # [2, 3, 4]
items[:3]       # [0, 1, 2]
items[7:]       # [7, 8, 9]
items[::2]      # [0, 2, 4, 6, 8]
items[::-1]     # [9, 8, ..., 0] (reversed)
items[-3:]      # [7, 8, 9] (last 3)
```

### Tuple Unpacking

```simple
let a, b = (1, 2)
a, b = b, a           # Swap

let first, *rest = [1, 2, 3, 4, 5]
# first = 1, rest = [2, 3, 4, 5]
```

### Spread Operators

```simple
let a = [1, 2, 3]
let b = [4, 5, 6]
let combined = [*a, *b]        # [1, 2, 3, 4, 5, 6]

let d1 = {"a": 1}
let d2 = {"b": 2}
let merged = {**d1, **d2}      # {"a": 1, "b": 2}
```

---

## Enhanced Pattern Matching

### Match Guards

```simple
match value:
    case x if x > 0:
        print "positive"
    case x if x < 0:
        print "negative"
    case 0:
        print "zero"
```

### Or Patterns

```simple
match command:
    case "quit" | "exit" | "q":
        shutdown()
    case "help" | "h" | "?":
        show_help()
```

### Range Patterns

```simple
match score:
    case 90..100: "A"
    case 80..90: "B"
    case 70..80: "C"
    case _: "F"
```

### If Let / While Let

```simple
if let Some(value) = optional:
    print "got {value}"

while let Some(item) = iterator.next():
    process(item)
```

### While With (Context Manager Loop)

The `while with` construct combines a `while` loop condition with a context manager, useful for render loops, streaming, and resource-managed iterations:

```simple
# Render loop: continues while window is open, frame context managed per iteration
while with window.frame() as frame:
    frame.clear([0.0, 0.0, 0.0, 1.0])
    frame.draw(pipeline, vertices)
# Window closed, loop exits

# Streaming: continues while data available
while with stream.next_chunk() as chunk:
    process(chunk)
# Stream exhausted
```

**Semantics:**

1. The expression (`window.frame()`) is evaluated
2. If it returns `None`/`nil`/falsy, the loop exits
3. Otherwise, `enter()` is called (context manager protocol)
4. The loop body executes with the bound variable (`frame`)
5. `exit()` is called (ensures cleanup even on error)
6. Loop repeats from step 1

**Grammar:**
```
while_with_stmt = 'while' 'with' expression 'as' IDENT ':' block
```

**Comparison with nested `while`/`with`:**

```simple
# Traditional nested approach
while !window.should_close():
    with window.frame() as frame:
        frame.draw(...)

# Unified while-with approach (condition implied by context manager)
while with window.frame() as frame:
    frame.draw(...)
```

The `while with` form is preferred when:
- The context manager itself determines loop continuation
- Resource acquisition and loop condition are coupled
- Cleaner, single-level indentation is desired

**Implementation Note:** The context manager must implement `ContextManager` trait and optionally return a falsy value to signal termination.

### Chained Comparisons

```simple
if 0 < x < 10:
    print "single digit"
```

---

## Context Managers

Context managers ensure proper resource cleanup:

```simple
with open("file.txt") as file:
    let content = file.read()
# file is automatically closed

with open("in.txt") as input, open("out.txt", "w") as output:
    output.write(transform(input.read()))
```

### Implementing Context Managers

```simple
trait ContextManager:
    fn enter(self) -> Self
    fn exit(self, error: Error?)

impl ContextManager for File:
    fn enter(self) -> File:
        return self

    fn exit(self, error: Error?):
        self.close()
```

---

## Move Closures

By default, closures capture variables by reference. Use `move` to capture by value:

```simple
fn create_counter(start: i64) -> Fn() -> i64:
    let count = start
    return move \:
        count = count + 1
        count

let counter = create_counter(0)
counter()  # 1
counter()  # 2
```

Move closures are essential for:
- Sending closures to other actors
- Storing closures that outlive their creation scope
- Parallel execution with isolated state

```simple
actor.send(move \: process(captured_data))
items.par_map(move \x: expensive_compute(x, config))
```

---

## Error Handling

Simple uses explicit error handling with Result types and the `?` operator.

### Result Type

```simple
enum Result[T, E]:
    Ok(value: T)
    Err(error: E)

fn divide(a: i64, b: i64) -> Result[i64, str]:
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)
```

### The `?` Operator

```simple
fn process_file(path: str) -> Result[Data, Error]:
    let file = open(path)?           # Returns Err if open fails
    let content = file.read_all()?   # Returns Err if read fails
    let data = parse(content)?       # Returns Err if parse fails
    return Ok(data)
```

Works with:
- `Result[T, E]` - propagates `Err`
- `T?` (Option) - propagates `None`

---

## Related Specifications

- [Syntax](syntax.md)
- [Functions](functions.md)
- [Traits](traits.md)
