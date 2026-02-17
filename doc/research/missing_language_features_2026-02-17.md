# Missing Language Features Research
**Date:** 2026-02-17
**Scope:** Useful language features absent from Simple, compared to Rust, Python, Ruby, Erlang, Zig, TypeScript, Go, Kotlin, Swift, Haskell, Julia
**Excluded (by design):** Exceptions/try-catch, class inheritance, introspection/reflection

---

## Executive Summary

Simple has a solid foundation: generics, pattern matching, traits, Option/Result, async/await, closures, comprehensions, pipeline operators, effect annotations, and a rich standard library. This document catalogs **useful practical features** missing from Simple that exist in peer languages, organized by impact and implementation complexity.

---

## 1. String Formatting Specifiers

**Missing:** Format specifiers inside string interpolation.

**Present in:** Python (`f"{value:.2f}"`), Rust (`"{:.2f}"`), C# (`$"{value:N2}"`), Swift (`String(format:)`), JavaScript (`toFixed(2)`)

**Problem:** Simple's interpolation only does basic `{expr}` substitution. No alignment, width, precision, radix, or padding.

```simple
# Current (verbose workaround needed)
val s = float_to_str_prec(value, 2)     # No native way
print "Result: {s}"

# What other languages offer
print f"Result: {value:.2f}"            # Python
println!("Result: {:.2f}", value)       # Rust
```

**Useful for:** Number formatting, table alignment, debug output, reports.

**Proposed syntax:**
```simple
print "Result: {value:.2f}"             # float, 2 decimal places
print "Name: {name:>20}"                # right-align in 20-char field
print "Hex: {byte:08x}"                 # hex, zero-padded to 8 chars
print "Int: {count:,}"                  # thousands separator
```

**Impact:** HIGH. Affects everyday output and debug code.

---

## 2. Labeled Breaks and Continues

**Missing:** Named loop labels to break out of specific outer loops.

**Present in:** Rust (`'label: loop { break 'label; }`), Java (`outer: for`), Kotlin, Go, Perl

**Problem:** Nested loops require awkward flags or early returns to escape multiple levels.

```simple
# Current workaround (ugly):
var done = false
for row in rows:
    for col in row:
        if found(col):
            done = true
            break
    if done:
        break

# What Rust has:
'outer: for row in rows:
    for col in row:
        if found(col):
            break 'outer
```

**Proposed syntax:**
```simple
outer: for row in rows:
    for col in row:
        if found(col):
            break outer
        if skip(col):
            continue outer
```

**Impact:** MEDIUM. Comes up frequently in nested iteration, parsing, graph traversal.

---

## 3. `errdefer` — Error-Conditional Cleanup

**Missing:** Deferred cleanup that only runs on error paths (not normal exit).

**Present in:** Zig (`errdefer`), some Go patterns with `defer` + named return values

**Problem:** Simple has `defer` (always runs). But sometimes you only want cleanup if an error occurs — e.g., release a resource if allocation fails later.

```zig
// Zig:
var list = ArrayList(i32).init(allocator);
errdefer list.deinit();  // only runs if we return an error
try list.append(1);
try list.append(2);
return list;  // no deinit here — caller owns it
```

```simple
# Proposed:
fn build_collection() -> Result<[i64], text>:
    val list = list_create()
    errdefer list_free(list)       # only on error
    result = list_append(list, 1)?
    result = list_append(list, 2)?
    Ok(list)                       # errdefer does NOT run
```

**Impact:** MEDIUM. Important for correct resource management in fallible code.

---

## 4. Struct Update / Spread Syntax

**Missing:** Create a new struct based on another with some fields changed.

**Present in:** Rust (`Point { x: 5, ..other }`), JavaScript (`{...obj, name: "new"}`), Elm, OCaml, F#

**Problem:** To create a modified copy of a struct, you must repeat all unchanged fields.

```simple
# Current (verbose):
val new_point = Point(x: p.x + 1, y: p.y, z: p.z, label: p.label)

# Proposed (struct update syntax):
val new_point = Point(..p, x: p.x + 1)   # copy p, override x
```

**Proposed syntax:**
```simple
val updated = User(..original_user, name: "Bob", age: 31)
val moved = Point(..p, x: p.x + dx, y: p.y + dy)
```

**Impact:** HIGH. Immutable-first design makes this critical — every struct modification requires full reconstruction.

---

## 5. Derive / Auto-Implementation

**Missing:** Auto-generating trait implementations for standard capabilities.

**Present in:** Rust (`#[derive(Debug, Clone, PartialEq, Hash)]`), Haskell (`deriving (Show, Eq, Ord)`), Kotlin (`data class`), Swift (`Codable`)

**Problem:** Common behaviors like equality, copying, printing, hashing, and serialization must be hand-implemented for every type.

```simple
# Current: must manually implement for each struct
struct Point:
    x: i64
    y: i64

fn point_equal(a: Point, b: Point) -> bool:
    a.x == b.x and a.y == b.y

# Proposed:
@derive(Eq, Clone, Hash, Display)
struct Point:
    x: i64
    y: i64
```

**Capabilities to derive:**
- `Eq` / `PartialEq` — structural equality via `==`
- `Clone` / `Copy` — explicit copy semantics
- `Hash` — for use as dict/set keys
- `Display` / `Debug` — human-readable string representation
- `Ord` / `PartialOrd` — comparison ordering
- `Default` — zero/empty value construction
- `Serialize` / `Deserialize` — JSON, SDN, binary

**Impact:** HIGH. Reduces boilerplate dramatically. Every non-trivial project needs at least `Eq` and `Display`.

---

## 6. Extension Methods

**Missing:** Adding methods to existing types without modifying their source.

**Present in:** Kotlin (`fun String.isPalindrome()`), Swift (`extension String`), C# (`static class Extensions`), Ruby (open classes), TypeScript (interface merging)

**Problem:** Cannot add methods to `text`, `[T]`, or library types without modifying the stdlib.

```kotlin
// Kotlin:
fun String.isPalindrome(): Boolean = this == this.reversed()
fun List<Int>.sum(): Int = this.reduce(0) { acc, x -> acc + x }
```

```simple
# Proposed:
extend text:
    fn is_palindrome() -> bool:
        self == self.reverse()

extend [i64]:
    fn sum() -> i64:
        self.reduce(0, \acc, x: acc + x)

# Usage:
"racecar".is_palindrome()  # true
[1, 2, 3].sum()             # 6
```

**Impact:** HIGH. Enables domain-specific APIs, keeps code readable (`items.to_csv()` vs `csv_from(items)`), avoids utility function sprawl.

---

## 7. Union Types (Type-Level OR)

**Missing:** A type that can be one of several types at the type-system level.

**Present in:** TypeScript (`string | number | boolean`), Python (`Union[str, int]` / `str | int`), Haskell (sum types), Ceylon

**Problem:** Simple has `enum` for tagged unions but no lightweight untagged union type notation for function signatures.

```typescript
// TypeScript:
type ID = string | number
fn lookup(id: string | number): User { ... }

// Python 3.10+:
def process(val: int | str | None) -> str: ...
```

```simple
# Proposed:
type ID = text | i64
fn lookup(id: text | i64) -> Option<User>:
    match id:
        text s: find_by_name(s)
        i64 n: find_by_id(n)
```

**Note:** Different from `enum` — union types require no wrapper, useful for ad-hoc polymorphism at call sites.

**Impact:** MEDIUM. Useful for interop, JSON-like data, public APIs that accept multiple representations.

---

## 8. Default Method Implementations in Traits

**Missing:** Providing default bodies for trait methods so implementations only need to override non-default ones.

**Present in:** Rust (default method bodies in `trait`), Java 8+ (`default`), Swift (`extension Protocol`), Kotlin (`interface`)

**Problem:** Every trait method must be implemented by every implementing type, even boilerplate ones.

```rust
// Rust:
trait Display {
    fn fmt(&self) -> String;
    fn print(&self) {
        println!("{}", self.fmt());  // default impl
    }
}
```

```simple
# Proposed:
trait Display:
    fn to_string() -> text       # required — no default

    fn print():                   # default implementation
        print self.to_string()

    fn println():                 # another default
        print "{self.to_string()}\n"

# Implementer only needs to_string():
impl Display for Point:
    fn to_string() -> text:
        "({self.x}, {self.y})"
```

**Impact:** HIGH. Without this, traits are limited to pure interfaces. Reduces the boilerplate explosion from every trait method needing impl in every type.

---

## 9. Associated Types in Traits

**Missing:** Type members defined within a trait, bound per implementation.

**Present in:** Rust (`type Item`), Swift (`associatedtype`), Haskell (type families), Scala

**Problem:** Generic traits with a type parameter (`Iterator<T>`) pollute type signatures everywhere. Associated types let the concrete type pick the associated type once.

```rust
// Rust:
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

impl Iterator for Counter {
    type Item = i32;
    fn next(&mut self) -> Option<i32> { ... }
}
```

```simple
# Proposed:
trait Iterator:
    type Item
    fn next() -> Option<Self.Item>

impl Iterator for Counter:
    type Item = i64
    fn next() -> Option<i64>:
        ...

# Usage: clean — no <T> pollution in calling code
fn sum_iter(it: Iterator) -> i64:
    var total: i64 = 0
    while it.next()?.? as v:
        total = total + v
    total
```

**Impact:** HIGH. Currently generics and trait bounds interact verbosely. Associated types reduce noise significantly for collection-like APIs.

---

## 10. Atom / Symbol Type

**Missing:** A lightweight, intern-pooled string that compares by identity, not content.

**Present in:** Ruby (`:symbol`), Erlang/Elixir (atoms), Lisp (symbols), Clojure (keywords), JavaScript (Symbol)

**Problem:** Using `text` for categorical values (statuses, event names, mode flags) is both wasteful (heap strings) and error-prone (typos are undetected).

```ruby
# Ruby:
status = :pending
status == :pending   # fast identity comparison
```

```erlang
% Erlang:
State = running,
case State of
  running -> io:format("still going~n");
  stopped -> io:format("done~n")
end
```

```simple
# Proposed: atom literal with backtick or colon prefix
val status = `pending
val mode = `reading

match status:
    `pending: start_processing()
    `done: cleanup()
    `error: handle_failure()

# Type: atom
fn set_status(s: atom): ...
```

**Benefit:** Compile-time checked names, fast O(1) comparison, no heap allocation, readable in pattern matching, good for event systems and state machines.

**Impact:** MEDIUM. Particularly valuable in actor systems, state machines, and protocol implementations.

---

## 11. Compile-Time Evaluation (`comptime` / `const fn`)

**Missing:** Evaluating expressions and functions at compile time.

**Present in:** Zig (`comptime`), Rust (`const fn`), C++ (`constexpr`), D (`enum` constants), Nim (`when`/`static`)

**Problem:** No way to compute constants, array sizes, or type-dependent values at compile time.

```zig
// Zig comptime:
fn fibonacci(n: comptime_int) comptime_int {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}
const fib10 = fibonacci(10);  // computed at compile time
```

```rust
// Rust const fn:
const fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}
const BUFFER_SIZE: usize = max(256, 512);
```

```simple
# Proposed:
const fn fibonacci(n: i64) -> i64:
    if n <= 1: n
    else: fibonacci(n - 1) + fibonacci(n - 2)

const FIB_10 = fibonacci(10)    # evaluated at compile time

# Or Zig-style:
comptime val LOOKUP_TABLE = build_table(256)
```

**Impact:** MEDIUM. Important for embedded systems, performance tuning, and avoiding magic numbers.

---

## 12. Newtype / Opaque Type Wrapper

**Missing:** Zero-cost type wrapper that creates a distinct type from an existing one.

**Present in:** Rust (`struct Meters(f64)`), Haskell (`newtype`), Kotlin (value classes), Swift, TypeScript (branded types)

**Problem:** Using primitive types for domain values (ids, measures, money) loses type safety — a `user_id` and `product_id` are both `i64` and can be accidentally swapped.

```rust
// Rust:
struct UserId(i64);
struct ProductId(i64);

fn find_user(id: UserId) -> Option<User> { ... }
// find_user(product_id)  // compile error!
```

```simple
# Proposed (zero-cost at runtime):
newtype UserId = i64
newtype ProductId = i64
newtype Meters = f64
newtype Milliseconds = i64

fn find_user(id: UserId) -> Option<User>: ...
fn find_product(id: ProductId) -> Option<Product>: ...

val uid = UserId(42)
val pid = ProductId(42)
# find_user(pid)   # ERROR: type mismatch UserId != ProductId
# uid + pid        # ERROR: can't mix newtypes
```

**Impact:** HIGH. Prevents entire classes of subtle bugs (unit confusion, ID mix-ups). Zero runtime overhead.

---

## 13. Exhaustiveness Checking in `match`

**Missing:** Compile-time verification that `match` covers all enum variants.

**Present in:** Rust (compiler error for non-exhaustive match), Haskell (warnings), TypeScript (discriminated unions), OCaml, Elm (hard error)

**Problem:** Simple has `match` but may not enforce that all enum variants are handled. Missing a case silently falls through or panics.

```rust
// Rust: compile error if variant missing
enum Direction { North, South, East, West }
match direction {
    Direction::North => ...,
    Direction::South => ...,
    // ERROR: patterns East and West not covered
}
```

```simple
# Proposed: compile-time exhaustiveness check
enum Status:
    Pending
    Running
    Done
    Failed(msg: text)

match status:
    Pending: start()
    Running: check()
    Done: finish()
    # COMPILE ERROR: Failed(msg) not handled
```

**Also useful:** `@non_exhaustive` annotation to explicitly allow partial matches (for forward-compatible APIs where new variants may be added).

**Impact:** HIGH. This is a core safety feature for enum-heavy code. Catches logic bugs at compile time.

---

## 14. `or_else` / Error Chaining (Result Ergonomics)

**Missing:** Ergonomic Result/Option chaining methods like Rust's `?` operator with error context, and chained transforms.

**Present in:** Rust (`?`, `.map_err()`, `.context()`, `.unwrap_or_else()`), Haskell (monadic bind), Swift (`try`, `map`, `flatMap`), Kotlin (`.let { }`)

**Problem:** Handling Result/Option chains is verbose without chaining methods.

```rust
// Rust:
fn read_config(path: &str) -> Result<Config, Error> {
    let text = fs::read_to_string(path)
        .map_err(|e| Error::Io(e))?;
    let config = parse_config(&text)
        .map_err(|e| Error::Parse(e))?;
    Ok(config)
}
```

```simple
# Proposed — Result chaining methods:
fn read_config(path: text) -> Result<Config, text>:
    val text = file_read(path).map_err(\e: "IO: {e}")?
    val config = parse_config(text).map_err(\e: "Parse: {e}")?
    Ok(config)

# Proposed chaining API:
result
    .map(\v: v * 2)                    # transform success
    .map_err(\e: "context: {e}")       # transform error
    .and_then(\v: validate(v))         # chain fallible
    .or_else(\e: use_default(e))       # fallback on error
    .unwrap_or(default_value)          # extract with default
    .unwrap_or_else(\e: compute(e))    # computed default
```

**Missing methods also for Option:**
```simple
option
    .map(\v: transform(v))
    .filter(\v: v > 0)
    .flat_map(\v: might_fail(v))
    .or_else(\: try_alternative())
    .zip(other_option)
    .unzip()
```

**Impact:** HIGH. `Result` and `Option` are the primary error handling mechanism — making them pleasant to work with is essential.

---

## 15. Tail Call Optimization (TCO) Guarantee

**Missing:** Language-level guarantee that tail recursive calls don't grow the stack.

**Present in:** Erlang (mandatory TCO), Haskell (lazy), Scheme (R5RS standard), Lua (guaranteed), Kotlin (`tailrec` keyword)

**Problem:** Recursive algorithms (parsers, tree traversals, state machines) risk stack overflow without TCO. Without a guarantee, developers can't safely use recursion for unbounded iteration.

```erlang
% Erlang: loop runs forever without stack growth
loop(State) ->
    NewState = process(State),
    loop(NewState).   % tail call — no stack growth
```

```kotlin
// Kotlin: explicit opt-in
tailrec fun factorial(n: Long, acc: Long = 1): Long =
    if (n == 1L) acc else factorial(n - 1, n * acc)
```

```simple
# Proposed: annotation or keyword
@tailrec
fn factorial(n: i64, acc: i64 = 1) -> i64:
    if n <= 1: acc
    else: factorial(n - 1, n * acc)   # compiler verifies this is tail position
```

**Impact:** MEDIUM. Especially important for functional-style programming with recursion instead of mutation.

---

## 16. Process Supervision Trees (Erlang OTP-style)

**Missing:** Structured fault recovery — supervisors that restart failed processes.

**Present in:** Erlang/OTP (`supervisor`, `gen_server`), Elixir (`Supervisor`), Akka (Scala/Java)

**Problem:** Simple has actors but no standard way to build fault-tolerant systems with automatic restart strategies.

```erlang
% Erlang supervisor:
-module(my_supervisor).
-behaviour(supervisor).

init([]) ->
    {ok, {{one_for_one, 5, 10},
          [{worker, my_worker, permanent, brutal_kill, worker, [my_worker]}]}}.
```

```simple
# Proposed:
supervisor MyApp:
    strategy: one_for_one       # restart only failed child
    max_restarts: 5
    max_seconds: 10

    child WorkerA:
        module: worker_a
        restart: permanent
        shutdown: brutal_kill

    child WorkerB:
        module: worker_b
        restart: transient      # only restart on abnormal exit
```

**Impact:** MEDIUM. Critical for building reliable server applications. Erlang's "let it crash" philosophy requires supervision trees.

---

## 17. Pattern Refinements

### 17a. Or-Patterns (Multi-case matching)

**Missing:** Matching multiple patterns in one arm.

**Present in:** Rust (`A | B | C`), Python (`case A | B`), Haskell, OCaml, Swift

```simple
# Proposed:
match status:
    Pending | Waiting: queue()
    Running | Processing: continue_work()
    Done | Succeeded: finish()
    Failed | Error: handle_failure()
```

**Note:** The current workaround `case X, Y:` is noted as non-working — `case X | Y:` is required.

### 17b. Binding in Patterns (`@` bind)

**Missing:** Binding a name to a value while also matching a pattern (already partially in match but may need improvement).

**Present in:** Rust (`name @ pattern`), Haskell (`as@pattern`), ML family

```simple
# Proposed:
match value:
    large @ (x if x > 1000): handle_large(large)  # bind AND guard
    n @ (10 | 20 | 30): handle_special(n)
```

### 17c. Negative / Guard Patterns

**Missing:** Matching when a sub-pattern does NOT match.

**Present in:** Rust (via guards `if !condition`), Elixir (guards), Haskell (patterns + guards)

```simple
# Proposed:
match event:
    click if not inside_modal(click.pos): handle_click(click)
    key if key.code not in reserved_keys: handle_key(key)
```

**Impact:** MEDIUM. Reduces boilerplate in complex matching. Or-patterns especially reduce redundant arms.

---

## 18. Module System Improvements

### 18a. Module Aliasing in `use`

**Missing:** Renaming an import to avoid collision or for brevity.

**Present in:** Python (`import numpy as np`), Rust (`use module as alias`), JavaScript (`import * as alias from`)

```simple
# Currently broken: use mod.{name as alias} fails
# Proposed:
use std.encoding.json as json
use std.collections.hashmap as HashMap
use very.long.module.name as short
```

### 18b. Re-export with Rename

**Missing:** Exporting an import under a different name from a module.

**Present in:** TypeScript (`export { foo as bar } from './module'`), Rust (`pub use`), JavaScript

```simple
# Proposed:
export use std.json.{parse as parse_json, encode as to_json}
pub use internal.{InternalType as PublicType}
```

### 18c. Namespace / Package Hierarchy

**Missing:** Explicit package declarations that aren't just directory structure.

**Present in:** Java (explicit `package com.example`), Go (`package main`), Python (explicit `__init__.py` with re-exports), Kotlin, Rust (`mod` tree)

**Impact:** MEDIUM. As projects grow, having explicit namespace control (not just implicit directory structure) improves maintenance.

---

## 19. `const` and Compile-Time Constants

**Missing:** A first-class `const` declaration distinct from `val` — computed once, guaranteed at compile time, usable as type arguments.

**Present in:** Rust (`const MAX: usize = 1024`), C++ (`constexpr`), Zig (`const`), TypeScript (`const enum`)

**Problem:** `val` is runtime-immutable. A compile-time constant differs: it can be used as array size, generic parameter, match discriminant, etc.

```simple
# Proposed:
const MAX_BUFFER: i64 = 4096
const VERSION: text = "1.0.0"
const PI: f64 = 3.14159265358979

# Usable as type-level value:
val buffer: [u8; MAX_BUFFER] = []        # fixed-size array
match response.version:
    VERSION: handle_current()
    _: handle_legacy()
```

**Impact:** MEDIUM. Important for embedded, performance-sensitive code, and public APIs that expose versioned constants.

---

## 20. String Multi-line Templates (Fix Triple-Quoted Strings)

**Missing (broken):** Multi-line string literals. Triple-quoted strings (`"""..."""`) are documented as broken in the runtime.

**Present in:** Python (`"""..."""`), JavaScript (template literals), Kotlin (raw strings), Ruby (`<<~HEREDOC`), Rust (`r#"..."#`)

```simple
# Proposed (raw heredoc style):
val sql = ~"""
    SELECT *
    FROM users
    WHERE age > 18
    ORDER BY name
    """

val html = ~"""
    <html>
        <body>{content}</body>
    </html>
    """

# Alternative: indentation-stripping multiline
val json = multiline:
    {
        "name": "{name}",
        "age": {age}
    }
```

**Impact:** HIGH. Multi-line strings are essential for SQL, HTML, JSON templates, error messages, and documentation examples. Current workaround (string concatenation) is extremely verbose.

---

## 21. Scoped `let` Expressions / Scope Functions

**Missing:** Evaluating a block as an expression with a locally scoped result.

**Present in:** Kotlin (`run`, `let`, `apply`, `also`, `with`), Swift (`{ ... }()`), Haskell (`let...in`), JavaScript (IIFE), Rust (block expressions)

**Problem:** Complex initialization logic must be broken into multiple statements or extracted into helper functions.

```kotlin
// Kotlin:
val result = run {
    val temp = expensive_computation()
    transform(temp)  // result of block
}

user?.let { u ->
    log("Processing {u.name}")
    process(u)
}
```

```simple
# Proposed: block as expression
val result = do:
    val temp = expensive_computation()
    transform(temp)                       # implicit return

# Also useful for null-safe chains:
val processed = user?.let \u:
    log("Processing {u.name}")
    process(u)
```

**Impact:** MEDIUM. Reduces function proliferation for short initialization blocks. Natural extension of Simple's expression-oriented design.

---

## 22. `where` Clauses for Generic Constraints

**Missing:** Separating generic type constraints from the function/type signature for readability.

**Present in:** Rust (`where T: Display + Clone`), Swift (`where Element: Comparable`), Haskell, C# (`where T : IComparable`)

**Problem:** Complex generic constraints inline in `<>` become unreadable.

```rust
// Rust: where clause
fn largest<T>(list: &[T]) -> T
where
    T: PartialOrd + Copy,
{ ... }
```

```simple
# Current (if generics support constraints):
fn largest<T: Ord + Clone>(list: [T]) -> T:
    ...

# Proposed where clause (cleaner for complex constraints):
fn process<T, E>(data: T, handler: E) -> Result<text, text>
    where T: Display + Serialize,
          E: EventHandler + Clone:
    ...
```

**Impact:** LOW-MEDIUM. Purely ergonomic. Becomes important when multiple bounded type parameters are involved.

---

## 23. Lazy / One-Time Initialization

**Missing:** A value that is computed once on first access and cached.

**Present in:** Rust (`once_cell`, `lazy_static`), Kotlin (`by lazy`), Swift (`lazy var`), Java (`double-checked locking`)

**Problem:** Module-level initialization often needs FFI calls or expensive computation that should only run once.

```kotlin
// Kotlin:
val config: Config by lazy {
    load_config_from_disk()
}
```

```simple
# Proposed:
lazy val config = load_config_from_disk()   # runs once on first access
lazy val lookup_table = build_table(256)

# Alternatively, explicit API:
use std.lazy.{once}
val get_config = once(\: load_config_from_disk())
```

**Impact:** MEDIUM. Currently workaround is manual flag-based initialization or init functions.

---

## 24. Named / Keyword-Only Parameters

**Missing:** Syntax to require callers to use named arguments (prevent positional misuse).

**Present in:** Python (everything after `*` must be keyword-only), Ruby (hash params), Kotlin (named parameters + `required`), Swift (argument labels)

**Problem:** Simple has named arguments but callers can still call positionally. For functions with multiple booleans or similar types, positional calls are bug-prone.

```python
# Python:
def connect(host, *, port, timeout):  # port and timeout MUST be named
    ...
connect("localhost", port=8080, timeout=30)
# connect("localhost", 8080, 30)  # ERROR
```

```simple
# Proposed: mark params as keyword-only with ~
fn connect(host: text, ~port: i64, ~timeout: i64 = 30):
    ...

connect("localhost", port: 8080)              # OK
# connect("localhost", 8080, 30)              # ERROR: port must be named
```

**Impact:** LOW-MEDIUM. Prevents common call-site bugs for functions with many parameters of the same type.

---

## 25. String Builder / Efficient Append

**Missing:** A mutable string accumulator that avoids O(n²) concatenation.

**Present in:** Java (`StringBuilder`), Rust (`String::with_capacity` + `push_str`), Python (`.join()`), Go (`strings.Builder`), C# (`StringBuilder`)

**Problem:** `text = text + more_text` inside a loop creates O(n²) copies.

```simple
# Proposed:
val sb = StringBuilder.new()
for item in items:
    sb.push("{item.name}: {item.value}\n")
val result = sb.to_text()

# Or functional style:
val result = items
    |> map(\item: "{item.name}: {item.value}")
    |> join("\n")
```

**Note:** `join` should be in the stdlib as a list method (currently exists but `join` is a reserved keyword per MEMORY.md — this collision should be resolved).

**Impact:** HIGH. Any code generating text in a loop suffers without this.

---

## 26. Type Classes / Trait Bounds at Call Site

**Missing:** Ability to constrain what operations are available based on trait bounds without full generic declarations.

**Present in:** Haskell (class constraints), Rust (trait objects `dyn Trait` and bounds), TypeScript (conditional types)

**Specifically missing:** `dyn Trait` style trait objects (dynamic dispatch without generics).

```rust
// Rust: trait objects
fn display_all(items: &[Box<dyn Display>]) {
    for item in items { println!("{}", item); }
}
```

```simple
# Proposed:
fn display_all(items: [dyn Display]):
    for item in items:
        print item.to_string()

fn process(handler: dyn EventHandler):
    handler.handle(event)
```

**Impact:** MEDIUM. Currently can't have heterogeneous collections of trait-implementing objects without boxing/enum workarounds.

---

## 27. Numeric Literal Improvements

**Missing:** Separator for readability and explicit type suffixes.

**Present in:** Rust (`1_000_000`, `0xFF_u8`), Python (`1_000_000`), Ruby, Java, C++, Zig, Swift

**Problem:** Large numbers and bit patterns are hard to read.

```simple
# Proposed:
val million = 1_000_000
val hex = 0xFF_A0_B3
val binary = 0b1010_1010
val octal = 0o777

# Type suffixes (if unambiguous):
val byte: u8 = 42u8
val wide: i64 = 100i64
val precise: f64 = 3.14f64
```

**Also missing:** `0b` binary literals — unclear if supported.

**Impact:** LOW-MEDIUM. Ergonomics/readability.

---

## 28. Module-Level `init` and `teardown`

**Missing:** Guaranteed initialization and cleanup hooks for modules.

**Present in:** Go (`func init()`), Python (`__init__.py` module code), Ruby (`at_exit`), Erlang (`application:start`), C (`.init` section)

**Problem:** Currently module-level code runs at load time, but there's no guaranteed teardown. For resource management (connections, file handles) in modules, you need explicit init/cleanup APIs.

```simple
# Proposed:
module database:
    var connection = nil

    init:
        connection = db_connect(config.host)

    teardown:
        if connection != nil:
            db_close(connection)

    fn query(sql: text) -> [Row]:
        db_execute(connection, sql)
```

**Impact:** LOW-MEDIUM. Particularly useful for FFI wrappers that need C library init/cleanup.

---

## 29. Conditional Compilation

**Missing:** Including/excluding code based on build configuration at compile time.

**Present in:** Rust (`#[cfg(target_os = "linux")]`), Zig (`@import` + `comptime`), C (`#ifdef`), Go (build tags), Nim (`when`)

**Problem:** Can't write cross-platform code that compiles differently per target without runtime checks.

```rust
// Rust:
#[cfg(target_os = "linux")]
fn get_home() -> String { ... linux impl ... }

#[cfg(target_os = "windows")]
fn get_home() -> String { ... windows impl ... }
```

```simple
# Proposed:
@when(os == "linux")
fn get_home() -> text: linux_home_dir()

@when(os == "windows")
fn get_home() -> text: windows_home_dir()

@when(arch == "x86_64")
fn use_simd_ops(): ...

# Or block form:
if comptime os == "linux":
    # linux-specific code (compiled out on other platforms)
```

**Impact:** MEDIUM. Essential for writing cross-platform code and platform-specific optimizations.

---

## 30. Phantom Types / Marker Types

**Missing:** Type parameters that carry compile-time information without runtime cost.

**Present in:** Rust (PhantomData), Haskell, TypeScript (branded types), OCaml

**Problem:** Can't track state machines, units of measure, or authorization levels at the type level without runtime overhead.

```rust
// Rust phantom types for state machines:
struct Connection<State> {
    socket: TcpStream,
    _state: PhantomData<State>,
}
struct Disconnected;
struct Connected;

fn connect(c: Connection<Disconnected>) -> Connection<Connected> { ... }
fn send(c: &Connection<Connected>, msg: &[u8]) { ... }
// send(&disconnected)  // COMPILE ERROR
```

```simple
# Proposed:
struct Connection<State phantom>:
    socket: Socket

struct Disconnected
struct Connected

fn connect(c: Connection<Disconnected>) -> Connection<Connected>: ...
fn send(c: Connection<Connected>, msg: [u8]): ...
```

**Impact:** LOW-MEDIUM. Advanced type safety. Prevents state machine misuse entirely at compile time.

---

## Feature Priority Matrix

| # | Feature | Impact | Complexity | Comparison Languages |
|---|---------|--------|------------|---------------------|
| 5 | Derive / Auto-implement | HIGH | MEDIUM | Rust, Haskell, Kotlin |
| 4 | Struct update syntax | HIGH | LOW | Rust, JS, Elm |
| 8 | Default trait methods | HIGH | LOW | Rust, Java, Kotlin |
| 14 | Result/Option ergonomics | HIGH | LOW | Rust, Haskell, Swift |
| 1 | String format specifiers | HIGH | MEDIUM | Python, Rust, C# |
| 6 | Extension methods | HIGH | MEDIUM | Kotlin, Swift, C# |
| 13 | Exhaustiveness checking | HIGH | MEDIUM | Rust, Haskell, Elm |
| 20 | Multi-line strings (fix) | HIGH | LOW | Python, JS, Kotlin |
| 25 | String builder | HIGH | LOW | Java, Rust, Go |
| 12 | Newtype wrappers | HIGH | LOW | Rust, Haskell, Kotlin |
| 9 | Associated types | HIGH | HIGH | Rust, Swift, Haskell |
| 2 | Labeled breaks | MEDIUM | LOW | Rust, Kotlin, Java |
| 3 | errdefer | MEDIUM | LOW | Zig |
| 7 | Union types | MEDIUM | HIGH | TypeScript, Python |
| 10 | Atom / Symbol type | MEDIUM | MEDIUM | Ruby, Erlang, Clojure |
| 11 | Comptime evaluation | MEDIUM | HIGH | Zig, Rust, C++ |
| 15 | Tail call guarantee | MEDIUM | MEDIUM | Erlang, Scheme, Kotlin |
| 16 | Process supervision | MEDIUM | HIGH | Erlang/OTP, Akka |
| 17 | Pattern refinements | MEDIUM | LOW | Rust, Python, OCaml |
| 19 | Compile-time constants | MEDIUM | LOW | Rust, Zig, C++ |
| 21 | Scoped let expressions | MEDIUM | LOW | Kotlin, Rust, Haskell |
| 23 | Lazy initialization | MEDIUM | LOW | Kotlin, Swift, Rust |
| 26 | Trait objects (dyn) | MEDIUM | MEDIUM | Rust |
| 29 | Conditional compilation | MEDIUM | MEDIUM | Rust, Zig, Go |
| 18 | Module aliasing (fix) | MEDIUM | LOW | Python, Rust, JS |
| 22 | where clauses | LOW | LOW | Rust, Swift, C# |
| 24 | Keyword-only params | LOW | LOW | Python, Ruby, Swift |
| 27 | Numeric separators | LOW | LOW | Rust, Python, Java |
| 28 | Module init/teardown | LOW | LOW | Go, Erlang, Ruby |
| 30 | Phantom types | LOW | MEDIUM | Rust, Haskell, OCaml |

---

## Quick Wins (Low Complexity, High Value)

These could be implemented with minimal risk:

1. **Struct update syntax** (`Point(..p, x: 5)`) — parser + desugaring only
2. **Default trait method bodies** — already have trait syntax, add optional body
3. **Labeled breaks/continues** — lexer + control flow
4. **String multi-line fix** — fix existing broken triple-quote parser
5. **Numeric separator `_`** — trivial lexer change
6. **`errdefer`** — small addition to defer semantics
7. **`or` patterns in match** — `| A | B` already partially implied
8. **Result/Option chaining methods** — pure stdlib addition (no syntax change)
9. **Exhaustiveness check warning** — static analysis pass
10. **Module init/teardown syntax** — parser + runtime hook

---

## Feature Gaps by Language

### From Rust
- ✅ Generics (implemented)
- ✅ Pattern matching (implemented)
- ✅ Traits (implemented)
- ✅ Option/Result (implemented)
- ❌ `#[derive(...)]`
- ❌ `..struct_update`
- ❌ `'labeled` loops
- ❌ `const fn`
- ❌ `where` clauses
- ❌ `dyn Trait` objects
- ❌ Associated types
- ❌ `PhantomData` / phantom types
- ❌ String format specifiers (`{:?}`, `{:.2}`)

### From Zig
- ✅ `defer` (implemented)
- ❌ `errdefer`
- ❌ `comptime`
- ❌ Error unions (`!T`)
- ❌ `@embedFile`

### From TypeScript
- ✅ Generics
- ✅ Union types via enum (but not lightweight `A | B` notation)
- ❌ Discriminated union type narrowing
- ❌ Mapped types
- ❌ Conditional types (`T extends U ? A : B`)
- ❌ Template literal types

### From Python
- ✅ String interpolation (implemented)
- ✅ Comprehensions (implemented)
- ✅ `*args`/`**kwargs` variadic (implemented)
- ❌ Format specifiers (`f"{x:.2f}"`)
- ❌ Keyword-only parameters (`def f(*, kw_only)`)
- ❌ `@property` decorator equivalent

### From Erlang
- ✅ Actors (partially)
- ✅ Pattern matching
- ❌ Supervision trees
- ❌ Tail call guarantee
- ❌ Atom type
- ❌ Hot code reload

### From Kotlin/Swift
- ✅ Closures
- ✅ Extension-like methods (via trait impl, but not open extension)
- ❌ Extension methods on existing types
- ❌ Scope functions (`let`, `run`, `apply`)
- ❌ Data classes / record copy
- ❌ Sealed classes (exhaustive hierarchies)

---

## Conclusion

Simple's current feature set is well-rounded for a systems language with functional programming support. The highest-priority gaps fall into three categories:

1. **Ergonomics holes** (struct update, derive, multi-line strings, format specifiers) — daily friction
2. **Type safety gaps** (newtype, exhaustiveness, associated types) — prevent whole bug classes
3. **Standard library completeness** (Result/Option chaining, string builder) — avoid reinventing patterns

The design decisions to exclude exceptions and inheritance are sound and align with Rust/Zig's philosophy. The language would most benefit from filling the ergonomics holes first, as they affect every program written in Simple.
