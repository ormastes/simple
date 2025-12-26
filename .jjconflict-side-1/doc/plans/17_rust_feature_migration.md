# Rust Feature Migration Analysis

Analyzing Rust syntax features for potential adoption in Simple, checking LL(1) grammar compatibility and formal verification feasibility.

## Rust Features Analysis

### 1. Result/Option Types

**Rust:**
```rust
fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 { Err("division by zero".to_string()) }
    else { Ok(a / b) }
}

fn find(items: &[i32], target: i32) -> Option<usize> {
    items.iter().position(|&x| x == target)
}
```

**Simple Adaptation:**
```simple
fn divide(a: i32, b: i32) -> Result[i32, str]:
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

fn find(items: [i32], target: i32) -> i32?:
    for i, x in items.enumerate():
        if x == target:
            return Some(i)
    return None
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `Result[T, E]` and `T?` are type syntax, not expressions |
| Formal Verification | Excellent - algebraic types with exhaustive matching |
| Priority | **High** - already planned (feature #38 Option Type) |

**Recommendation:** Already have `T?` for Option. Add `Result[T, E]` as standard library type.

---

### 2. The `?` Operator (Error Propagation)

**Rust:**
```rust
fn process() -> Result<i32, Error> {
    let x = try_something()?;  // Early return on Err
    let y = try_another()?;
    Ok(x + y)
}
```

**Simple Adaptation:**
```simple
fn process() -> Result[i32, Error]:
    let x = try_something()?    # Early return on Err
    let y = try_another()?
    return Ok(x + y)
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - postfix `?` is unambiguous after expression |
| Formal Verification | Excellent - desugars to match, formally provable |
| Priority | **High** - major ergonomic improvement |

**Desugaring:**
```simple
# x = expr?
# becomes:
match expr:
    Ok(v): x = v
    Err(e): return Err(e)
```

**Recommendation:** Adopt. Clean syntax, formally verifiable transformation.

---

### 3. Impl Blocks

**Rust:**
```rust
struct Point { x: f64, y: f64 }

impl Point {
    fn new(x: f64, y: f64) -> Self { Point { x, y } }
    fn distance(&self, other: &Point) -> f64 { ... }
}
```

**Simple Already Has This:**
```simple
struct Point:
    x: f64
    y: f64

impl Point:
    fn new(x: f64, y: f64) -> Self:
        return Point(x: x, y: y)

    fn distance(self, other: Point) -> f64:
        ...
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `impl TypeName:` starts a block |
| Formal Verification | Yes - method resolution is static |
| Priority | **Already Implemented** (feature #16) |

---

### 4. Traits

**Rust:**
```rust
trait Display {
    fn fmt(&self) -> String;
}

impl Display for Point {
    fn fmt(&self) -> String { format!("({}, {})", self.x, self.y) }
}
```

**Simple Adaptation:**
```simple
trait Display:
    fn fmt(self) -> str

impl Display for Point:
    fn fmt(self) -> str:
        return "({self.x}, {self.y})"
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `trait Name:` and `impl Trait for Type:` are distinct |
| Formal Verification | Yes - trait coherence is decidable |
| Priority | **High** - already planned (feature #15) |

---

### 5. Lifetime Annotations

**Rust:**
```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

**Simple Approach:** Avoid explicit lifetimes.

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | N/A |
| Formal Verification | Complex - lifetime inference is hard |
| Priority | **Reject** - use ownership modes instead |

**Rationale:** Simple uses pointer modes (`&T`, `*T`, `-T`, `+T`) and GC by default. Explicit lifetimes add complexity without proportional benefit for Simple's use cases.

**Alternative:** Rely on:
- GC for most allocations (default)
- Unique pointers `&T` with RAII (no explicit lifetimes needed)
- Borrow checker can infer simple cases

---

### 6. Match Guards

**Rust:**
```rust
match value {
    Some(x) if x > 0 => println!("positive"),
    Some(x) if x < 0 => println!("negative"),
    Some(0) => println!("zero"),
    None => println!("nothing"),
}
```

**Simple Adaptation:**
```simple
match value:
    Some(x) if x > 0:
        print "positive"
    Some(x) if x < 0:
        print "negative"
    Some(0):
        print "zero"
    None:
        print "nothing"
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `if` after pattern is unambiguous |
| Formal Verification | Yes - guards are boolean expressions |
| Priority | **High** - natural extension of pattern matching |

**Exhaustiveness:** Guards complicate exhaustiveness checking but are manageable. The pattern without guard is the fallback.

---

### 7. If Let / While Let

**Rust:**
```rust
if let Some(x) = optional {
    println!("got {}", x);
}

while let Some(item) = iter.next() {
    process(item);
}
```

**Simple Adaptation:**
```simple
if let Some(x) = optional:
    print "got {x}"

while let Some(item) = iter.next():
    process(item)
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `if let` and `while let` are distinct from `if expr` |
| Formal Verification | Yes - desugars to match |
| Priority | **Medium** - convenient but match works |

**Desugaring:**
```simple
# if let pattern = expr: body
# becomes:
match expr:
    pattern: body
    _: pass
```

---

### 8. Derive Macros

**Rust:**
```rust
#[derive(Debug, Clone, PartialEq)]
struct Point { x: f64, y: f64 }
```

**Simple Adaptation (using attributes):**
```simple
#[derive(Debug, Clone, Eq)]
struct Point:
    x: f64
    y: f64
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - attributes are prefix metadata |
| Formal Verification | Yes - generated code is deterministic |
| Priority | **Medium** - reduces boilerplate |

**Built-in Derives:**
- `Debug` - string representation
- `Clone` - deep copy
- `Eq` / `PartialEq` - equality comparison
- `Ord` / `PartialOrd` - ordering
- `Hash` - hashing
- `Default` - default values

---

### 9. Declarative Macros (macro_rules!)

**Rust:**
```rust
macro_rules! vec {
    ($($x:expr),*) => { ... };
}
```

**Simple Approach:** Simpler macro system.

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Depends on design |
| Formal Verification | Challenging - macro expansion complicates proofs |
| Priority | **Low** - defer to later version |

**Recommendation:** Start with hygienic, expression-level macros. Avoid full Rust-style pattern macros initially.

---

### 10. Closures with `move`

**Rust:**
```rust
let x = 10;
let add_x = move |y| x + y;  // Captures x by value
```

**Simple Adaptation:**
```simple
let x = 10
let add_x = move \y: x + y    # Captures x by value
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `move` is keyword prefix |
| Formal Verification | Yes - ownership transfer is explicit |
| Priority | **Medium** - useful for async/actors |

**Default Behavior:**
- Without `move`: capture by reference (GC-managed)
- With `move`: capture by value (ownership transferred)

---

### 11. Iterator Combinators

**Rust:**
```rust
let sum: i32 = items.iter()
    .filter(|x| x > 0)
    .map(|x| x * 2)
    .sum();
```

**Simple (already similar):**
```simple
let sum = items
    .filter(\x: x > 0)
    .map(\x: x * 2)
    .sum()
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - method chaining is standard |
| Formal Verification | Yes - lazy iterators have clear semantics |
| Priority | **High** - already supported via method chaining |

---

### 12. Turbofish `::<T>`

**Rust:**
```rust
let x = "42".parse::<i32>()?;
let v = Vec::<i32>::new();
```

**Simple Alternative:**
```simple
let x: i32 = "42".parse()?
let v = Vec[i32].new()
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `[T]` for generics avoids `<>` ambiguity |
| Formal Verification | Yes - explicit type annotation |
| Priority | **Already Decided** - use `[T]` not `<T>` |

**Rationale:** `<>` conflicts with comparison operators. `[]` is unambiguous.

---

### 13. Associated Types

**Rust:**
```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

**Simple Adaptation:**
```simple
trait Iterator:
    type Item
    fn next(mut self) -> Self.Item?
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `type Name` in trait is distinct |
| Formal Verification | Yes - associated types are resolved statically |
| Priority | **Medium** - needed for advanced generics |

---

### 14. Where Clauses

**Rust:**
```rust
fn process<T, U>(x: T, y: U) -> i32
where
    T: Display + Clone,
    U: Iterator<Item = i32>,
{ ... }
```

**Simple Adaptation:**
```simple
fn process[T, U](x: T, y: U) -> i32
where T: Display + Clone,
      U: Iterator[Item = i32]:
    ...
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `where` after params, before `:` |
| Formal Verification | Yes - constraints are checked at instantiation |
| Priority | **Medium** - needed for complex generics |

---

### 15. Async/Await

**Rust:**
```rust
async fn fetch_data() -> Result<String, Error> {
    let response = client.get(url).await?;
    Ok(response.text().await?)
}
```

**Simple Adaptation:**
```simple
async fn fetch_data() -> Result[str, Error]:
    let response = client.get(url).await?
    return Ok(response.text().await?)
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `async fn` and `.await` are distinct |
| Formal Verification | Challenging - state machine transformation |
| Priority | **High** - already planned (feature #48) |

---

### 16. Pattern Bindings (`@`)

**Rust:**
```rust
match point {
    p @ Point { x: 0..=10, .. } => println!("small x: {:?}", p),
    _ => {}
}
```

**Simple Adaptation:**
```simple
match point:
    p @ Point(x: 0..10, ..):
        print "small x: {p}"
    _:
        pass
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `name @` before pattern |
| Formal Verification | Yes - name binding is simple |
| Priority | **Low** - rarely needed |

---

### 17. Or Patterns

**Rust:**
```rust
match value {
    1 | 2 | 3 => println!("small"),
    _ => println!("large"),
}
```

**Simple Adaptation:**
```simple
match value:
    1 | 2 | 3:
        print "small"
    _:
        print "large"
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `|` between patterns is distinct from expr `|` |
| Formal Verification | Yes - union of pattern sets |
| Priority | **Medium** - convenient for matching |

---

### 18. Range Patterns

**Rust:**
```rust
match age {
    0..=12 => "child",
    13..=19 => "teen",
    20..=64 => "adult",
    _ => "senior",
}
```

**Simple Adaptation:**
```simple
match age:
    0..12:
        "child"
    13..19:
        "teen"
    20..64:
        "adult"
    _:
        "senior"
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `n..m` in pattern context |
| Formal Verification | Yes - range membership is trivial |
| Priority | **Medium** - natural extension |

**Note:** Use `..` for exclusive end (Python-like), not `..=`.

---

### 19. Const Generics

**Rust:**
```rust
fn process<const N: usize>(arr: [i32; N]) { ... }
```

**Simple Adaptation:**
```simple
fn process[const N: usize](arr: [i32; N]):
    ...
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `const Name: Type` in generics |
| Formal Verification | Yes - compile-time constants |
| Priority | **Low** - advanced feature |

---

### 20. Struct Update Syntax

**Rust:**
```rust
let p2 = Point { x: 10.0, ..p1 };
```

**Simple (already has functional update):**
```simple
let p2 = p1 with x: 10.0
# or
let p2 = Point(x: 10.0, ..p1)
```

| Aspect | Analysis |
|--------|----------|
| LL(1) Safe | Yes - `with` keyword or `..expr` in struct literal |
| Formal Verification | Yes - field copying is explicit |
| Priority | **Already Considered** - feature #20 functional update |

---

## Summary Table

| Feature | LL(1) Safe | Formal Proof | Priority | Status |
|---------|------------|--------------|----------|--------|
| Result type | Yes | Excellent | High | Adopt as stdlib |
| `?` operator | Yes | Excellent | High | **Adopt** |
| Impl blocks | Yes | Yes | High | Already have |
| Traits | Yes | Yes | High | Planned (#15) |
| Lifetimes | N/A | Complex | - | **Reject** |
| Match guards | Yes | Yes | High | **Adopt** |
| If let / While let | Yes | Yes | Medium | **Adopt** |
| Derive macros | Yes | Yes | Medium | **Adopt** |
| macro_rules! | Risky | Hard | Low | Defer |
| `move` closures | Yes | Yes | Medium | **Adopt** |
| Iterators | Yes | Yes | High | Already have |
| Turbofish | N/A | N/A | - | Use `[T]` instead |
| Associated types | Yes | Yes | Medium | **Adopt** |
| Where clauses | Yes | Yes | Medium | **Adopt** |
| Async/await | Yes | Hard | High | Planned (#48) |
| Pattern `@` | Yes | Yes | Low | Optional |
| Or patterns | Yes | Yes | Medium | **Adopt** |
| Range patterns | Yes | Yes | Medium | **Adopt** |
| Const generics | Yes | Yes | Low | Defer |
| Struct update | Yes | Yes | Medium | Planned (#20) |

## Features to Add to feature.md

Based on this analysis, these Rust features should be added:

| # | Feature | Importance | Difficulty | Notes |
|---|---------|------------|------------|-------|
| 72 | **Result Type** (`Result[T, E]`) | 5 | 2 | Stdlib type for error handling |
| 73 | **`?` Operator** (error propagation) | 5 | 2 | Desugars to match |
| 74 | **Match Guards** (`case x if cond:`) | 4 | 2 | Extension of pattern matching |
| 75 | **If Let / While Let** | 3 | 2 | Convenient pattern sugar |
| 76 | **Derive Macros** (`#[derive(...)]`) | 4 | 3 | Code generation |
| 77 | **Move Closures** (`move \x: ...`) | 3 | 3 | Explicit capture |
| 78 | **Associated Types** (`type Item`) | 3 | 3 | For advanced traits |
| 79 | **Where Clauses** | 3 | 2 | For complex generics |
| 80 | **Or Patterns** (`a | b | c:`) | 4 | 2 | Pattern union |
| 81 | **Range Patterns** (`0..10:`) | 4 | 2 | Numeric range match |

## Rejected Rust Features

| Feature | Reason |
|---------|--------|
| Explicit lifetimes | Too complex; use GC + ownership modes |
| macro_rules! | Too complex; defer to simpler macro system |
| Turbofish `::<T>` | Use `[T]` bracket syntax instead |
| Const generics | Low priority; defer to later |

## Simple vs Rust: Design Differences

| Aspect | Rust | Simple | Rationale |
|--------|------|--------|-----------|
| Memory | Manual + Borrow checker | GC default + modes | Easier learning curve |
| Generics | `<T>` | `[T]` | Avoid `<>` ambiguity |
| Lifetimes | Explicit `'a` | Implicit/inferred | Reduce complexity |
| Blocks | `{}` | Indentation | Python-like readability |
| Mutability | `let mut` | `mut` keyword | Similar approach |
| Null | None (Option) | `T?` syntax | Simpler notation |
| Error | `Result<T, E>` | `Result[T, E]` | Same concept, bracket syntax |

## Implementation Order

### Phase 1: Error Handling (0.2.x)
1. Result type in stdlib
2. `?` operator
3. Match guards

### Phase 2: Pattern Extensions (0.2.x)
4. If let / While let
5. Or patterns
6. Range patterns

### Phase 3: Advanced Generics (0.3.x)
7. Where clauses
8. Associated types
9. Derive macros

### Phase 4: Closures (0.3.x)
10. Move closures (needed for actors/async)
