# Simple Language Specification

## Syntax

Simple is a statically typed programming language with a clean, high-level syntax. It uses indentation to define code blocks (similar to Python) instead of braces or end keywords. All statements indented at the same level belong to the same block, and a decrease in indentation signifies the end of the current block. Indentation makes the structure of code clear and enforceable by the language (not just a style choice). For example:

```simple
# An if/else example with indentation
if x > 0:
    print "x is positive"
else:
    print "x is non-positive"
```

Simple's syntax also draws inspiration from Ruby for method calls and DSLs. Method calls do not require parentheses around arguments at the **statement level** (outermost position only), especially for DSL-style usage. For instance, `user.set name: "John", age: 30` is valid, treating `name:` and `age:` as named arguments. However, nested calls require parentheses to maintain unambiguous, one-pass parsing: `print format("Hello", name)` rather than `print format "Hello", name`. This restriction ensures the grammar remains LL(1)-compatible with single-token lookahead. Named arguments are supported and passed by name, improving readability for functions with multiple parameters (e.g. `order.place item: "Book", quantity: 2`). Trailing blocks (closures) can be passed to methods for iteration or DSL constructs. A method call can be followed by a block introduced by a backslash-prefixed parameter list and colon. For example:

```simple
# Iterating with a trailing block (using backslash for lambda params)
list.each \item:
    print "Item: {item}"

# Multiple parameters
map.each \key, value:
    print "{key}: {value}"
```

In the example above, `each` is a method that takes a block. The block is introduced by `\item` (the backslash signals lambda parameters, inspired by ML-family languages) and a colon, then indented code as the block body. This syntax is unambiguous and requires only one token of lookahead—the parser sees `\` and immediately knows a lambda parameter list follows. This Python-like indentation combined with explicit lambda syntax allows DSLs to read naturally while remaining easy to parse. No semicolons are needed at end of lines (newlines separate statements). Comments begin with `#` and extend to end of line.

### Other Syntax Highlights

- **Literals**: Numbers (`42`, `3.14`), booleans (`true`, `false`), and `nil` for "null" are supported. Underscores can be used in numeric literals for readability (e.g. `1_000_000`).

- **String Literals**: Simple has two string literal types:

  **Interpolated Strings (default)** - Double quotes `"..."` create strings with automatic interpolation where `{expr}` embeds the value of any expression:
  ```simple
  let name = "world"
  let count = 42
  let msg = "Hello, {name}! Count is {count + 1}"
  # Result: "Hello, world! Count is 43"
  ```
  Use `{{` and `}}` for literal braces. This is the default and most common string type.

  **Raw Strings** - Single quotes `'...'` create raw strings with no interpolation or escape processing:
  ```simple
  let regex = '[a-z]+\d{2,3}'     # No escaping needed
  let path = 'C:\Users\name'      # Backslashes are literal
  let template = '{name}'         # Braces are literal, not interpolation
  ```
  Raw strings are useful for regular expressions, file paths, and templates where you want literal backslashes and braces.

  **Legacy f-string prefix**: For compatibility, the `f` prefix is still supported but optional since double-quoted strings interpolate by default:
  ```simple
  let msg = f"Hello, {name}!"  # Same as "Hello, {name}!"
  ```

- **Line Continuation**: A line ending with a backslash `\` followed immediately by a newline will continue on the next line (though in many cases, indentation or parentheses make this unnecessary). Note: This is unambiguous with lambda syntax since line continuation requires `\` at line end, while lambda params have `\` followed by identifiers.

- **Operators**: Standard arithmetic and comparison operators (`+`, `-`, `*`, `/`, `==`, `!=`, `<`, `>` etc.), logical operators (`and`, `or`, `not`), and the method chaining arrow operator (`->`, explained below) are available.

### Parsing Design Rationale

Simple's syntax is carefully designed to support **true one-pass, predictive parsing** with at most one token of lookahead (LL(1) or near-LL(1)). Two key decisions enable this:

1. **No-parentheses calls restricted to statement level**: Parentheses can only be omitted for the outermost method call in a statement. This eliminates ambiguity in nested expressions. For example:
   ```simple
   # Valid: outermost call drops parens
   print format("value: {x}")
   user.set name: "Alice", age: 30
   
   # Invalid: nested no-paren call is ambiguous
   # print format "value: {x}"  # Error: use parens for nested calls
   ```

2. **Backslash-prefixed lambda parameters**: Lambda/block parameters use `\x` rather than `|x|`. The backslash is unambiguous—when the parser sees `\`, it immediately knows a lambda parameter list follows, with no lookahead confusion against bitwise OR or other operators:
   ```simple
   # Clear lambda syntax
   let double = \x: x * 2
   items.filter \x: x > 0
   
   # Multiple parameters
   pairs.map \a, b: a + b
   ```

These choices keep the grammar simple and predictable while preserving the language's expressive power. The `->` functional update operator remains unambiguous because its context is always local (appearing between an identifier/expression and a method name).

---

## Functional Update Syntax (`->`)

Simple introduces a functional update syntax using `->`. Writing `target->method(args)` is syntactic sugar that:
1. Calls `target.method(args)`
2. Assigns the result back to `target`

This is equivalent to `target = target.method(args)` but more concise.

### Basic Usage

```simple
let mut data = load_data()
data->normalize()           # data = data.normalize()
data->filter(min: 0)        # data = data.filter(min: 0)
data->save("out.txt")       # data = data.save("out.txt")
```

### Chaining

Multiple updates can be chained in a single expression:

```simple
data->normalize()->filter(min: 0)->save("out.txt")
```

This is equivalent to:

```simple
data = data.normalize()
data = data.filter(min: 0)
data = data.save("out.txt")
```

### Use Cases

The `->` operator is particularly useful for:

1. **Immutable data transformations** - When methods return new instances rather than mutating in place:
   ```simple
   let mut list = [1, 2, 3]
   list->append(4)->sort()->reverse()
   # list is now [4, 3, 2, 1]
   ```

2. **Builder patterns** - When constructing objects step by step:
   ```simple
   let mut config = Config.new()
   config->set_host("localhost")->set_port(8080)->set_timeout(30)
   ```

3. **State machine transitions** - When updating state:
   ```simple
   let mut parser = Parser.new(input)
   parser->read_header()->validate()->parse_body()
   ```

### Requirements

- The target must be a mutable variable (`let mut` or mutable field)
- The method must return a value compatible with the target's type
- Works with any expression that evaluates to an assignable location

---

## Types and Mutability Rules

Simple is statically typed, but it features type inference to reduce verbosity. This means the compiler can often deduce the types of variables and expressions from context, so developers do not need to annotate types everywhere. For example, `let count = 5` automatically infers `count` to be an `i64`. However, you can explicitly annotate types when needed for clarity or interface definitions (e.g. `let count: i64 = 5`). Every value and expression has a definite type at compile time, even if not explicitly written, due to inference.

The language has a variety of built-in types: primitive types like `i8`, `i16`, `i32`, `i64` (signed integers), `u8`, `u16`, `u32`, `u64` (unsigned integers), `f32`, `f64` (floating-point numbers), `bool` (boolean), and `str` (text). It also includes compound types such as tuples `(T1, T2, ...)`, arrays `[T]`, and dictionaries `{Key: Value}`. Functions have function types (with arrows, e.g. `fn(i64, i64) -> i64` for a function taking two i64s and returning an i64). Types can be parameterized using generics (e.g. `List[T]` for a list of T elements).

Simple enforces clear mutability rules for data structures to encourage safe programming. Immutability is the default for value types, aligning with modern best practices:

### Structs (Value Types)

Structs are immutable by default. If you declare a struct with no additional modifier, its fields cannot be modified after construction. This means all fields are effectively read-only values. To define a struct whose fields can change, you must mark it with the `mut` keyword (mutable). For example:

```simple
struct Point:
    x: f64
    y: f64

mut struct Cursor:
    x: f64
    y: f64
```

In this snippet, `Point` is immutable (once created, you can't change its `x` or `y`), whereas `Cursor` is a mutable struct. Making immutability the default for structs helps prevent accidental changes and enables the compiler to make optimizations. As the Julia language designers note, defaulting to immutable encourages asking "does this really need to be mutable?" which leads to safer designs.

### Classes (Reference Types)

Classes are mutable by default. Classes represent objects on the heap that are referred to by reference, and their internal state can be changed. If a class's state should never change once created, it can be marked with `immut` to indicate an immutable class. For example:

```simple
class Person:
    name: String
    age: i32

immut class Color:
    red: u8
    green: u8
    blue: u8
```

Here, `Person` is a regular mutable class (you can change a Person's name or age via methods or direct access if allowed), while `Color` is an immutable class (its `red`, `green`, `blue` fields are set at construction and never change). An `immut` class requires that all its fields are either immutable types or also marked immutable, ensuring the entire object state cannot be altered.

### Variables

Variables in Simple are **mutable by default** (like Python) for ease of use. The `let` keyword is optional. Use `const` for immutable bindings:

```simple
x = 10            # mutable variable (let is optional)
let y = 20        # also mutable (let is explicit but optional)
x = 30            # ok, x is mutable
y = 40            # ok, y is mutable

const MAX = 100   # immutable constant
MAX = 200         # compile error, const cannot be reassigned
```

This Python-like approach makes the language easy to learn and use. For cases where immutability is desired, use `const` for compile-time constants or `static` for global variables.

The compiler enforces that only mutable variables or fields can be assigned to, and that immutable data cannot be modified. Attempting to modify an immutable struct or an `immut` class's field results in a compile-time error. You can freely copy or pass around immutable values without worrying that they will change underfoot, which is especially important in concurrent and functional patterns.

Type inference works in tandem with these rules. For example, if you write `p = Point(3,4)` and `Point` is immutable, the type of `p` is inferred as `Point` and you simply can't call any mutating method on it (since none exist for an immutable struct). If you had `cur = Cursor(0,0)`, the compiler infers `cur` as type `Cursor` and allows `cur.x = 5` because variables are mutable by default.

---

## Structs and Classes

Structs and classes are the two mechanisms for defining custom composite types in Simple, each with distinct semantics:

### Structs

Structs are value types (similar to structs in C or Rust). They are copied on assignment and passed by value (although the compiler may optimize large structs by reference under the hood, this is transparent). Structs are ideal for small, immutable data groupings like points, ranges, or data transfer objects. Unless marked `mut`, a struct's fields cannot be changed after it's constructed. Structs do not support inheritance (you cannot subclass a struct), but they can implement traits (interfaces) for polymorphism. Example struct definition and usage:

```simple
struct Point:
    x: f64
    y: f64

a = Point(x: 1, y: 2)
b = a              # copies the values x=1, y=2 into b
# a.x = 5          # Error: Point is immutable by default
```

### Classes

Classes are reference types, allocated on the heap and managed by the runtime (likely with automatic memory management, e.g. garbage collection). Variables of class type are references (pointers) to objects. Classes can be thought of like objects in Java or Ruby. By default, class instances are mutable (fields can be changed), but you can opt-in to immutability by declaring the class as `immut` (making it a deeply immutable object as explained in the previous section). Classes can have methods (including constructors, typically a special `init` method or part of `fn new` pattern) and support single inheritance by default (a class may inherit from one base class if desired) unless the language design is purely composition-oriented. Traits can also be implemented by classes. Example class:

```simple
class Person:
    name: String
    age: i32

    fn birthday():
        # method to increment age
        self.age = self.age + 1

let p = Person(name: "Alice", age: 30)
p.birthday()          # now age is 31
```

In this example, `Person` is a class with a method that mutates its state. Because classes are reference types, assigning `q = p` would make `q` and `p` refer to the same `Person` object (so changes via one reference reflect in the other). If `Person` were declared as `immut class Person: ...`, then its fields could not be changed after construction and the `birthday()` method as written would not compile (since it attempts to modify an immutable field).

### Visibility and Access

By default, all struct and class fields are publicly readable but only modifiable according to mutability rules. The language could allow an optional access modifier (like `private` or similar) to restrict access, but by default the emphasis is on immutability for safety rather than encapsulation for correctness. Methods defined inside a class have access to its private state.

### Equality and Copying

Structs, being value types, support value equality by default (two Points with same x,y are equal). Classes use reference equality by default (two references are equal if they point to the same object), though classes can override an `.equals` method to define structural equality if needed. Cloning an object requires either a copy method or, if the class is `immut`, just assigning the reference (since immutability means sharing is safe).

---

## Memory & Ownership

Simple has two memory worlds:

1. **GC-managed references** – plain `T`
2. **Manual/explicit memory** – via pointer types and typed `new` forms

GC is the default; manual memory is opt-in and always explicit in the types. This design allows Simple to be used for both high-level application code (using GC) and performance-critical systems code (using manual memory management) within the same program.

### Reference and Pointer Kinds

#### GC-Managed Reference: `T`

A bare type `T` is a GC-managed reference to a heap object:

```simple
let p: Player = Player(name: "Hero", hp: 100)
```

Lifetime is fully managed by the garbage collector. This is the default and recommended approach for most code.

#### Unique Pointer: `&T`

`&T` is a unique owning pointer:

- Exactly one owner at a time
- Move-only (cannot be copied)
- When the `&T` goes out of scope, the object is destroyed and memory freed (RAII)

```simple
let u: &Player = new(&) Player(name: "Solo", hp: 50)
# u is the sole owner

let v = move u    # ownership transferred to v
# u is now unusable (compile error if accessed)
```

#### Shared Pointer: `*T`

`*T` is a shared owning pointer (reference-counted):

- Multiple owners allowed
- Copying/cloning increments the reference count
- Object freed when reference count hits zero

```simple
let s1: *Player = new* Player(name: "Shared", hp: 75)
let s2 = s1       # refcount incremented, both own the object
# Object freed when both s1 and s2 go out of scope
```

#### Weak Pointer: `-T`

`-T` is a weak pointer:

- Non-owning reference to an object managed by `*T` (or GC)
- Does not keep the object alive
- Must be upgraded to a strong pointer before use

```simple
let s: *Player = new* Player(name: "Target", hp: 100)
let w: -Player = weak_of(s)

# Later...
match w.upgrade():
    case Some(strong):
        print "Player still alive: {strong.name}"
    case None:
        print "Player was freed"
```

#### Handle Pointer: `+T`

`+T` is a handle pointer:

- A small ID (typically `(slot_index, generation)`) into a global handle pool for type `T`
- Non-owning; lifetime is controlled by the pool, not the handle
- Dereference always goes through the global pool
- Cheap to copy (like an integer)

```simple
let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
# h is a lightweight handle into the global Enemy pool
```

**Important constraints**:

- For each concrete type `T`, there is **at most one** handle pool
- That pool must be defined at **global scope**
- `+T` handles are only valid relative to that single global pool for `T`

### Allocation Forms (`new` Variants)

There is no generic `new`. The allocation form explicitly encodes ownership semantics:

| Form | Returns | Ownership |
|------|---------|-----------|
| `new(&) T(...)` | `&T` | Unique (move-only, RAII) |
| `new* T(...)` | `*T` | Shared (refcounted) |
| `new- T(...)` | `-T` | Weak (non-owning) |
| `new+ T(...)` | `+T` | Handle (pool-managed) |

#### Unique Allocation: `new(&) T(...) → &T`

```simple
let u: &Player = new(&) Player(name: "Unique", hp: 100)
```

Semantics:

- Allocate `T` on the manual heap
- Return unique pointer `&T`
- `&T` is move-only:
  - `let b = u` → compile error (implicit copy)
  - `let b = move u` → OK; `u` becomes unusable
- When the `&T` binding goes out of scope, destructor runs and memory is freed

#### Shared Allocation: `new* T(...) → *T`

```simple
let s: *Player = new* Player(name: "Shared", hp: 100)
```

Semantics:

- Allocate `T` with an embedded reference count
- Return shared pointer `*T`
- Copying `*T` increments the reference count
- When reference count reaches zero, destructor runs and memory is freed

#### Weak Allocation: `new- T(...) → -T`

```simple
let w: -Player = new- Player(name: "Ephemeral", hp: 50)
```

Semantics:

- Convenience for creating a weak pointer to a freshly allocated shared object
- Equivalent to:
  ```simple
  let s: *Player = new* Player(name: "Ephemeral", hp: 50)
  let w: -Player = weak_of(s)
  # Caller must keep some *T alive; w alone is non-owning
  ```
- `w` never owns; dropping `w` does not affect the object's lifetime
- Use `w.upgrade()` to get `*T?` (returns `None` if object was freed)

#### Handle Allocation: `new+ T(...) → +T`

```simple
let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
```

Semantics:

- Uses the **single global handle pool** for type `Enemy`
- Allocates a slot in that pool, constructs `Enemy` in that slot
- Returns a handle `+Enemy` pointing to that slot
- `+T` is cheap to copy (it's just an ID)
- Dropping `+T` does **not** free the object; the pool controls lifetime

### Global Handle Pools

For each handle-eligible type `T`:

- There can be **at most one** handle pool
- It **must** be declared at global scope

#### Declaration Syntax

```simple
handle_pool Enemy:
    capacity: 1024
```

Semantics:

- Declares the global handle pool for `Enemy`
- Internally, the compiler/runtime creates:
  ```simple
  global __handle_pool_Enemy: HandlePool[Enemy] = HandlePool[Enemy].with_capacity(1024)
  ```
- All uses of `new+ Enemy(...)` and handle operations for `+Enemy` refer to this pool

#### Pool Rules

1. **Exactly one pool per type**: Multiple `handle_pool Enemy` declarations produce a compile-time error

2. **Pool required for `new+`**: If code uses `new+ T(...)` without a declared `handle_pool T`, the compiler emits:
   ```
   error: No global handle pool for type T
   ```

3. **Global scope only**: Declaring `handle_pool` inside a function, actor, or block produces a compile-time error

#### Using Handles at Runtime

Given:

```simple
handle_pool Enemy:
    capacity: 1024

let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
```

The runtime:

1. Allocates or reuses a slot in `__handle_pool_Enemy`
2. Constructs `Enemy` in that slot
3. Returns a `+Enemy` handle (slot index + generation)

**Accessing handle data**:

```simple
# Mutable access
match Enemy.handle_get_mut(h):
    case Some(e):
        e.hp -= 10
    case None:
        # Handle invalid (freed or never allocated)
        log "Enemy not found"

# Read-only access
match Enemy.handle_get(h):
    case Some(e):
        print "Enemy HP: {e.hp}"
    case None:
        log "Enemy not found"
```

**Freeing a handle**:

```simple
Enemy.handle_free(h)   # Invalidate handle, recycle slot
```

Under the hood, all operations act on the single global pool for `Enemy`.

### Ownership and Lifetime Summary

| Type | Ownership | Lifetime Control |
|------|-----------|------------------|
| `T` | GC-managed | Garbage collector |
| `&T` | Unique owner | RAII (freed when owner drops) |
| `*T` | Shared owners | Reference count (freed at zero) |
| `-T` | Non-owning | Controlled by `*T` or GC |
| `+T` | Non-owning | Controlled by global handle pool |

**Who frees what**:

| Type | Freed When |
|------|------------|
| `&T` | Last `&T` binding goes out of scope |
| `*T` | Reference count reaches zero |
| `-T` | Never frees (non-owning) |
| `+T` | Never frees; pool's `handle_free` or compaction |
| `T` (GC) | GC determines unreachability |

### Compile-Time Checks for `+T` / `new+`

1. **Pool requirement**: Use of `new+ T(...)` is only valid if a single global `handle_pool T` exists
   - No pool → compile error
   - More than one pool → compile error

2. **No local pools**: `handle_pool T` is only allowed at top-level (global) scope
   - Inside function, actor, or block → compile error

3. **Type match**: `new+ T(...)` and all `T.handle_*` operations are bound to the pool for exactly that `T`
   - The type system keeps pools sealed per type
   - No polymorphic or wrong-type handle usage

### Borrowing

Borrow types provide non-owning temporary references:

| Borrow Type | Description |
|-------------|-------------|
| `&T_borrow` | Immutable borrow |
| `&mut T_borrow` | Mutable borrow |

Borrows can reference data inside:
- GC-managed `T`
- Unique `&T`
- Shared `*T`
- Handle pool slots

The compiler enforces that **borrows never outlive their source**:

```simple
fn damage_enemy(h: +Enemy, amount: i32):
    match Enemy.handle_get_mut(h):
        case Some(e):      # e is a short-lived mutable borrow
            e.hp -= amount
            # e cannot escape this scope
        case None:
            log "Enemy not found"
```

### Choosing the Right Pointer Type

| Use Case | Recommended Type |
|----------|------------------|
| General application code | `T` (GC) |
| Single owner, deterministic cleanup | `&T` (unique) |
| Multiple owners, shared lifetime | `*T` (shared) |
| Observer pattern, caches | `-T` (weak) |
| Entity systems, game objects, pools | `+T` (handle) |

#### Example: Game Entity System with Handles

```simple
handle_pool Enemy:
    capacity: 10000

handle_pool Projectile:
    capacity: 50000

actor GameWorld:
    state:
        enemies: List[+Enemy] = []
        projectiles: List[+Projectile] = []

    on SpawnEnemy(pos: Vec2, hp: i32) waitless:
        let h: +Enemy = new+ Enemy(pos: pos, hp: hp)
        self.enemies->push(h)

    on SpawnProjectile(pos: Vec2, vel: Vec2, target: +Enemy) waitless:
        let p: +Projectile = new+ Projectile(pos: pos, vel: vel, target: target)
        self.projectiles->push(p)

    on Tick(dt: f64) waitless:
        # Update projectiles
        for proj_handle in self.projectiles:
            match Projectile.handle_get_mut(proj_handle):
                case Some(proj):
                    proj.pos = proj.pos + proj.vel * dt
                    # Check collision with target
                    match Enemy.handle_get_mut(proj.target):
                        case Some(enemy):
                            if distance(proj.pos, enemy.pos) < HIT_RADIUS:
                                enemy.hp -= DAMAGE
                                Projectile.handle_free(proj_handle)
                        case None:
                            # Target enemy was destroyed
                            Projectile.handle_free(proj_handle)
                case None:
                    pass  # Projectile already freed

        # Remove dead enemies
        for enemy_handle in self.enemies:
            match Enemy.handle_get(enemy_handle):
                case Some(enemy):
                    if enemy.hp <= 0:
                        Enemy.handle_free(enemy_handle)
                case None:
                    pass

        # Compact lists (remove freed handles)
        self.enemies->retain(\h: Enemy.handle_valid(h))
        self.projectiles->retain(\h: Projectile.handle_valid(h))
```

This example demonstrates:
- Separate handle pools for different entity types
- Handles stored in collections (cheap to copy)
- Safe access patterns with `handle_get`/`handle_get_mut`
- Explicit lifetime control via `handle_free`
- Validation with `handle_valid`

---

## Functions and Pattern Matching

### Functions

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition style and Rust's explicitness. A function definition includes the name, parameters (with optional types if not inferrable), an optional return type, and a body indented under the header. For example:

```simple
fn add(a: i64, b: i64) -> i64:
    return a + b
```

This defines a function `add` that takes two Ints and returns an Int. If the return type can be inferred, it might be optional; for instance, `fn add(a: Int, b: Int): return a + b` could be allowed with type inference inferring the return as Int from the `a+b` expression. If a function does not explicitly return a value, it returns `nil` (unit type).

Simple supports first-class functions and lambdas/closures. You can assign functions to variables or pass them as arguments. An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages like Haskell), for example: `let square = \x: x * x` assigns a lambda to `square`. For lambdas with explicit type annotations, parentheses clarify the parameter types: `let square = \(x: Int) -> i64: x * x`. The backslash syntax was chosen for one-pass parsing—seeing `\` immediately signals a lambda, requiring only single-token lookahead.

### Pattern Matching

Pattern Matching is a powerful feature of Simple, enabling branching on the structure of data (especially for enums and other algebraic types). The `match` expression is used, similar to a switch in other languages but far more flexible. A match takes an expression and a series of pattern cases to try. Each case has a pattern and the code to execute if the pattern matches. Patterns can include literal values, variable binding, enum constructors, struct destructuring, and wildcards. All possibilities must be covered (exhaustive matching), otherwise the code will not compile.

Example of pattern matching on an enum and other values:

```simple
enum Token:
    Number(value: i64)
    Plus
    Minus
    EOF

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return "Number({val})"
        case Plus:
            return "Plus sign"
        case Minus:
            return "Minus sign"
        case EOF:
            return "End of input"

# Using pattern matching with other types
let x = 10
match x:
    case 0:
        print "Zero"
    case 1 | 2 | 3:
        print "Small number"
    case n if n < 0:
        print "Negative number: {n}"
    case _:
        print "Large number"
```

In the first match, each possible variant of `Token` is handled, and the compiler will ensure no variant is missing (exhaustiveness). In the second match on an integer `x`, we see various pattern forms: a literal, a pattern with alternatives (`1 | 2 | 3` matches any of those values), a guard clause (`n if n < 0` to add an extra condition when matching a value to `n`), and a wildcard `_` to catch all other cases. The semantics are like Rust's match or Scala's pattern matching – the first matching case's body is executed, and patterns are tested in order.

Pattern matching can also destructure structs and tuples. For example:

```simple
struct Point:
    x: f64
    y: f64

let p = Point(x: 5, y: 0)
match p:
    case Point(x: 0, y: 0):
        print "Origin"
    case Point(x: x_val, y: 0):
        print "On X axis at {x_val}"
    case Point(x: 0, y: y_val):
        print "On Y axis at {y_val}"
    case Point(x: _, y: _):
        print "Somewhere else"
```

This demonstrates matching a struct by its fields. You can use `_` to ignore certain values, or bind them to new variables (`x_val`, `y_val`) for use in the case's body. Pattern matching thus provides a concise yet expressive way to branch on complex data structures safely.

---

## Traits and Implementations

Traits in Simple are the mechanism for defining interfaces or abstract sets of methods that types can implement (similar to type classes in Haskell or interfaces in Java, but more flexible). A trait is a collection of method signatures (and optionally default method implementations) that describe some behavior. Types (structs or classes) can implement these traits to guarantee they provide those methods, enabling polymorphic code that works over any type implementing the trait.

### Defining a Trait

```simple
trait Printable:
    fn stringify() -> String
    fn print_self():
        # default implementation
        print self.stringify()
```

Here, `Printable` is a trait with one required method `stringify` (no default provided) and one method `print_self` that has a default implementation (calling `stringify` and printing the result). The special `self` keyword in trait definitions refers to the implementing instance type (like `Self` in Rust traits).

### Implementing a Trait

To implement a trait for a type, use an `impl Trait for Type` block:

```simple
struct Person:
    name: String
    age: i32

impl Printable for Person:
    fn stringify() -> String:
        # implement the required trait method
        return "{self.name} (age {self.age})"
    # print_self method is not overridden, so it will use the trait's default
```

In this example, we implement `Printable` for `Person`. We provide an implementation for `stringify`. We did not provide `print_self`, so `Person` gets the default implementation of `print_self` from the trait automatically. Now any function that expects a `Printable` can accept `Person` as well.

### Dispatch

Traits support static dispatch by default – the compiler knows at compile time the exact type and can optimize calls – but they could also support dynamic dispatch if needed (for example, using a `Printable` trait object to hold any printable thing, akin to a `dyn Trait` in Rust). To use dynamic dispatch, the language might allow something like `let x: Printable = somePrintableObject` which under the hood uses a vtable. But by default, generics with trait bounds are the idiomatic way: e.g. `fn log[T: Printable](item: T) { ... }` can call `item.print_self()` on anything that implements `Printable` without knowing the concrete type (monomorphization at compile time).

### Trait Bounds and Generics

Traits are often used as bounds on type parameters. For instance:

```simple
fn print_all[T: Printable](items: List[T]):
    for item in items:
        item.print_self()
```

This generic function `print_all` can accept a list of any type `T` that implements `Printable`. The compiler will enforce that only types implementing `Printable` are passed, and within the function, `item` is known to be `Printable` so calling `print_self` is allowed.

### Associated Types and Trait Inheritance

Associated types and trait inheritance may also be part of the trait system. For example, a trait could include an associated type placeholder that implementations must specify (similar to Rust's associated types), and one trait could require another (trait `Drawable` might require trait `Printable`, meaning any `Drawable` must also be `Printable`). These allow advanced abstraction capabilities.

By using traits, Simple supports polymorphism without needing class inheritance for every use-case. You can achieve mixins or interface-like behavior by implementing multiple traits for a single type (since a struct or class can implement any number of traits). This enables a form of multiple inheritance of behavior (as opposed to state), since a type can fulfill multiple interfaces. The design encourages composition: rather than subclassing a base class to inherit methods, you implement traits that provide the desired behavior.

---

## Enums and Unions

Simple provides enumerations (enums) as a way to define a type that can be one of several variants (each variant possibly carrying data). Enums in Simple are algebraic data types, very similar to those in Rust or Haskell. They are sum types that facilitate clear modeling of data that has multiple shapes.

### Defining an Enum

```simple
enum Result[T]:
    Ok(value: T)
    Err(error: String)
```

This defines a generic enum `Result[T]` with two variants: `Ok` holding a value of type `T`, and `Err` holding an error message. Enums can be parameterized by type as shown. Each variant can have zero or more fields (here `Ok` has one field, `Err` has one field). Enums are value types (like structs) and, like structs, are immutable by default (their contents can't be changed after creation, you'd create a new variant instead).

### Using Enums

Using enums typically goes hand-in-hand with pattern matching (as shown earlier). For example:

```simple
fn handle(result: Result[i64]):
    match result:
        case Ok(val):
            print "Success: {val}"
        case Err(msg):
            print "Error: {msg}"
```

### Union Types

Simple also supports union types for cases where you want to indicate a variable might hold one of multiple types. There are two concepts often referred to as "union":

1. **Tagged unions** – which is essentially what enums are (each variant is an implicit tag). In that sense, enums already provide a form of union with safety (since you must match the tag to access the value).

2. **Untagged unions** – a low-level feature (like C unions) where the same memory can represent different types without an explicit tag. These are unsafe in general and not a typical feature of a high-level safe language like Simple. Simple avoids raw untagged unions to maintain type safety (only one active type at a time and the compiler knows which).

However, Simple's type system does allow a form of union type in type annotations: for example, one could write a function parameter type as `Int | String` to mean it accepts either an `i64` or a `str`. This is more like a type union or sum type without a name. Under the hood, this could be compiled into an enum with two variants. Pattern matching can be used to discern which one it is at runtime:

```simple
fn example(x: i64 | str):
    match x:
        case i: i64:
            print "Integer: {i}"
        case s: String:
            print "String: {s}"
```

This notation treats `i64|str` as an anonymous union of two types. The pattern `i: i64` matches if `x` is an `i64` (and binds it to `i`), and `s: String` matches if it's a `String`. Such union types are handy for quick use-cases, but for more complex scenarios or more than a couple of alternatives, a named enum is preferable for clarity.

### Option Type

A very common enum that is likely in the standard library (or prelude) is `Option[T]` or `Maybe[T]`, representing "something or nothing" (with variants like `Some(value)` or `None`). This is used instead of null values to represent the absence of a value in a type-safe way.

In summary, enums (tagged unions) allow you to define custom variants and enforce at compile time that you handle all cases, and union types allow ad-hoc combination of types when needed. Both features work with pattern matching for safe, expressive branching on types.

---

## Macros

Simple includes a compile-time macro system to enable metaprogramming. Macros in Simple are programs that run at compile time to generate code (values, functions, types, or even identifiers) which is then compiled as part of the program. Macros help reduce boilerplate and enable domain-specific language features by letting you extend the language in limited ways.

### Key Characteristics

**Hygiene and Explicit Declarations**: Macros operate on the code abstract syntax tree (AST) to produce new code. Simple's macros are hygienic by default (they won't accidentally capture local variables unless intended), but unlike some macro systems, Simple requires macros to declare any new names (variables, functions, types) and their types that they introduce into the program. This makes the macro system IDE-friendly – development tools can know about macro-generated constructs ahead of time, avoiding the "magic code" problem where IDEs and linters are unaware of macro expansions. For example, if a macro generates a function `foo() -> i64`, the macro definition would specify that it introduces a function `foo` returning `Int`. This explicit naming scheme is similar to Swift's approach where macros must specify a naming pattern for expanded declarations. Declaring introduced names prevents collisions and allows tooling to track macro expansions.

### Defining Macros

Macros can be defined using a special keyword (for instance, `macro`), and they look like functions but are evaluated at compile time. For example:

```simple
macro define_counter(name: Ident):
    # This macro generates a mutable static counter with given name and two functions to access it
    gen_code:
        mut static {name}: i64 = 0

        fn {name}_increment():
            {name} = {name} + 1
            return {name}

        fn {name}_reset():
            {name} = 0
```

In this hypothetical macro, `Ident` is a type of macro input (an identifier). The macro `define_counter(X)` will produce a static `X: Int` and two functions `X_increment()` and `X_reset()`. The `{ ... }` syntax here illustrates splicing the provided identifier into generated code. The macro uses a `gen_code:` block to indicate it returns code to the compiler. All names introduced (`X`, `X_increment`, `X_reset`) are explicitly spelled out in the macro definition, so the compiler and IDE know about them. After this macro, you could write `define_counter(counter)` in your program, and it would expand to actual `counter`, `counter_increment`, `counter_reset` definitions at compile time.

### Macro Capabilities

Macros can generate:

- **Values/Expressions**: e.g., a macro that computes a constant at compile time (like a factorial of a constant, or embedding a file).
- **Functions or Methods**: generate function definitions. These could be stand-alone or within impl blocks, etc.
- **Types**: generate struct, class, enum definitions or implementations of traits for types.
- **Identifiers/Names**: create or transform identifiers. For instance, a macro could take a name `X` and produce a new identifier `make_X_widget` by concatenation – but such generated names must follow the declaration rules (e.g. macro must declare the pattern of naming it uses, like adding a prefix/suffix).

### Invocation

Using a macro is done by calling it like a function but with some syntactical marker. Some languages use a sigil (Rust uses `!` for macro invocations), or it might be contextually determined. For example, we might have:

```simple
define_counter(my_counter)
```

and the compiler recognizes `define_counter` is a macro and expands it. Macros may also be allowed as attributes or annotations on declarations (for example, `@auto_repr struct Foo: ...` could invoke a macro to auto-generate a repr method). The exact invocation model is designed such that the macro expansion happens at compile time before type checking the final code.

### Safety and Limits

Macros operate within the language's syntax and type system. They cannot arbitrarily break typing rules – the expanded code must still compile and type-check. Macros don't have unrestricted power to do I/O or arbitrary logic at compile time (unless specifically allowed through a controlled meta-programming API); typically they can use a subset of the language for computing code (like pure functions, etc.) or manipulate AST nodes provided as input.

### Examples

A simple example might be a macro to generate getters and setters for struct fields:

```simple
macro make_property(type_name: Ident, field: Ident, field_type: Type):
    gen_code:
        fn {field}() -> {field_type}:
            return self.{field}
        fn set_{field}(new_value: {field_type}):
            self.{field} = new_value
```

Then inside a impl block of a class/struct, you could write `make_property(Person, age, i32)` to generate an `age()` getter and `set_age(i32)` setter for `age` field. The macro explicitly introduces two methods, which the compiler can anticipate.

Macros in Simple aim to give you metaprogramming superpowers while keeping the language tooling-friendly and type safe. By requiring explicit declaration of introduced names and types, Simple ensures that even with macros, the structure of code remains transparent. This avoids pitfalls where one might call a macro-generated function that the IDE doesn't recognize – in Simple, the IDE/compiler know the macro will create that function (because the macro said so).

**Note**: Because macros run at compile time, they must be used with care – heavy computations in macros can slow compilation. Also, to avoid confusing code, macros are typically named or invoked in a way that's clear (often using a different syntax or annotation). Simple reserves certain sigils or keywords to denote macro use, so it's obvious when reading code that expansion is happening.

---

## Concurrency

Simple adopts a message-passing concurrency model inspired by Erlang's actor model. Instead of shared mutable threads, concurrency in Simple is achieved by spawning lightweight processes (actors) that communicate via immutable messages. This model greatly simplifies writing concurrent programs by eliminating data races and locking concerns, as each process has its own isolated state.

### Key Concurrency Primitives

**Processes (Actors)**: A process is an independent thread of execution (managed by the runtime, potentially as a green thread or fiber) that does not share memory with other processes. Processes are extremely lightweight, allowing many of them to run concurrently. You can think of a process as analogous to an Erlang process or an Akka actor, rather than an OS thread. Since processes do not share memory, all interaction must be done through messaging.

**spawn**: The `spawn` function is used to create a new process. You might call it with a function or lambda to execute in the new process:

```simple
let pid = spawn(fn():
    # child process code
    do_work()
    send(self(), :done)
)
```

The `spawn` call returns a process identifier (`pid`) which is a handle to communicate with that process. If you spawn a function (like by name), that function runs in the new process. You can also spawn an inline anonymous function or block, as shown. Each process has a unique id and an isolated mailbox for incoming messages.

**send**: The `send(pid, message)` function (or syntax) is used to send an asynchronous message to another process. In Erlang, the syntax is `Pid ! Message`; in Simple, we can use a function call `send(pid, msg)` or possibly an operator like `pid <- msg` for convenience. Sending a message is non-blocking – the sender continues immediately after sending. For example:

```simple
send(pid, "hello")
send(pid, Msg(data))    # send a Msg variant, possibly an enum
```

The message can be any immutable data: value types, immutable structs, enums, etc., but cannot be a mutable object (to ensure no shared state). Under the hood, the runtime will copy the message (deep-copy if necessary) to the receiver's mailbox so that messages are transferred immutably and atomically. This guarantees that the sender and receiver don't have a shared mutable object; they each have their own copy if it's a complex structure.

**receive**: A process waits for messages by using a `receive` block, which is similar to a pattern-matching `match` specifically on the mailbox. For example:

```simple
receive:
    case "ping":
        print "pong"
    case ("add", x, y):
        print "{x} + {y} = {x+y}"
    case Msg(data):
        handle_data(data)
    case _:
        print "Got something: {_}"
```

When a `receive` is executed, the process checks its mailbox for any message that fits one of the given patterns (patterns work like in `match`). The first message that matches is removed from the mailbox and the corresponding case executes. If no message matches any pattern, the process will block (pause) waiting for a matching message to arrive. This blocking on receive is the primary way a process waits for work. (Optionally, there could be a `receive ... after timeout:` clause to handle timeouts, similar to Erlang).

Inside a receive block, you can use pattern guards and complex patterns just like in a match. Mailbox ordering is preserved (first in, first out), but pattern matching can bypass messages that don't match — those remain in the mailbox for future receives. This is exactly how selective receive works in Erlang.

### Example: Ping-Pong

```simple
fn ping(pong_pid, count: i32):
    for i in range(count):
        send(pong_pid, "ping")
        # wait for pong
        receive:
            case "pong":
                print "Ping received pong"
    print "Ping finished"

fn pong():
    loop:                        # infinite loop (could be while true)
        receive:
            case "ping":
                print "Pong received ping"
                send(sender(), "pong")   # sender() gets PID of who sent the message
            case :done:
                print "Pong finished"
                break loop
```

Here, `ping` function sends "ping" messages and waits for "pong" replies repeatedly. The `pong` function (intended to run in its own process) loops, responding to each "ping" by printing and replying with "pong". If it receives a `:done` message (perhaps as an atom or a special enum variant), it breaks out and ends. To set this up:

```simple
let pong_pid = spawn(fn(): pong())
spawn(fn(): ping(pong_pid, count: 3))
# After sending pings, tell pong to stop:
send(pong_pid, :done)
```

The output might interleave as ping and pong messages are exchanged concurrently.

### Immutability in Concurrency

As noted, only immutable (or deeply copied) data is allowed in messages. This means there is no shared mutable state between processes, which eliminates a whole class of concurrency bugs. Each process can be thought of as owning its state, and communication only happens by sending copies of data. This approach follows Erlang/Elixir philosophy: "share nothing, communicate by messages".

### Synchronization and Ordering

If multiple messages are in the mailbox, receive chooses the first that matches a pattern. If you need to synchronize or order events, you do so by protocol design. For instance, you might send a request and then wait for a specific response message. Since each process handles one message at a time, this model naturally serializes access to a process's state (no two messages are processed simultaneously in one process).

### Failure Handling

In the style of Erlang, one could imagine a supervision system where processes can monitor or link to each other. If a process crashes (due to an unhandled exception), it could send a signal to a supervisor process that can take action (restart it, etc.). The Simple language at least provides primitives for robust concurrency, and a standard library module likely implements higher-level actor patterns and supervisors.

In summary, concurrency in Simple is about spawning isolated processes and communicating with messages. It leverages immutability for safety and pattern matching for expressiveness in message handling. This model scales from single-machine multi-threading to potentially distributed systems, as the abstraction of sending messages can, in principle, work across process boundaries or network boundaries. The result is a system where you can have hundreds of thousands of lightweight concurrent activities (like Erlang) without shared-state complexity.

---

## Waitless Effects and Stackless Coroutine Actors

Simple provides a specialized actor model optimized for high-performance, predictable execution: **stackless coroutine actors** with **waitless** message handlers. This model guarantees that message processing never blocks, enabling extremely efficient scheduling and predictable latency.

### The Waitless Effect

#### Definition of "Waiting"

For waitless code, we forbid anything that can stall progress of an actor:

- Blocking syscalls (synchronous file/network I/O, sleep, thread join, etc.)
- Explicit `await`, `receive`, or blocking locks
- Spinning loops or recursion that the compiler can't prove will terminate promptly

We call such operations **blocking effects**. A `waitless` function must not:

1. Perform any blocking effect directly
2. Call any function that might perform a blocking effect
3. Recurse (direct or indirect)
4. Contain unbounded loops

#### Syntax

Add a function effect modifier after the signature:

```simple
fn handle(msg: Msg) waitless:
    # guaranteed non-blocking
    ...
```

Or using attribute-style syntax:

```simple
@waitless
fn handle(msg: Msg):
    ...
```

**Meaning**: A `waitless` function is guaranteed by the compiler not to block or spin forever, under explicit, checkable rules.

#### Effect Classification

Every function receives a simple effect flag:

| Effect | Description |
|--------|-------------|
| `waitless` | Statically checked to be non-blocking and structurally finite |
| `may_block` | Default; can perform any operation |

**Rules**:

1. **Default**: Every function is `may_block` unless explicitly declared `waitless` (or inferred `waitless` by future extensions).

2. **Call rule**: A `waitless` function may only call:
   - Other `waitless` functions
   - Whitelisted intrinsics known to be non-blocking (pure math, local allocations, message send, etc.)
   
   Calling a `may_block` function from `waitless` code produces a compile-time error.

3. **Trait methods**: Trait method signatures can be tagged `waitless`:
   ```simple
   trait Handler:
       fn handle(msg: Msg) waitless
   ```
   Any implementation of a `waitless` trait method must itself be `waitless`. Calling a trait object method is allowed in `waitless` code only if the trait method is declared `waitless`.

4. **FFI / external functions**: All FFI functions are `may_block` by default. They must be explicitly annotated to be callable from `waitless` code:
   ```simple
   extern fn fast_random() waitless -> i64
   ```

### Compile-Time Rules for Waitless Functions

#### Forbidden Constructs

Inside a `waitless` function, the following are forbidden:

| Construct | Reason |
|-----------|--------|
| `await` | Suspends execution |
| `receive` | Blocks waiting for messages |
| Blocking I/O functions | All are `may_block` |
| Blocking locks/mutexes | Can stall indefinitely |
| Direct recursion | Function calls itself |
| Mutual recursion | Cycle between `waitless` functions |
| Unbounded loops | Cannot prove termination |

#### Loop Restrictions

Loops must be **statically finite**:

**Allowed**:
```simple
# Constant-bounded range
for i in 0 .. 100:
    process(i)

# Fixed-size array iteration
let items: [i64; 10] = ...
for elem in items:
    handle(elem)

# Compile-time constant bound
const MAX_ITERATIONS: i32 = 50
for i in 0 .. MAX_ITERATIONS:
    step(i)
```

**Disallowed** (in v1):
```simple
# Runtime-dependent bound - forbidden
while condition:
    ...

# Unknown iterator length - forbidden
for item in dynamic_list:
    ...

# Infinite loop - forbidden
loop:
    ...
```

**Simplest initial rule set**: In `waitless` functions, allow only `for i in 0 .. constN` and `for elem in fixed_size_array`. Ban `while`, `loop`, and all recursion entirely. This provides strong guarantees with straightforward static checking.

#### Data and Allocations

Inside a `waitless` function:

- **Local allocations** (stack, small heap) are allowed if they cannot block. If the GC is unpredictable, options include:
  - Disallow heap allocation in `waitless` entirely
  - Provide a "bump allocator" region guaranteed to be non-blocking and fast

- **Mutations** must be to local or actor-local state only (no global locks). This aligns with Simple's immutability-by-default philosophy.

#### Static Checking Algorithm

For each `waitless` function `f`:

1. **Scan body for forbidden constructs**:
   - If `await`, `receive`, `lock`, `sleep`, `while`, `loop`, or explicit recursion is found → reject

2. **Build call graph from `f`**:
   - For every call site in `f` (and transitive callees):
     - Verify callee is `waitless` or a whitelisted intrinsic

3. **Check loops**:
   - Verify each `for` loop has a statically-known upper bound

If any check fails: **compile-time error** with message indicating which `waitless` constraint was violated.

### Runtime Detection

Some properties cannot be fully proven at compile time:

| Issue | Detection Method |
|-------|------------------|
| Misclassified FFI/native calls | Runtime check or manual review |
| GC pauses / OS scheduler stalls | Cannot prevent; can only minimize/measure |
| Data-dependent loop bounds | Runtime limits / watchdog |
| Dynamically loaded plugins | Unknown effects at compile time |

#### Runtime Guard: TLS Context Flag

When entering a `waitless` function, the compiler/runtime sets a thread/actor-local flag:

```simple
# Pseudocode - compiler-generated
TLS.current_context = Context.Waitless
```

When exiting, the flag is restored. All blocking APIs in the runtime check this flag:

```simple
fn sleep(ms: i64):
    if TLS.current_context == Context.Waitless:
        panic("sleep() called from waitless context")
    # ... actual implementation
```

The same check applies to:
- Blocking I/O calls
- Lock acquisition that might block
- Blocking `receive`

**Build modes**:
- **Debug**: Hard panic on violation (fail-fast)
- **Release**: Options include panic, log + kill actor, or offload to blocking pool

#### Runtime Guard: Stack Depth Counter

Even with recursion forbidden, the runtime maintains a recursion-depth counter per thread/actor:

- On function entry: `depth++`
- On exit: `depth--`
- If `depth > threshold` → panic "excessive recursion"

This protects against FFI bypasses, unsafe code, or future language relaxations.

#### Runtime Guard: Time Slice Watchdog

Optionally, the scheduler can:

1. Track instruction count or wall-clock time per actor message handling
2. If a `waitless` handler exceeds a configured budget:
   - Log the violation
   - Preempt the handler (if preemption is implemented)
   - Kill and restart the actor (with supervision)

This doesn't contradict run-to-completion semantics at the language level but prevents one misbehaving handler from freezing the system.

### Stackless Coroutine Actor Specification

#### Actor Definition Syntax

```simple
actor Counter:
    state:
        value: i64 = 0

    on Inc(by: i64) waitless:
        self.value = self.value + by

    on Get(reply_to: Pid[i64]) waitless:
        send reply_to, self.value

    on Reset() waitless:
        self.value = 0
```

**Semantics**:

- `actor Name:` defines an actor type
- `state:` block declares actor-local fields (immutable by default; use `mut` if needed)
- `on MessageType(...) waitless:` defines message handlers
- Every handler must be `waitless` (by design for this actor kind)

#### Stackless and Run-to-Completion

For stackless coroutine actors:

1. Each incoming message is processed by calling the corresponding `on` handler
2. The handler:
   - Runs on the current execution stack
   - Must not suspend (`await`, `receive`, blocking API)
   - Must return to the runtime when done

There is **no coroutine continuation kept on the stack**:
- Multi-step behavior is modeled by storing state in `self` and returning
- The next message may depend on that state

This is "stackless" because:
- Logical coroutine progress is encoded in **explicit fields/enums** (state machines)
- Not in the call stack or suspended frames

#### Hidden Per-Actor Local ("Actor TLS")

Within an actor's `on` handler, `self` is implicitly available and points to the actor state. Implementation options:

**Option A: Normal parameter** (simplest):
```simple
# Compiler-generated signature
fn Counter_on_Inc(self: &mut CounterState, msg: Inc) waitless:
    self.value = self.value + msg.by
```

**Option B: TLS style**:
```simple
# At runtime, when actor is scheduled:
TLS.ACTIVE_ACTOR_STATE = pointer_to_actor_state

# Handlers access via self or hidden TLS lookup
```

Both appear identical from user code: you write `self.value`, `self.buffer`, etc.

#### Allowed Operations in Handlers

Inside `on ... waitless:` handlers:

**Allowed** (compile-time verified):
| Operation | Notes |
|-----------|-------|
| Local computation | Pure functions |
| Actor state access | `self.field` reads/writes |
| `send pid, msg` | Non-blocking |
| `spawn` new actors | Non-blocking |
| Logging, metrics | Assuming non-blocking implementations |
| Bounded loops | Per `waitless` rules |

**Forbidden** (compile-time error):
| Operation | Reason |
|-----------|--------|
| `receive` | Blocks waiting for messages |
| `await` | Suspends execution |
| Blocking I/O / locks / sleep | `may_block` operations |
| Recursion / unbounded loops | Cannot prove termination |

**Forbidden** (runtime guard via TLS):
- Any `may_block` API call when `TLS.current_context == Waitless`

#### Message Queue and Scheduling

Runtime responsibilities:

1. **Mailbox**: Each actor has a FIFO queue of messages

2. **Scheduler loop**:
   ```
   loop:
       actor = pick_actor_with_nonempty_mailbox()
       msg = actor.mailbox.pop()
       handler = lookup_handler(actor.type, msg.type)
       
       # Set TLS flags
       TLS.current_context = Context.Waitless
       TLS.current_actor = actor
       
       # Run handler
       handler(actor.state, msg)
       
       # Clear TLS flags
       TLS.current_context = Context.Normal
       TLS.current_actor = nil
   ```

3. **Optional monitoring**:
   - Track steps/time spent in handler
   - Preempt or flag if budget exceeded

The actor is **run-to-completion** per message: it doesn't yield to the scheduler voluntarily; it only returns when the handler finishes.

#### State-Machine Style Behavior

For coroutine-like multi-step processing, encode state explicitly:

```simple
enum ParserMode:
    ReadingHeader
    ReadingBody
    Done

actor StreamParser:
    state:
        mode: ParserMode = ParserMode.ReadingHeader
        buffer: Bytes = Bytes.empty()
        header: Option[Header] = None

    on Data(chunk: Bytes) waitless:
        match self.mode:
            case ReadingHeader:
                self.buffer->append(chunk)
                if header_complete(self.buffer):
                    self.header = Some(parse_header(self.buffer))
                    self.buffer = Bytes.empty()
                    self.mode = ParserMode.ReadingBody
            
            case ReadingBody:
                self.buffer->append(chunk)
                if body_complete(self.buffer, self.header):
                    self.mode = ParserMode.Done
                    send self.parent, ParseComplete(self.buffer)
            
            case Done:
                # Ignore further data or log warning
                pass

    on Reset() waitless:
        self.mode = ParserMode.ReadingHeader
        self.buffer = Bytes.empty()
        self.header = None
```

Each `on Data` call is a **single step** of the state machine:
- No waiting
- No stackful recursion into prior states
- All progress encoded in `mode`, `buffer`, and `header` fields

#### Spawning and Communicating with Actors

```simple
# Spawn an actor, get its Pid
let counter_pid = spawn Counter()

# Send messages (non-blocking)
send counter_pid, Inc(by: 5)
send counter_pid, Inc(by: 3)

# Request-response pattern using another actor or callback
actor Main:
    state:
        counter: Pid[Counter.Msg]

    on Start() waitless:
        self.counter = spawn Counter()
        send self.counter, Inc(by: 10)
        send self.counter, Get(reply_to: self.pid)

    on Int(value: i64) waitless:
        # Received response from Counter
        print "Counter value: {value}"
```

#### Error Handling for Violations

If something violates `waitless` rules at runtime:

| Violation | Response |
|-----------|----------|
| Blocking API called in waitless context | Panic or controlled error |
| Recursion limit exceeded | Panic with stack info |
| Handler exceeds time budget | Supervisor flags/kills actor |

In **debug mode**: Hard, loud failures so developers fix issues immediately.

In **release mode**: Configurable policy (panic, log, supervisor restart).

### Integration with Standard Actors

Simple supports both:

1. **Standard actors** (from the Concurrency section): Use `spawn`, `send`, `receive` with full flexibility including blocking operations

2. **Stackless coroutine actors** (this section): Use `actor` definition with `waitless` handlers for guaranteed non-blocking execution

You can mix both in the same system:

```simple
# Standard actor that can block
let worker_pid = spawn fn():
    loop:
        receive:
            case Job(data, reply_to):
                # Can do blocking I/O here
                let result = blocking_compute(data)
                send reply_to, Result(result)

# Stackless actor for fast coordination
actor Coordinator:
    state:
        workers: List[Pid]
        pending: Dict[RequestId, Pid]

    on Dispatch(job: Job, client: Pid) waitless:
        let worker = self.workers.next_available()
        let req_id = generate_id()
        self.pending[req_id] = client
        send worker, Job(job.data, reply_to: self.pid, req_id: req_id)

    on Result(data: Data, req_id: RequestId) waitless:
        let client = self.pending.remove(req_id)
        send client, Response(data)
```

### Summary

The waitless stackless coroutine actor model provides:

| Feature | Benefit |
|---------|---------|
| `waitless` effect | Compile-time guarantee of non-blocking execution |
| Static analysis | Catches blocking calls, recursion, unbounded loops |
| Runtime guards | TLS flag catches FFI/unsafe violations |
| Stackless design | No suspended frames; state machines in fields |
| Run-to-completion | Predictable scheduling, no preemption needed |
| Actor-local state | Safe mutation without locks |

**What's caught at compile time**:
- Direct waits (`await`, `receive`, blocking calls)
- Recursion (direct and mutual)
- Calls to `may_block` functions
- Unbounded loops

**What's caught at runtime**:
- Misbehaving FFI/native functions
- Excessive recursion depth (safety net)
- Handler timeout violations

**What cannot be fully prevented**:
- GC pauses / OS scheduler stalls
- Pathological data-dependent behavior
- Dynamically loaded code with unknown effects

---

## Futures and Promises

Simple provides TypeScript-style async/await built on top of the actor system for handling asynchronous computations.

### Future Type

A `Future<T>` represents an asynchronous computation that will eventually produce a value of type `T` or an error:

```simple
enum Future<T>:
    Pending       # Not yet started
    Running       # Currently executing
    Resolved(T)   # Completed successfully with value
    Rejected(Error)  # Completed with error
```

### Promise Type

A `Promise<T>` is the writable end of a Future, allowing you to resolve or reject it:

```simple
struct Promise<T>:
    # Internal shared state with the corresponding Future

    fn resolve(self, value: T):
        # Resolve the future with a value

    fn reject(self, error: Error):
        # Reject the future with an error
```

### Creating Futures

Create a new future/promise pair using `promise<T>()`:

```simple
let (future, promise) = promise<i64>()

# Later, resolve or reject
promise.resolve(42)
# or
promise.reject(Error("Something went wrong"))
```

### Async/Await Syntax

Functions can be marked `async` to return a Future and use `await` to wait for other Futures:

```simple
fn fetch_data() async -> Data:
    let response = await http_get("https://api.example.com")
    return parse(response)
```

The compiler transforms async functions into state machines:

```simple
# The above becomes approximately:
fn fetch_data() -> Future<Data>:
    # Returns a Future that, when polled:
    # 1. Calls http_get and awaits the response
    # 2. Parses the response
    # 3. Resolves with the parsed Data
```

**Important**: `await` can only be used inside `async` functions. Using `await` in a `waitless` context is a compile-time error.

### Future Combinators

Futures support several combinators similar to JavaScript Promises:

#### then - Transform Results

```simple
let future: Future<i64> = get_number()
let doubled: Future<i64> = future.then(\x: x * 2)
```

#### catch - Handle Errors

```simple
let future: Future<i64> = risky_operation()
let safe: Future<i64> = future.catch(\err: 0)  # Default to 0 on error
```

#### finally - Always Execute

```simple
let future: Future<Data> = load_data()
let with_cleanup: Future<Data> = future.finally(\: cleanup())
```

#### all - Wait for All

```simple
let futures: List<Future<i64>> = [get_a(), get_b(), get_c()]
let all_results: Future<List<i64>> = Future.all(futures)
# Resolves when ALL futures resolve, or rejects if ANY rejects
```

#### race - First to Complete

```simple
let futures: List<Future<i64>> = [slow_source(), fast_source()]
let first: Future<i64> = Future.race(futures)
# Resolves/rejects with the first future to complete
```

#### any - First Success

```simple
let futures: List<Future<i64>> = [try_a(), try_b(), try_c()]
let first_success: Future<i64> = Future.any(futures)
# Resolves with first success, rejects only if ALL reject
```

#### all_settled - Wait for All (No Short-Circuit)

```simple
enum SettledResult<T>:
    Fulfilled(T)
    Rejected(Error)

let futures: List<Future<i64>> = [a(), b(), c()]
let all: Future<List<SettledResult<i64>>> = Future.all_settled(futures)
# Always waits for all futures, never short-circuits on rejection
```

### Integration with Actors

Futures integrate naturally with the actor system:

```simple
actor DataService:
    state:
        cache: Dict<String, Data> = {}

    # Async handler (NOT waitless - can await)
    on FetchData(key: String, reply_to: Pid) async:
        if key in self.cache:
            send reply_to, self.cache[key]
        else:
            let data = await fetch_from_remote(key)
            self.cache[key] = data
            send reply_to, data
```

**Note**: Async handlers cannot be marked `waitless` since `await` is a blocking operation. Use standard actors for async operations and stackless coroutine actors for guaranteed non-blocking handlers.

### Request-Response Pattern

A common pattern for actor communication using Futures:

```simple
fn request<T>(pid: Pid, msg: Msg) async -> T:
    let (future, promise) = promise<T>()
    send pid, Request(msg, promise)
    return await future

# Usage
let result = await request(service_pid, GetData("key"))
```

---

## DSL Features

Simple is designed to be flexible enough to build internal Domain-Specific Languages (DSLs), drawing inspiration from Ruby's expressiveness. Two key features enable DSL creation: context blocks and `method_missing`.

### Context Blocks

A context block lets you change the method lookup context for a section of code, so that method calls can be interpreted relative to a specific object (like an implicit receiver). In Ruby, this is often done with `instance_eval` or passing a block to a DSL instance; Simple provides a dedicated syntax to make it clearer.

**Syntax**: `context <expr>:` introduces a new indentation block in which any method call (or property access) that is not otherwise defined will be sent to `<expr>` as the receiver. `<expr>` is evaluated to an object, and inside the block that object becomes the default context (`self` in Ruby terms). For example:

```simple
class HTMLBuilder:
    fn tag(name: String, content: String):
        print "<{name}>{content}</{name}>"

    fn method_missing(meth: Symbol, args: [Any], block: Fn):
        # If a method name isn't defined, assume it's an HTML tag
        let tag_name = meth.name    # get method name as string
        if block != nil:
            # If block given, use its content as inner HTML
            print "<{tag_name}>"
            block()    # execute block content (which presumably prints inner HTML)
            print "</{tag_name}>"
        else:
            # No block, treat args[0] as content string
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

In this contrived example, `context html:` means that calls inside the block, like `p "This is a DSL example."`, are looked up on the `html` object. If `HTMLBuilder` doesn't have a method `p`, the call triggers `method_missing` on that object. The `method_missing` in `HTMLBuilder` is implemented to handle arbitrary tag names: if a method isn't found, it treats the method name as an HTML tag (printing opening tag, content, closing tag). The `div:` line shows a block is provided to `div` (which goes to `method_missing`, sees a block, and prints a container tag). This ability to intercept undefined calls is powerful for building fluent DSLs.

### Method Missing

The `method_missing` feature is borrowed from Ruby: if an object receives a method call for a method it doesn't have, it can override a special hook named `method_missing` to handle the call dynamically. In Simple, a class can define `fn method_missing(name: Symbol, args: [Any], block: Fn) -> Any` and that will be invoked whenever an undefined method is called on an instance of that class.

This is extremely useful for DSLs, as it allows "commands" in the DSL to be handled without predefining every method. As shown above, `HTMLBuilder.method_missing` catches calls like `p`, `div`, `span` and interprets them. Another example: an ORM might use `method_missing` to handle dynamic query methods (e.g. `User.find_by_name("Alice")` could be caught by `method_missing` and translated to a database query).

**Using method_missing**:

```simple
class ConfigDSL:
    data: Map[String, String] = {}

    fn method_missing(key: Symbol, args: [Any], block: Fn):
        # Called when an undefined method is invoked
        if args.size == 1:
            # treat it as setting a configuration key
            data[key.name] = toString(args[0])
        elif args.size == 0 and block != nil:
            # treat it as a section: execute the block (which might contain more calls)
            block()
        else:
            print "Unknown config usage: {key}"

# Using the ConfigDSL
let config = ConfigDSL()
context config:
    database "postgres"
    host "localhost"
    port 5432
```

In this snippet, calls like `database "postgres"` call `method_missing` with name `:database` and args `["postgres"]`, resulting in storing `"postgres"` under key `"database"` in the map. If a block was provided and no args (like a section, e.g., `production: ...block...`), it simply executes the block (which in context would still refer to the same `config` object, so nested config categories can be built). The `method_missing` approach allows a very fluid DSL style where the config keys appear as if they were methods.

One should use `method_missing` with care, as it can make code less explicit. However, for DSLs and metaprogramming, it provides flexibility. In Simple, this mechanism is opt-in; if `method_missing` is not defined, an unknown method call results in a compile-time error (or runtime error if somehow invoked dynamically). We recommend DSL implementers to also provide a way to list supported "pseudo-commands" (document the DSL), and possibly implement a `responds_to_missing?(Symbol)` method (like Ruby's `respond_to_missing?`) for better introspection, although that's beyond the core spec.

### DSL Support Summary

Combining context blocks and `method_missing` (along with flexible syntax for method calls), Simple empowers the creation of internal DSLs:

- **No-Parentheses Calls**: as noted, you can omit parentheses for method calls at the statement level, which makes DSL statements look more like natural language or configuration. For example, `user.name "Alice"` could set a name, or `rotate 90` could be a graphics DSL command – both look cleaner without parentheses clutter. (Nested calls still require parentheses for unambiguous parsing.)

- **Named Arguments**: allow DSL methods to have keyword-like parameters that make the intent clear (e.g., `draw line, color: "red", thickness: 2`).

- **Blocks as Lambdas**: passing blocks (using the `\params:` syntax for trailing blocks) allows constructing tree-like or scoped DSL instructions, such as building HTML or scenes in a game engine.

- **Context / Implicit Receiver**: the `context` mechanism means inside a DSL block you don't have to repeatedly mention the DSL object. In a testing DSL, you might do `context test_suite: ...` then just write `expect x toEqual y` inside, which the `TestSuite` object's `method_missing` can handle.

- **Fluent Interfaces**: Although not explicitly mentioned above, Simple's flexible syntax also allows methods to be chainable (especially with the `->` functional update operator). A DSL can be designed where calls return `self` or new contexts to allow continuing the chain on new lines without extra punctuation.

All these features together enable writing code in Simple that reads almost like a custom language for your domain, without sacrificing static typing and IDE support. The macros system further complements DSLs by allowing generation of boilerplate or repetitive patterns behind the scenes, while the core context/missing-method features handle the front-facing syntax.

---

## Standard Library Overview (Brief)

The standard library of Simple (often referred to as the "std" lib) provides a broad collection of modules and functions to support development needs out of the box. It is designed to be comprehensive yet modular, so developers have a rich set of tools without needing numerous third-party libraries for basic tasks. Here's a brief overview of major components:

### Core Types and Utilities

Basic types like `Int`, `Float`, `Bool`, `Char`, `String`, etc., come with a suite of utility functions and methods. For example, strings support concatenation, slicing, searching, and formatting. There is likely a `StringBuilder` for efficient mutable string construction, even though strings themselves are immutable. Numerics have math functions (`sqrt`, `sin`, etc. in a `Math` module or as methods).

### Collections

The library provides generic collection types:

- `List[T]` (an immutable singly-linked list, and/or perhaps an array-based dynamic list type like `ArrayList`)
- `Vec[T]` (a contiguous growable array type, if differentiated from List)
- `Dict[K, V]` (hash map/dictionary)
- `Set[T]` (hash set)
- Possibly specialized collections like `Deque`, `TreeMap`/`TreeSet` for sorted data, etc.

These collections implement relevant traits like `Iterable`, `Sequence`, etc., allowing use of high-level algorithms. They come with functional-style methods (`map`, `filter`, `reduce`) as well as iteration support.

### Iteration and Generators

An `Iterator` trait is provided for types that can be iterated over. Comprehensions or generator functions might also be supported (e.g., a `yield` mechanism) to easily create iterators. The standard library contains utility iterators (range generation, lazy sequences).

### Concurrency and Actor Library

Building on the primitives `spawn`, `send`, `receive`, the std library likely includes higher-level concurrency constructs. For example, a `Mailbox` abstraction or channels (for typed communication), actor supervisors and pools, future/promises for async request-response patterns, etc. This might live in a `concurrent` or `actor` module.

### I/O and System

Facilities to interact with the outside world, such as:

- File I/O (`File` class or functions to read/write files, streams, support for binary and text modes)
- Networking (sockets, HTTP client perhaps, etc., likely in a `net` module)
- Command-line arguments and environment variables
- Timing (`sleep`, timers)

These are designed to work with the type and concurrency system (e.g., perhaps asynchronous I/O or at least the ability to spawn a process to handle I/O without blocking others).

### Utilities and Algorithms

Common algorithms for sorting, searching, etc., possibly in utility modules. For instance, a `sort(list)` function or a `list.sort()` method (with trait constraints like elements being `Comparable` or providing a comparator). Utility functions for tasks like JSON parsing, regular expressions (`regex` module), etc., might also be included.

### Standard Traits and Interfaces

The library defines many common traits:

- `Comparable` for ordering (with `<`, `==` operators possibly tied to it)
- `Printable`/`Display` for converting to string
- `Equatable` (though `==` might be available for all, struct vs class difference noted earlier)
- `Iterable`, `Iterator` as mentioned
- `Error` or `Exception` trait perhaps for error handling (the language might use enums like `Result` and exceptions possibly)

These provide a consistent interface for common operations.

### Memory and Performance

If needed, a `Unsafe` or low-level module might expose operations for manual memory management or interfacing with C, but given the high-level nature of Simple, this would be limited and clearly marked.

### Reflection/Introspection

There might be a `reflect` module to query type information at runtime, needed in some advanced scenarios or for certain DSL implementations.

### Math and Science Libraries

Beyond basic math in core, possibly extended libraries for big integers, big decimal, statistics, random number generation, etc.

### Date/Time

A module for dates, times, timezones, etc., as is common in standard libraries.

### Collections of Algorithms

Functional helpers like `map`, `filter`, `reduce` are available on collections (or as free functions). There may also be more advanced ones like `groupBy`, `partition`, etc., in the library for convenience.

### Error Handling

The standard library defines how errors are handled. Likely using `Result` enum for recoverable errors and possibly exceptions (class types subclassing an `Exception` class) for exceptions. The language might support a `try/except` (or `try/catch`) for exception handling, and the library provides various Exception classes (`IOError`, `NetworkError`, etc.).

### Concurrency Utilities

Besides actors, maybe things like atomic counters, locks (if ever needed for FFI or rare shared memory use), and thread pools (if using OS threads) might be provided.

It's important to note that the standard library is considered part of the language's specification, as it defines much of the runtime behavior and available tools (in many languages, the standard library is defined in tandem with the language spec). Simple's std library emphasizes immutability and safety (for instance, collections might prefer returning new modified collections rather than in-place modification, except for clearly mutable structures like a mutable Vector).

In summary, the standard library gives you everything you need to be productive: from data structures to I/O to concurrency frameworks, all working seamlessly with the language's features like traits, enums, and macros. It is the "batteries included" foundation on which you can build applications in Simple without reinventing the wheel for common functionalities. The combination of a strong, static type system with a powerful standard library makes programming in Simple both safe and convenient.

---

## Sources

- Bernd Klein, Python Indentation Principle – Python uses indentation to define code blocks (no braces), which Simple adopts for cleaner syntax.
- Ruby Style Guide – Emphasizes omitting parentheses in DSL method calls for readability and using named arguments for clarity.
- Wikipedia, Type Inference – Type inference relieves the programmer from annotating types the compiler can deduce.
- Stack Overflow (Julia) – Rationale for default immutability of structs: it encourages safer, faster code by default.
- Rust By Example – Pattern matching requires covering all cases and allows matching literal values, ranges, etc., similar to Simple's match.
- Rust By Example – Traits are collections of methods that can be implemented by any type (e.g., trait Animal for type Sheep), providing polymorphic behavior.
- Vinicius Stock, Write a simple DSL in Ruby – Demonstrates using method_missing in a DSL context to handle calls that aren't pre-defined in the interface.
- QuickBird Studios, Swift Macros – Example of macros requiring naming schemes for generated declarations to aid tooling and avoid conflicts.
- Fred Hebert et al., Erlang Concurrency – Erlang's model uses spawn to create processes and messages that are sent immutably to process mailboxes; Simple adopts this for safe concurrency.

