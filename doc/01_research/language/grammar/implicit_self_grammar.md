# Implicit Self Grammar Research

Research on languages with implicit self and how they distinguish mutable vs immutable methods.

## Goal
Find grammar that:
1. Makes `self` implicit (not written in parameter list)
2. Clearly distinguishes mutable vs immutable methods
3. Has clear syntax for static methods

---

## Language Survey

### 1. Ruby
**Self is implicit, methods are always mutable**

```ruby
class Point
  attr_reader :x, :y

  # Instance method - self is implicit
  def initialize(x, y)
    @x = x
    @y = y
  end

  # Instance method - reads self.x
  def magnitude
    Math.sqrt(@x * @x + @y * @y)
  end

  # Instance method - mutates self
  def translate!(dx, dy)
    @x += dx
    @y += dy
  end

  # Class method (static) - explicit self.
  def self.origin
    Point.new(0, 0)
  end
end
```

**Key Features:**
- ✓ `self` is implicit - never written in parameters
- ✓ `def self.method` for static methods - clear and explicit
- ✗ No distinction between mutable/immutable methods
- ✓ Convention: `!` suffix for mutating methods (not enforced)

---

### 2. Python
**Self is explicit but conventional**

```python
class Point:
    # Instance method - self is explicit parameter
    def __init__(self, x, y):
        self.x = x
        self.y = y

    # Instance method - self explicit
    def magnitude(self):
        return (self.x ** 2 + self.y ** 2) ** 0.5

    # Instance method - mutates self
    def translate(self, dx, dy):
        self.x += dx
        self.y += dy

    # Static method - decorator, no self
    @staticmethod
    def origin():
        return Point(0, 0)

    # Class method - receives cls
    @classmethod
    def from_tuple(cls, coords):
        return cls(coords[0], coords[1])
```

**Key Features:**
- ✗ `self` is explicit in parameter list (but convention, not enforced)
- ✓ `@staticmethod` decorator - very clear
- ✗ No mutable/immutable distinction
- ✓ First parameter convention is flexible

---

### 3. Scala
**Self is implicit in classes, methods are expressions**

```scala
class Point(var x: Double, var y: Double) {
  // Instance method - self (this) is implicit
  def magnitude: Double =
    math.sqrt(x * x + y * y)

  // Instance method - mutates this
  def translate(dx: Double, dy: Double): Unit = {
    x += dx
    y += dy
  }

  // Method with explicit result type
  def getX: Double = x
}

// Companion object - for "static" methods
object Point {
  def origin: Point = new Point(0, 0)

  def apply(x: Double, y: Double): Point = new Point(x, y)
}
```

**Key Features:**
- ✓ `self`/`this` is implicit - access fields directly
- ✓ Companion `object` for static methods - clear separation
- ✗ No mutable/immutable method distinction
- ✓ `def` keyword for all methods
- ✓ Methods are expressions (no return needed)

---

### 4. Rust (for comparison)
**Self is explicit, mutability is explicit**

```rust
struct Point {
    x: f64,
    y: f64,
}

impl Point {
    // Associated function (static) - no self
    fn new(x: f64, y: f64) -> Point {
        Point { x, y }
    }

    // Immutable method - &self explicit
    fn magnitude(&self) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }

    // Mutable method - &mut self explicit
    fn translate(&mut self, dx: f64, dy: f64) {
        self.x += dx;
        self.y += dy;
    }
}
```

**Key Features:**
- ✗ `self` is explicit parameter
- ✓ `&self` vs `&mut self` - clear mutability
- ✓ No self parameter = static method
- ✓ Compiler enforced mutability

---

### 5. JavaScript/TypeScript
**Self is implicit (this), methods mutable by default**

```typescript
class Point {
  x: number;
  y: number;

  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }

  // Instance method - this is implicit
  magnitude(): number {
    return Math.sqrt(this.x * this.x + this.y * this.y);
  }

  // Instance method - mutates this
  translate(dx: number, dy: number): void {
    this.x += dx;
    this.y += dy;
  }

  // Static method - static keyword
  static origin(): Point {
    return new Point(0, 0);
  }
}
```

**Key Features:**
- ✓ `this` is implicit - not in parameter list
- ✓ `static` keyword for static methods
- ✗ No mutable/immutable distinction
- ✓ Simple and familiar syntax

---

### 6. C++ (const methods)
**This is implicit, const methods enforce immutability**

```cpp
class Point {
  double x, y;

public:
  // Constructor
  Point(double x, double y) : x(x), y(y) {}

  // Static method
  static Point origin() {
    return Point(0, 0);
  }

  // Const method - cannot modify this
  double magnitude() const {
    return sqrt(x * x + y * y);
  }

  // Non-const method - can modify this
  void translate(double dx, double dy) {
    x += dx;
    y += dy;
  }

  // Const method
  double getX() const {
    return x;
  }
};
```

**Key Features:**
- ✓ `this` is implicit
- ✓ `const` suffix for immutable methods - compiler enforced
- ✓ `static` keyword for static methods
- ✓ Methods are non-const (mutable) by default
- ✓ `const` methods cannot call non-const methods

---

### 7. Nim
**Self is implicit, has method call syntax**

```nim
type Point = object
  x, y: float

# Procedure syntax - first param is implicit self
proc magnitude(p: Point): float =
  sqrt(p.x * p.x + p.y * p.y)

proc translate(p: var Point, dx, dy: float) =
  p.x += dx
  p.y += dy

# Static method - no self-like parameter
proc origin(): Point =
  Point(x: 0, y: 0)

# Usage:
var point = Point(x: 3, y: 4)
echo point.magnitude()      # Method call syntax
point.translate(1, 1)
```

**Key Features:**
- ✓ First parameter becomes implicit `self` in method call
- ✓ `var` parameter for mutable methods
- ✓ Regular parameter for immutable methods
- ✓ No special keyword for static (no self parameter)
- ✓ Unified function call syntax (UFCS)

---

## Grammar Options for Simple

### Option A: Ruby/Scala Style (def keyword variations)

```simple
impl Point:
    # Static method - prefix with 'static'
    static def new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - 'def' keyword, self implicit
    def magnitude() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)

    # Mutable method - 'mut def' keyword, self implicit
    mut def translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Pros:**
- ✓ `self` fully implicit
- ✓ `mut def` clearly indicates mutation
- ✓ `static def` clearly indicates static
- ✓ Clean and readable

**Cons:**
- ✗ Changes `fn` to `def`
- ✗ `mut def` is two keywords

---

### Option B: Method Type Keywords (val/let/fun)

```simple
impl Point:
    # Static method - 'fun' keyword (function, not method)
    fun new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - 'val' keyword, self implicit
    val magnitude() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)

    # Mutable method - 'let' keyword, self implicit
    let translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Pros:**
- ✓ `self` fully implicit
- ✓ `val`/`let` mirrors variable semantics
- ✓ `fun` for functions (static), `val`/`let` for methods
- ✓ Very concise

**Cons:**
- ✗ Overloads `val`/`let` meaning
- ✗ `fun` vs `fn` inconsistency

---

### Option C: Prefix Keywords (const/mut/static fn)

```simple
impl Point:
    # Static method - 'static' prefix
    static fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - 'const' prefix, self implicit
    const fn magnitude() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)

    # Mutable method - 'mut' prefix, self implicit
    mut fn translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Pros:**
- ✓ `self` fully implicit
- ✓ `const` familiar from C++
- ✓ `mut` already used in Simple
- ✓ `static` universally understood
- ✓ Keeps `fn` keyword

**Cons:**
- ✗ `const` might conflict with const variables
- ✗ Three different prefixes

---

### Option D: Suffix Modifiers (C++ style)

```simple
impl Point:
    # Static method - 'static' suffix
    fn new(x: f64, y: f64) -> Point static:
        return Point(x: x, y: y)

    # Immutable method - 'const' suffix, self implicit
    fn magnitude() -> f64 const:
        return sqrt(self.x * self.x + self.y * self.y)

    # Mutable method - no suffix, self implicit
    fn translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Pros:**
- ✓ `self` fully implicit
- ✓ `const` from C++ (familiar)
- ✓ Keeps `fn` keyword
- ✓ Mutable is default (no keyword)

**Cons:**
- ✗ Suffix syntax less common
- ✗ Return type vs modifier ordering

---

### Option E: Decorator + No Modifier (minimal)

```simple
impl Point:
    # Static method - decorator
    @static
    fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - default, self implicit
    fn magnitude() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)

    # Mutable method - decorator, self implicit
    @mut
    fn translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Pros:**
- ✓ `self` fully implicit
- ✓ Decorators are extensible
- ✓ Clean syntax
- ✓ Immutable is default (safe)

**Cons:**
- ✗ `@mut` less common than `mut` keyword
- ✗ Decorators for core language features

---

### Option F: Ruby-Inspired with Nim mutability

```simple
impl Point:
    # Static method - 'self.' prefix on name
    fn self.new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - no modifier, self implicit
    fn magnitude() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)

    # Mutable method - 'mut' prefix, self implicit
    mut fn translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Pros:**
- ✓ `self` fully implicit for instance methods
- ✓ `self.` prefix makes static methods obvious
- ✓ Ruby-inspired static syntax
- ✓ Immutable is default

**Cons:**
- ✗ `self.` in method name is unusual
- ✗ Might confuse with method calls

---

## Recommendations

### Option 1: Rust-Style (mut fn) - Consistency with Current Variables

```simple
impl Point:
    # Static method - 'static' keyword, no self
    static fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - 'fn' only (default), self implicit
    fn magnitude() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)

    fn get_x() -> f64:
        return self.x

    # Mutable method - 'mut' keyword, self implicit
    mut fn set_x(value: f64):
        self.x = value

    mut fn translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy

# Local variables (current syntax)
let x = 5           # Immutable
let mut count = 0   # Mutable
```

### Option 2: Scala-Style (var fn) - Shorter and Symmetric

```simple
impl Point:
    # Static method - 'static' keyword, no self
    static fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable method - 'val fn', self implicit
    val fn magnitude() -> f64:
        return sqrt(self.x * self.x + self.y * self.y)

    val fn get_x() -> f64:
        return self.x

    # Mutable method - 'var fn', self implicit
    var fn set_x(value: f64):
        self.x = value

    var fn translate(dx: f64, dy: f64):
        self.x += dx
        self.y += dy

# Local variables (new syntax to match)
val x = 5         # Immutable
var count = 0     # Mutable
```

---

## Detailed Comparison

### Option 1 Rationale (Rust-Style):

✓ **Consistent with current syntax** - already using `let`/`let mut`
✓ **No breaking change** - local variables stay the same
✓ **Familiar to Rust users** - `mut` keyword widely understood
✓ **One keyword** - `mut` means mutation everywhere
✓ **Safe default** - methods immutable unless `mut`

✗ **Verbose** - `let mut` is longer than `var`
✗ **Two keywords for locals** - `let` + `mut` modifier

### Option 2 Rationale (Scala-Style):

✓ **Shorter syntax** - `var` vs `let mut` (saves 4 characters)
✓ **Perfect symmetry** - `val` immutable everywhere, `var` mutable everywhere
✓ **Clear semantics** - variable-like keywords for both methods and variables
✓ **Familiar to Scala/Kotlin users** - very common pattern
✓ **Clean defaults** - can make `val fn` optional (just `fn`)

✗ **Breaking change** - must migrate all `let`/`let mut` to `val`/`var`
✗ **Method keywords look like variables** - `var fn` is unusual

### Syntax Rules:

**Option 1 (Rust-Style):**
```
static fn name(...) -> T     # Static method, no self
fn name(...) -> T            # Immutable method, self implicit
mut fn name(...) -> T        # Mutable method, self implicit

let name = value             # Immutable local
let mut name = value         # Mutable local
```

**Option 2 (Scala-Style):**
```
static fn name(...) -> T     # Static method, no self
val fn name(...) -> T        # Immutable method, self implicit
var fn name(...) -> T        # Mutable method, self implicit

val name = value             # Immutable local
var name = value             # Mutable local
```

### Option 2a (Scala-Style with Optional val):

Make `val fn` optional since immutable is default:

```simple
static fn name(...) -> T     # Static method, no self
fn name(...) -> T            # Immutable method (val fn implied)
var fn name(...) -> T        # Mutable method, explicit var

val name = value             # Immutable local (can also be implicit in some contexts)
var name = value             # Mutable local
```

---

## Complete Comparison Table

| Feature | Current | Option 1 (Rust) | Option 2 (Scala) | Option 2a (Short Scala) |
|---------|---------|-----------------|------------------|------------------------|
| **Methods** | | | | |
| Static | `fn new()` | `static fn new()` | `static fn new()` | `static fn new()` |
| Immutable | `fn get(self)` | `fn get()` | `val fn get()` | `fn get()` |
| Mutable | `fn set(mut self)` | `mut fn set()` | `var fn set()` | `var fn set()` |
| **Variables** | | | | |
| Immutable | `let x = 5` | `let x = 5` | `val x = 5` | `val x = 5` |
| Mutable | `let mut x = 5` | `let mut x = 5` | `var x = 5` | `var x = 5` |
| **Pros** | | | | |
| Brevity | ✗ verbose | ✗ `let mut` long | ✓✓ short | ✓✓✓ shortest |
| Symmetry | ✗ no pattern | ✓ `mut` everywhere | ✓✓✓ `val`/`var` everywhere | ✓✓ mostly symmetric |
| Migration | ✗ explicit self | ✓✓ easy (vars same) | ✗ must change vars | ✗ must change vars |
| Familiarity | Rust | Rust, Swift | Scala, Kotlin | Kotlin |
| Consistency | ✗ | ✓✓✓ | ✓✓ | ✓ |

---

## Real-World Examples

### Example 1: Counter Class

**Current (Explicit self):**
```simple
pub struct Counter:
    value: i32

impl Counter:
    fn new() -> Counter:
        return Counter(value: 0)

    fn get(self) -> i32:
        return self.value

    fn increment(mut self):
        self.value += 1

# Usage
let counter = Counter::new()
let mut value = counter.get()    # Immutable local
counter.increment()
```

**Option 1 (Rust-Style):**
```simple
pub struct Counter:
    value: i32

impl Counter:
    static fn new() -> Counter:
        return Counter(value: 0)

    fn get() -> i32:              # self implicit
        return self.value

    mut fn increment():           # self implicit, mutable
        self.value += 1

# Usage
let counter = Counter::new()
let mut value = counter.get()    # Same variable syntax
counter.increment()
```

**Option 2 (Scala-Style):**
```simple
pub struct Counter:
    value: i32

impl Counter:
    static fn new() -> Counter:
        return Counter(value: 0)

    val fn get() -> i32:          # self implicit, immutable
        return self.value

    var fn increment():           # self implicit, mutable
        self.value += 1

# Usage
val counter = Counter::new()
var value = counter.get()        # Changed to val/var
counter.increment()
```

**Option 2a (Short Scala):**
```simple
pub struct Counter:
    value: i32

impl Counter:
    static fn new() -> Counter:
        return Counter(value: 0)

    fn get() -> i32:              # Immutable (default)
        return self.value

    var fn increment():           # Mutable (explicit var)
        self.value += 1

# Usage
val counter = Counter::new()
var value = counter.get()        # val/var
counter.increment()
```

---

### Example 2: Point with Local Variables

**Option 1 (Rust-Style):**
```simple
impl Point:
    fn distance_to(other: Point) -> f64:
        let dx = self.x - other.x        # Immutable local
        let dy = self.y - other.y
        let dist_sq = dx * dx + dy * dy
        return dist_sq.sqrt()

    mut fn normalize():
        let mag = self.magnitude()       # Immutable local
        let mut scale = 1.0 / mag        # Mutable local
        if mag == 0.0:
            scale = 1.0
        self.x *= scale
        self.y *= scale
```

**Option 2 (Scala-Style):**
```simple
impl Point:
    val fn distance_to(other: Point) -> f64:
        val dx = self.x - other.x        # Immutable local
        val dy = self.y - other.y
        val dist_sq = dx * dx + dy * dy
        return dist_sq.sqrt()

    var fn normalize():
        val mag = self.magnitude()       # Immutable local
        var scale = 1.0 / mag            # Mutable local
        if mag == 0.0:
            scale = 1.0
        self.x *= scale
        self.y *= scale
```

**Option 2a (Short Scala):**
```simple
impl Point:
    fn distance_to(other: Point) -> f64:
        val dx = self.x - other.x        # Immutable local
        val dy = self.y - other.y
        val dist_sq = dx * dx + dy * dy
        return dist_sq.sqrt()

    var fn normalize():
        val mag = self.magnitude()       # Immutable local
        var scale = 1.0 / mag            # Mutable local
        if mag == 0.0:
            scale = 1.0
        self.x *= scale
        self.y *= scale
```

---

### Example 3: Short Form Methods

**Option 1:**
```simple
impl Point:
    fn get_x() -> f64: self.x
    fn get_y() -> f64: self.y
    mut fn set_x(v: f64): self.x = v
    mut fn set_y(v: f64): self.y = v
```

**Option 2:**
```simple
impl Point:
    val fn get_x() -> f64: self.x
    val fn get_y() -> f64: self.y
    var fn set_x(v: f64): self.x = v
    var fn set_y(v: f64): self.y = v
```

**Option 2a:**
```simple
impl Point:
    fn get_x() -> f64: self.x           # val fn implied
    fn get_y() -> f64: self.y
    var fn set_x(v: f64): self.x = v    # var explicit
    var fn set_y(v: f64): self.y = v
```

---

## Migration Impact

### Option 1 (Rust-Style) - Low Impact
```diff
# Methods: Remove self parameter
- fn get(self) -> i32:
+ fn get() -> i32:

- fn increment(mut self):
+ mut fn increment():

# Add static for constructors
- fn new() -> Counter:
+ static fn new() -> Counter:

# Variables: NO CHANGE
  let x = 5
  let mut count = 0
```

### Option 2/2a (Scala-Style) - High Impact
```diff
# Methods: Remove self parameter, add val/var
- fn get(self) -> i32:
+ val fn get() -> i32:     # or just: fn get() -> i32:

- fn increment(mut self):
+ var fn increment():

# Add static for constructors
- fn new() -> Counter:
+ static fn new() -> Counter:

# Variables: MUST CHANGE ALL
- let x = 5
+ val x = 5

- let mut count = 0
+ var count = 0
```

---

## Final Recommendation Matrix

Choose based on your priorities:

### Choose Option 1 (Rust-Style) if you want:
- ✓ **Minimal migration** - no variable syntax changes
- ✓ **Consistency with Rust** - leverage Rust developer familiarity
- ✓ **One keyword for mutation** - `mut` means mutation everywhere
- ✓ **Low risk** - smaller change to existing codebase

**Syntax:**
```simple
static fn / fn / mut fn
let / let mut
```

### Choose Option 2a (Short Scala) if you want:
- ✓ **Maximum brevity** - `var` vs `let mut` (saves 4 chars)
- ✓ **Perfect symmetry** - `val`/`var` for both methods and variables
- ✓ **Clean defaults** - immutable methods just use `fn`
- ✓ **Familiar to Scala/Kotlin users** - industry standard pattern

**Syntax:**
```simple
static fn / fn / var fn
val / var
```

### Decision Factors:

| Factor | Option 1 Winner | Option 2a Winner |
|--------|-----------------|------------------|
| Already have lots of `.spl` code | ✓ | |
| Want shortest syntax | | ✓ |
| Team knows Rust | ✓ | |
| Team knows Scala/Kotlin | | ✓ |
| Want perfect symmetry | | ✓ |
| Want minimal migration | ✓ | |
| Want modern style | | ✓ |

---

## References

**Scala Resources:**
- [Two Types of Variables | Scala Documentation](https://docs.scala-lang.org/overviews/scala-book/two-types-variables.html)
- [Scala val vs var | Medium](https://medium.com/@knoldus/scala-variables-var-vs-val-421c4928667)
- [A First Look at Scala Methods | Scala Documentation](https://docs.scala-lang.org/overviews/scala-book/methods-first-look.html)
- [Extension Methods | Scala 3 Documentation](https://www.scala-lang.org/api/3.7.1/docs/docs/reference/contextual/extension-methods.html)

**Erlang Resources:**
- [Erlang - Functions | TutorialsPoint](https://www.tutorialspoint.com/erlang/erlang_functions.htm)
- [Learn You Some Erlang - Syntax in Functions](https://learnyousomeerlang.com/syntax-in-functions)

**Key Insight from Research:**
- **Scala**: Uses `val`/`var` for variables, but all methods use `def` (no mutability distinction at method level)
- **Erlang**: Purely functional, all variables immutable, no OOP concepts
- **Rust**: Uses `let`/`let mut` for variables, `&self`/`&mut self` for methods
- **Proposed**: Combines best of both worlds with symmetrical keywords

---

## FINAL DECISION: Option B (fn/me) ✅

**Selected for LL(1) parsing compatibility:**

```simple
impl Point:
    static fn new(x: f64, y: f64) -> Point:  # Static method (no self)
    fn get_x(self) -> f64:                   # Immutable method
    me set_x(self, value: f64):              # Mutable method ('me' keyword)

val x = 5          # Immutable variable
var count = 0      # Mutable variable
```

**Why Option B:**
- ✓✓ Perfect LL(1) - completely disjoint FIRST sets
- ✓ `me` is short and semantic ("method that modifies me")
- ✓ `val`/`var` for variables matches Scala/Kotlin
- ✓ No lookahead needed - parser can decide in one token
- ✓ Keeps `fn` keyword consistent with functions

**Grammar:**
```
StaticMethod  ::= 'static' 'fn' NAME '(' params ')' ...
ImmutMethod   ::= 'fn' NAME '(' 'self' ',' params ')' ...
MutMethod     ::= 'me' NAME '(' 'self' ',' params ')' ...
ImmutVariable ::= 'val' NAME '=' expr
MutVariable   ::= 'var' NAME '=' expr
```

**FIRST Sets (Disjoint):**
- Methods: `{static, fn, me}`
- Variables: `{val, var}`
- No conflicts!

---

## Quick Reference Card

```
╔══════════════════════════════════════════════════════════════════════╗
║                    IMPLICIT SELF GRAMMAR OPTIONS                     ║
╚══════════════════════════════════════════════════════════════════════╝

┌─────────────────────────────────────────────────────────────────────┐
│ CURRENT (Explicit Self)                                             │
├─────────────────────────────────────────────────────────────────────┤
│  fn new() -> T                    # Static (no self)                │
│  fn get(self) -> i32              # Instance (immutable)            │
│  fn set(mut self, v: i32)         # Instance (mutable)              │
│                                                                       │
│  let x = 5                        # Immutable local                 │
│  let mut count = 0                # Mutable local                   │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│ OPTION 1: Rust-Style (Minimal Migration)                           │
├─────────────────────────────────────────────────────────────────────┤
│  static fn new() -> T             # Static (explicit keyword)       │
│  fn get() -> i32                  # Instance (self implicit)        │
│  mut fn set(v: i32)               # Instance (self implicit, mut)   │
│                                                                       │
│  let x = 5                        # Immutable local (NO CHANGE)     │
│  let mut count = 0                # Mutable local (NO CHANGE)       │
│                                                                       │
│  Keywords: static, mut                                              │
│  Migration Impact: LOW (only methods change)                        │
└─────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────┐
│ OPTION 2a: Scala-Style (Maximum Symmetry)                          │
├─────────────────────────────────────────────────────────────────────┤
│  static fn new() -> T             # Static (explicit keyword)       │
│  fn get() -> i32                  # Instance (immutable default)    │
│  var fn set(v: i32)               # Instance (mutable explicit)     │
│                                                                       │
│  val x = 5                        # Immutable local                 │
│  var count = 0                    # Mutable local                   │
│                                                                       │
│  Keywords: static, var, val                                         │
│  Migration Impact: HIGH (methods + variables change)                │
│  Symmetry: ★★★ Perfect (val/var everywhere)                        │
└─────────────────────────────────────────────────────────────────────┘

═══════════════════════════════════════════════════════════════════════

SELF ACCESS IN METHOD BODIES (same for both options):
  self.x              # Read field
  self.x = 5          # Write field (only in mut/var methods)
  self.method()       # Call method

RULES:
  ✓ self is IMPLICIT in parameter list (not written)
  ✓ self is EXPLICIT in method body (must write self.x)
  ✓ Static methods have NO self access
  ✓ Immutable methods CANNOT modify self
  ✓ Mutable methods CAN modify self

═══════════════════════════════════════════════════════════════════════
```
