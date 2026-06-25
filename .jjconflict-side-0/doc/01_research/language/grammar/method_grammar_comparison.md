# Method Grammar Comparison Across Programming Languages

Research on how different languages express static methods, mutable methods, and immutable methods.

## Current Simple Language Design

```simple
impl Point:
    # Static method - no self parameter
    fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable instance method
    fn get_x(self) -> f64:
        return self.x

    # Mutable instance method
    fn set_x(mut self, value: f64):
        self.x = value
```

## Proposed Alternative Design

```simple
impl Point:
    # Static method - explicit decorator
    @static
    fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable instance method - val keyword
    val get_x() -> f64:
        return self.x

    # Mutable instance method - let keyword
    let set_x(value: f64):
        self.x = value
```

---

## Language Comparison

### 1. Rust
**Philosophy:** Explicit borrowing and mutability

```rust
impl Point {
    // Associated function (static)
    fn new(x: f64, y: f64) -> Point {
        Point { x, y }
    }

    // Immutable borrow
    fn get_x(&self) -> f64 {
        self.x
    }

    // Mutable borrow
    fn set_x(&mut self, value: f64) {
        self.x = value;
    }
}
```

**Key Features:**
- ✓ Explicit `&self` vs `&mut self` - clear at call site and definition
- ✓ Static methods have no self parameter
- ✓ Compiler-enforced borrowing rules
- ✗ Verbose syntax with `&` symbols

---

### 2. Swift
**Philosophy:** Value semantics with explicit mutation

```swift
struct Point {
    var x: Double
    var y: Double

    // Static method
    static func origin() -> Point {
        return Point(x: 0, y: 0)
    }

    // Immutable method (default)
    func getX() -> Double {
        return x
    }

    // Mutable method - explicit 'mutating'
    mutating func setX(_ value: Double) {
        x = value
    }
}
```

**Key Features:**
- ✓ `static` keyword for static methods - very clear
- ✓ `mutating` keyword for methods that modify value types
- ✓ Methods are immutable by default (safe default)
- ✓ Applies to structs (value types), classes use references

---

### 3. Kotlin
**Philosophy:** Properties and functions with extension support

```kotlin
class Point(var x: Double, var y: Double) {
    companion object {
        // Static method via companion object
        fun create(x: Double, y: Double) = Point(x, y)
    }

    // Properties handle get/set automatically
    // val property = immutable
    val magnitude: Double
        get() = sqrt(x * x + y * y)

    // var property = mutable
    // Methods use 'fun' keyword - always mutable access to 'this'
    fun translate(dx: Double, dy: Double) {
        x += dx
        y += dy
    }
}
```

**Key Features:**
- ✓ Properties (`val`/`var`) separate from functions
- ✓ `companion object` for static methods (explicit scope)
- ✗ No built-in way to mark functions as non-mutating
- ✓ Clear distinction between data and behavior

---

### 4. Python
**Philosophy:** Decorators for special method types

```python
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    # Static method - decorator
    @staticmethod
    def origin():
        return Point(0, 0)

    # Class method - decorator
    @classmethod
    def from_tuple(cls, coords):
        return cls(coords[0], coords[1])

    # Regular instance method
    def get_x(self):
        return self.x

    # No distinction between mutating and non-mutating
    def set_x(self, value):
        self.x = value
```

**Key Features:**
- ✓ `@staticmethod` decorator - very explicit
- ✓ `@classmethod` for methods that receive the class
- ✗ No distinction between mutable/immutable methods
- ✓ Decorator pattern is pythonic and extensible

---

### 5. C#
**Philosophy:** Keywords for method modifiers

```csharp
class Point {
    public double X { get; set; }
    public double Y { get; set; }

    // Static method - 'static' keyword
    public static Point Create(double x, double y) {
        return new Point { X = x, Y = y };
    }

    // Instance method (can read/write)
    public double GetX() {
        return X;
    }

    // Instance method (mutating)
    public void SetX(double value) {
        X = value;
    }

    // Readonly struct methods (C# 8.0+)
    public readonly double Magnitude() {
        return Math.Sqrt(X * X + Y * Y);
    }
}
```

**Key Features:**
- ✓ `static` keyword for static methods - standard and clear
- ✓ `readonly` methods in structs (C# 8.0+) for non-mutating
- ✓ Properties handle get/set with clear syntax
- ✗ `readonly` method modifier is uncommon in most C# code

---

### 6. Scala
**Philosophy:** Object-oriented + functional, with objects for static

```scala
class Point(var x: Double, var y: Double) {
  // Instance method
  def getX: Double = x

  // Mutating method
  def setX(value: Double): Unit = {
    x = value
  }
}

// Companion object for "static" methods
object Point {
  def origin: Point = new Point(0, 0)

  def apply(x: Double, y: Double): Point = new Point(x, y)
}
```

**Key Features:**
- ✓ Companion objects provide static-like functionality
- ✓ `val` vs `var` for immutable/mutable data
- ✗ No syntax to mark methods as non-mutating
- ✓ Functional programming influence

---

### 7. D Language
**Philosophy:** const-correctness at method level

```d
struct Point {
    double x, y;

    // Static method
    static Point create(double x, double y) {
        return Point(x, y);
    }

    // Const method (cannot modify)
    double getX() const {
        return x;
    }

    // Mutable method
    void setX(double value) {
        x = value;
    }

    // Immutable method
    double magnitude() immutable {
        return sqrt(x * x + y * y);
    }
}
```

**Key Features:**
- ✓ `const` methods cannot modify the object
- ✓ `immutable` methods for deeply immutable types
- ✓ `static` keyword for static methods
- ✓ C++-style const correctness

---

## Analysis for Simple Language

### Option 1: Current Design (Rust-like)
```simple
fn static_method() -> Point:           # No self = static
fn immutable_method(self) -> f64:      # self = immutable
fn mutable_method(mut self):           # mut self = mutable
```

**Pros:**
- Already implemented
- Similar to Rust (proven design)
- Type is implicit, mutability explicit

**Cons:**
- Static methods not visually distinct
- `mut self` is a parameter modifier (not method-level)
- Less clear at a glance

---

### Option 2: Decorator + Keywords (Python/Swift-inspired)
```simple
@static
fn static_method() -> Point:           # @static decorator

val immutable_method() -> f64:         # val = immutable (self implicit)
    return self.x

let mutable_method(value: f64):       # let = mutable (self implicit)
    self.x = value
```

**Pros:**
- `@static` very explicit and clear
- `val`/`let` matches Simple's variable semantics
- Self is fully implicit in both cases
- Shorter, cleaner syntax
- `val` for values (read-only) aligns with functional programming
- `let` for bindings (can modify) is intuitive

**Cons:**
- `val` and `let` overloading (used for variables AND methods)
- Different from most mainstream languages
- May confuse: `val x = ...` (variable) vs `val method()` (function)

---

### Option 3: Explicit Keywords (C#/Swift-like)
```simple
static fn static_method() -> Point:    # static keyword prefix

fn immutable_method(self) -> f64:      # self = immutable (current)

mutating fn mutable_method(value: f64): # mutating keyword
    self.x = value
```

**Pros:**
- `static` is universally understood
- `mutating` is clear (from Swift)
- Keywords before `fn` follow common patterns

**Cons:**
- `mutating fn` is verbose
- Still requires `self` parameter for immutable

---

### Option 4: Suffix Modifiers (D-like)
```simple
fn static_method() static -> Point:    # static suffix

fn immutable_method(self) const -> f64: # const suffix
    return self.x

fn mutable_method(mut self, value: f64): # mut self (current)
    self.x = value
```

**Pros:**
- `const` is familiar from C++/D
- Keeps `fn` keyword consistent

**Cons:**
- Suffix syntax less common
- Mixes suffix and prefix modifiers

---

## Recommendation

### Best Option: Hybrid Approach (Option 2 Modified)

```simple
impl Point:
    # Static methods - use @static decorator
    @static
    fn new(x: f64, y: f64) -> Point:
        return Point(x: x, y: y)

    # Immutable methods - use fn with self (current design)
    fn get_x(self) -> f64:
        return self.x

    fn distance_to(self, other: Point) -> f64:
        let dx = self.x - other.x
        let dy = self.y - other.y
        return (dx * dx + dy * dy).sqrt()

    # Mutable methods - use fn with mut self (current design)
    fn set_x(mut self, value: f64):
        self.x = value

    fn translate(mut self, dx: f64, dy: f64):
        self.x += dx
        self.y += dy
```

**Rationale:**
1. **`@static` decorator** - Explicit, clear, Python-inspired, doesn't overload existing keywords
2. **Keep `fn` for all instance methods** - Consistent with Simple's existing syntax
3. **Keep `self` vs `mut self`** - Already implemented, works well, Rust-proven
4. **Don't overload `val`/`let`** - These are for variables, not methods

**Why NOT use `val`/`let` for methods:**
- Confusing: `val x = 5` (immutable variable) vs `val method()` (immutable function?)
- `val` in Kotlin/Scala means "immutable property", not "immutable method"
- Better to keep `val`/`let` for their current purpose (variable binding)

**Final Syntax:**
```simple
@static fn name(...) -> T:    # Static method
fn name(self, ...) -> T:      # Immutable instance method
fn name(mut self, ...) -> T:  # Mutable instance method
```

This gives you:
- ✓ Clear static method marking with `@static`
- ✓ Explicit mutability with `mut self`
- ✓ No keyword overloading
- ✓ Familiar to Python users (`@decorator`)
- ✓ Familiar to Rust users (`mut self`)
- ✓ Clean and consistent
