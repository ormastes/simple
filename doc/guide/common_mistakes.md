# Common Programming Mistakes in Simple
**Helpful Guide for Developers from Other Languages**

This guide helps you avoid common mistakes when transitioning to Simple from Python, Rust, Java, C++, TypeScript, and other languages.

---

## Python → Simple

### ❌ Using `def` instead of `fn`

```python
# Python
def add(a, b):
    return a + b
```

```simple
# Simple ✅
fn add(a, b):
    return a + b
```

**Error message:**
```
error: unknown keyword 'def'
  --> line 1:1
   |
 1 | def add(a, b):
   | ^^^

Suggestion: Use 'fn' to define functions in Simple, not 'def'

Help:
  Python:  def add(a, b):
  Simple:  fn add(a, b):
```

---

### ❌ Using `None` instead of `nil`

```python
# Python
return None
```

```simple
# Simple ✅
return nil
```

---

### ❌ Using `True`/`False` instead of `true`/`false`

```python
# Python
if True:
    print("yes")
```

```simple
# Simple ✅
if true:
    print("yes")
```

---

### ❌ Writing explicit `self.`

```python
# Python
class Point:
    def get_x(self):
        return self.x  # explicit self.
```

```simple
# Simple ✅
struct Point:
    x: i32

impl Point:
    fn get_x() -> i32:
        return x  # self is implicit!
```

**Note:** In Simple, `self` is implicit in method bodies. You don't write `self.`.

---

## Rust → Simple

### ❌ Using `let mut` instead of `var`

```rust
// Rust
let mut x = 5;
x = 10;
```

```simple
// Simple ✅
var x = 5  # mutable
x = 10
```

**Error message:**
```
error: unexpected identifier 'mut' after 'let'
  --> line 1:5
   |
 1 | let mut x = 5
   |     ^^^

Suggestion: Use 'var' for mutable variables, 'val' for immutable

Help:
  Rust:    let mut x = 5;
  Simple:  var x = 5     # mutable
           val y = 10    # immutable (preferred)
```

---

### ❌ Using `&mut self` parameter

```rust
// Rust
impl Point {
    fn update(&mut self, x: i32) {
        self.x = x;
    }
}
```

```simple
// Simple ✅
impl Point:
    me update(x: i32):  # 'me' keyword, self is implicit
        self.x = x      # Wait, self IS implicit, so:
        x = x           # Just use the field name!
```

**Correct version:**
```simple
impl Point:
    me update(new_x: i32):  # 'me' = mutable method
        x = new_x           # self.x is implicit
```

---

### ❌ Using lifetime annotations

```rust
// Rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

```simple
// Simple ✅
// No lifetime annotations! Use reference capabilities instead
fn longest(x: &str, y: &str) -> &str:
    if x.len() > y.len(): x else: y
```

**Note:** Simple uses reference capabilities (`mut`, `iso`, `&`) instead of Rust lifetimes.

---

### ❌ Using turbofish `::<T>`

```rust
// Rust
let v = vec.collect::<Vec<i32>>();
```

```simple
// Simple ✅
val v = vec.collect<Vec<i32>>()  # Direct <T>, no ::
```

---

## Java/C++ → Simple

### ❌ Using `public class`

```java
// Java
public class Point {
    private int x;
    private int y;
}
```

```simple
// Simple ✅
pub struct Point:
    x: i32
    y: i32
```

Or use `class` for OOP-style:
```simple
pub class Point:
    x: i32
    y: i32
```

---

### ❌ Using `void` for no return

```java
// Java
public void print(String message) {
    System.out.println(message);
}
```

```simple
// Simple ✅
pub fn print(message: String):  # No return type = void
    println(message)
```

**Warning when you write:**
```simple
fn print(message: String) -> ():  # Verbose!
    println(message)
```

**Message:**
```
warning: unnecessary return type annotation
  --> line 1:31
   |
 1 | fn print(message: String) -> ():
   |                               ^^

Suggestion: Omit the return type (-> Type) for void functions

Help: Return type can be inferred. Only specify when needed for clarity.
```

---

### ❌ Using `new` keyword

```java
// Java
Point p = new Point(1, 2);
```

```simple
// Simple ✅
val p = Point { x: 1, y: 2 }  # Struct literal syntax
```

---

### ❌ Using `this` instead of `self`

```java
// Java
public class Point {
    int x;
    public int getX() {
        return this.x;
    }
}
```

```simple
// Simple ✅
struct Point:
    x: i32

impl Point:
    fn get_x() -> i32:
        return x  # 'self' is implicit, no 'this'
```

---

### ❌ Using `template<T>` syntax (C++)

```cpp
// C++
template<typename T>
class Vector {
    T* data;
};
```

```simple
// Simple ✅
struct Vector<T>:  # Generic params after name
    data: *T
```

---

### ❌ Using `namespace` (C++)

```cpp
// C++
namespace math {
    int add(int a, int b) { return a + b; }
}
```

```simple
// Simple ✅
mod math:
    fn add(a: i32, b: i32) -> i32:
        return a + b
```

---

## TypeScript/JavaScript → Simple

### ❌ Using `function` keyword

```typescript
// TypeScript
function add(a: number, b: number): number {
    return a + b;
}
```

```simple
// Simple ✅
fn add(a: i32, b: i32) -> i32:
    return a + b
```

---

### ❌ Using `const` instead of `val`

```typescript
// TypeScript
const x = 5;
```

```simple
// Simple ✅
val x = 5  # Immutable (preferred)
```

---

### ❌ Using `let` for immutable values

```typescript
// TypeScript
let x = 5;  // Could be reassigned
```

```simple
// Simple ✅
val x = 5   # Immutable (preferred)
var y = 5   # Mutable (if needed)
```

**Warning when you write:**
```simple
let x = 5  # Legacy syntax
```

**Message:**
```
warning: 'let' is deprecated, use 'val' or 'var'
  --> line 1:1
   |
 1 | let x = 5
   | ^^^

Suggestion: Use 'val' (immutable) or 'var' (mutable)

Help:
  TypeScript:  let x = 5;
  Simple:      val x = 5   # immutable (preferred)
               var y = 5   # mutable
```

---

### ❌ Using `interface` instead of `trait`

```typescript
// TypeScript
interface Named {
    name: string;
}
```

```simple
// Simple ✅
trait Named:
    fn get_name() -> String
```

---

### ❌ Using arrow function `=>` in definitions

```typescript
// TypeScript
const add = (a: number, b: number) => a + b;
```

```simple
// Simple ✅
val add = \a: i32, b: i32: a + b  # Lambda uses backslash
```

---

## C-Style → Simple

### ❌ Using type-first declarations

```c
// C
int x = 5;
char* name = "Alice";
```

```simple
// Simple ✅
val x: i32 = 5          # Type after name
val name: String = "Alice"

// Or use type inference
val x = 5               # Inferred as i32
val name = "Alice"      # Inferred as String
```

---

### ❌ Using unnecessary semicolons

```c
// C
int x = 5;
printf("%d\n", x);
```

```simple
// Simple ✅
val x = 5              # No semicolon needed
println("{x}")         # No semicolon

// Semicolons only for same-line statements
val a = 1; val b = 2   # Multiple statements on one line
```

---

## Common Generic Mistakes

### ❌ Using explicit `self` parameter

**DON'T:**
```simple
impl Point:
    fn get_x(self) -> i32:  # ❌ Redundant self parameter
        return x
```

**DO:**
```simple
impl Point:
    fn get_x() -> i32:      # ✅ self is implicit
        return x
```

**Error message:**
```
warning: explicit 'self' parameter is redundant
  --> line 2:14
   |
 2 |     fn get_x(self) -> i32:
   |              ^^^^

Suggestion: Remove the 'self' parameter (it's implicit)

Help:
  The 'self' parameter is implicit in methods. Don't write it.

  Explicit:  fn get_x(self) -> i32:  # redundant
  Implicit:  fn get_x() -> i32:      # self is automatic
```

---

### ❌ Verbose return type when inference works

**VERBOSE:**
```simple
fn add(a: i32, b: i32) -> i32:  # Return type obvious from body
    return a + b
```

**CONCISE:**
```simple
fn add(a: i32, b: i32):  # Return type inferred ✅
    return a + b
```

**Warning message:**
```
warning: return type can be inferred
  --> line 1:23
   |
 1 | fn add(a: i32, b: i32) -> i32:
   |                        ^^^^^^^

Suggestion: Consider omitting return type (type inference works)

Help:
  Verbose:  fn add(a: i32, b: i32) -> i32: a + b
  Concise:  fn add(a: i32, b: i32): a + b  # return type inferred

  Only specify return type when:
  - The function body is complex
  - You want explicit documentation
  - Type inference fails or is ambiguous
```

---

### ❌ Missing colon before function body

```simple
# Wrong
fn foo()
    print("hello")
```

**Error:**
```
error: expected ':' before function body
  --> line 1:9
   |
 1 | fn foo()
   |         ^

Suggestion: Add ':' before the function body

Help:
  Missing: fn foo()
  Correct: fn foo():
```

---

### ❌ Using `[]` instead of `<>` for generics

**OLD (GLR):**
```simple
struct List[T]:  # Legacy syntax (still works)
    data: *T
```

**NEW (LL(1)):**
```simple
struct List<T>:  # ✅ Preferred syntax
    data: *T
```

**Warning message:**
```
warning: prefer angle brackets <> for generics
  --> line 1:13
   |
 1 | struct List[T]:
   |             ^^^

Suggestion: Use <> instead of [] for generics

Help:
  Old:     List[T]
  New:     List<T>  # industry standard (Rust/C++/Java/TypeScript)

  Both work, but <> is preferred for LL(1) parsing and
  matches industry standards.
```

---

### ❌ Semicolon after block closure

```simple
# Wrong
if x > 0: {
    print("positive")
};  # ❌ Unnecessary semicolon
```

**Error:**
```
warning: unnecessary semicolon after block
  --> line 3:2
   |
 3 | };
   |  ^

Suggestion: Remove semicolon after block closure

Help:
  Wrong:  if x > 0: { ... };
  Right:  if x > 0: { ... }

  Semicolons are only needed for same-line statements.
```

---

## Summary Table

| From | Wrong | Right (Simple) |
|------|-------|----------------|
| Python | `def foo():` | `fn foo():` |
| Python | `None` | `nil` |
| Python | `True`/`False` | `true`/`false` |
| Python | `self.x` | `x` (implicit) |
| Rust | `let mut x` | `var x` |
| Rust | `fn foo(&mut self)` | `me foo()` |
| Rust | `::<T>` | `<T>` |
| Java | `public class` | `pub class/struct` |
| Java | `void foo()` | `fn foo():` (no return type) |
| Java | `new Point()` | `Point {}` |
| Java | `this.x` | `x` (implicit) |
| C++ | `template<T>` | `struct Name<T>:` |
| C++ | `namespace foo` | `mod foo:` |
| TypeScript | `function foo()` | `fn foo():` |
| TypeScript | `const x` | `val x` |
| TypeScript | `interface I` | `trait I:` |
| C | `int x = 5;` | `val x: i32 = 5` or `val x = 5` |
| Any | `fn foo(self)` | `fn foo()` (self implicit) |
| Any | `-> ()` for void | (omit return type) |

---

## Tips for Success

### 1. **Embrace Immutability**
Use `val` by default, `var` only when mutation is needed:
```simple
val x = 5      # ✅ Preferred (immutable)
var y = 5      # Only when you need to mutate
```

### 2. **Trust Type Inference**
Specify types only when needed:
```simple
val x = 5                      # ✅ Type inferred as i32
val list = []                  # ⚠️ May need type hint
val list: List<i32> = []       # ✅ Explicit when ambiguous
```

### 3. **Remember: Self is Implicit**
In methods, you never write `self.`:
```simple
impl Point:
    fn get_x() -> i32:
        return x        # Not self.x!

    me set_x(new_x: i32):
        x = new_x      # Not self.x = new_x!
```

### 4. **Use Modern Generic Syntax**
Prefer `<>` over `[]`:
```simple
List<T>          # ✅ Modern, LL(1) compatible
List[T]          # ⚠️ Legacy (works but discouraged)
```

### 5. **Colons Matter**
Function and block definitions need `:`:
```simple
fn foo():        # ✅ Colon before body
if x > 0:        # ✅ Colon before block
match value:     # ✅ Colon before cases
```

---

## See Also

- [Language Comparison Guide](./language_comparison.md) - Detailed comparisons with Python, Rust, etc.
- [Type Inference Guide](./type_inference.md) - When to specify types
- [Memory Model](./memory_model.md) - Understanding `mut`, `iso`, and capabilities
- [Style Guide](./style_guide.md) - Simple best practices
