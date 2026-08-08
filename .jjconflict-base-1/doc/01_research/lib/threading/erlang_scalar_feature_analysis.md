# Scala & Erlang Features for Simpler Coding in Simple

Analysis of features from Scala and Erlang that could make Simple language more concise and ergonomic.

---

## Executive Summary

| Feature | Source | Impact | Effort | Recommendation |
|---------|--------|--------|--------|----------------|
| **Placeholder `_` in lambdas** | Scala | ⭐⭐⭐⭐⭐ | Low | **HIGH PRIORITY** |
| **Pattern matching in function args** | Erlang | ⭐⭐⭐⭐⭐ | Medium | **HIGH PRIORITY** |
| **Infix method calls** | Scala | ⭐⭐⭐⭐ | Low | Medium |
| **For-comprehensions** | Scala | ⭐⭐⭐⭐ | High | Consider |
| **Binary pattern matching** | Erlang | ⭐⭐⭐⭐ | High | Niche but powerful |
| **Pipe with placeholder** | Elixir | ⭐⭐⭐⭐ | Low | Already have `->` |
| **Guard clauses** | Erlang | ⭐⭐⭐⭐ | Medium | Good addition |
| **Zip generators** | Erlang | ⭐⭐⭐ | Medium | Nice to have |
| **Case classes** | Scala | ⭐⭐⭐⭐ | Medium | Data-first design |

---

## 1. Scala Features

### 1.1 Placeholder Syntax `_` in Lambdas ⭐⭐⭐⭐⭐

**The single most impactful feature for concise code.**

```scala
// Scala - placeholder syntax
nums.map(_ * 2)           // instead of: nums.map(x => x * 2)
nums.filter(_ > 0)        // instead of: nums.filter(x => x > 0)
nums.reduce(_ + _)        // instead of: nums.reduce((a, b) => a + b)
prices.map(_.toInt)       // method call on placeholder
```

**Proposed Simple Syntax:**
```simple
# Current Simple
nums.map(\x: x * 2)
nums.filter(\x: x > 0)
nums.reduce(\a, b: a + b)

# With placeholder (proposed)
nums.map(_ * 2)
nums.filter(_ > 0)
nums.reduce(_ + _)

# Method calls on placeholder
users.map(_.name)
users.filter(_.age > 18)
users.sort_by(_.created_at)
```

**Rules:**
1. Each `_` represents a different parameter (positional)
2. Can only use each `_` once per lambda
3. `_.method` calls method on the placeholder
4. Falls back to `\x:` syntax for complex cases

**Implementation:** Parser change - desugar `_` to lambda parameter.

---

### 1.2 Infix Method Calls (Optional Dots/Parens)

```scala
// Scala allows infix notation
list map double        // same as list.map(double)
1 to 10               // same as 1.to(10)
"hello" contains "ell" // same as "hello".contains("ell")
```

**Proposed Simple (conservative):**
```simple
# Already have pipeline, but consider:
users filter active    # reads naturally
1 to 10               # range (already exists as 1..10)
list contains x       # predicate

# Or keep dots but allow space before args:
users.filter active
list.contains x
```

**Recommendation:** Low priority - Simple's `->` pipeline already provides fluent chaining.

---

### 1.3 For-Comprehensions (Monadic Sugar)

```scala
// Scala for-comprehension
for {
  x <- xs
  y <- ys
  if x + y > 10
} yield (x, y)

// Desugars to:
xs.flatMap(x => ys.filter(y => x + y > 10).map(y => (x, y)))
```

**Proposed Simple:**
```simple
# List comprehension syntax (Python-style, simpler than Scala)
[(x, y) for x in xs, y in ys if x + y > 10]

# Or Erlang-style
[(x, y) | x <- xs, y <- ys, x + y > 10]

# For monadic operations (Option, Result), keep explicit:
xs.flat_map(\x: ys.filter(\y: x + y > 10).map(\y: (x, y)))
```

**Recommendation:** Add list comprehension syntax; defer full monadic for-comprehension.

---

### 1.4 Case Classes (Data Classes)

```scala
// Scala case class - auto-generates:
// - constructor, equals, hashCode, toString, copy, pattern matching
case class User(name: String, age: Int)

val u = User("Alice", 30)
u.copy(age = 31)
u match { case User(n, a) => ... }
```

**Proposed Simple:**
```simple
# Data class with auto-generated methods
data User:
    name: String
    age: Int

# Automatically provides:
# - Constructor: User("Alice", 30)
# - Field access: u.name, u.age
# - Equality: u1 == u2 (structural)
# - Copy with update: u.with(age: 31)
# - Pattern match: match u: case User(n, a): ...
# - Debug string: "{User name=\"Alice\" age=30}"
```

**Implementation:** Type system + code generation.

---

### 1.5 Extension Methods

```scala
// Scala 3 extension methods
extension (s: String)
  def words: List[String] = s.split(" ").toList
  def isBlank: Boolean = s.trim.isEmpty

"hello world".words  // List("hello", "world")
```

**Proposed Simple:**
```simple
extend String:
    fn words(self) -> Vec<String>:
        self.split(" ")
    
    fn blank(self) -> Bool:
        self.trim.empty

"hello world".words  # => ["hello", "world"]
```

**Status:** Already in the analysis doc as recommended feature.

---

### 1.6 Named and Default Arguments

```scala
def greet(name: String, greeting: String = "Hello") = s"$greeting, $name!"
greet("Alice")                    // "Hello, Alice!"
greet("Bob", greeting = "Hi")     // "Hi, Bob!"
greet(greeting = "Hey", name = "Carol")  // "Hey, Carol!"
```

**Proposed Simple:**
```simple
fn greet(name: String, greeting: String = "Hello") -> String:
    "{greeting}, {name}!"

greet("Alice")                    # "Hello, Alice!"
greet("Bob", greeting: "Hi")      # "Hi, Bob!"
greet(greeting: "Hey", name: "Carol")  # "Hey, Carol!"
```

**Implementation:** Function signature grammar change.

---

### 1.7 String Interpolation

```scala
val name = "Alice"
s"Hello, $name!"           // simple
s"Sum: ${1 + 2}"          // expression
f"Pi: $pi%.2f"            // formatted
raw"No \n escape"         // raw string
```

**Simple already has interpolation:**
```simple
name = "Alice"
"Hello, {name}!"           # simple
"Sum: {1 + 2}"            # expression (if supported)

# Consider adding:
f"Pi: {pi:.2f}"           # formatted (Python-style)
r"No \n escape"           # raw string
```

---

### 1.8 Lazy Evaluation

```scala
lazy val expensive = computeExpensive()  // evaluated on first access
```

**Proposed Simple:**
```simple
lazy expensive = compute_expensive()  # evaluated on first access

# Or as a type:
let expensive: Lazy<Int> = lazy compute_expensive()
expensive.get  # forces evaluation
```

---

## 2. Erlang Features

### 2.1 Pattern Matching in Function Heads ⭐⭐⭐⭐⭐

**Erlang's most powerful feature for concise, readable code.**

```erlang
%% Erlang - pattern matching in function definition
factorial(0) -> 1;
factorial(N) -> N * factorial(N - 1).

%% Multiple patterns with guards
area({circle, R}) -> 3.14159 * R * R;
area({rectangle, W, H}) -> W * H;
area({triangle, B, H}) -> 0.5 * B * H.

%% Pattern match on lists
sum([]) -> 0;
sum([H|T]) -> H + sum(T).
```

**Proposed Simple:**
```simple
# Pattern matching in function definition
fn factorial(0) -> Int:
    1
fn factorial(n: Int) -> Int:
    n * factorial(n - 1)

# Combined syntax with case (traditional):
fn factorial(n: Int) -> Int:
    match n:
        case 0: 1
        case _: n * factorial(n - 1)

# Combined syntax with | -> (Erlang-style, PREFERRED):
fn factorial(n: Int) -> Int:
    match n:
        | 0 -> 1
        | _ -> n * factorial(n - 1)

# Pattern match on data types
fn area(shape: Shape) -> Float:
    match shape:
        case Circle(r): 3.14159 * r * r
        case Rectangle(w, h): w * h
        case Triangle(b, h): 0.5 * b * h

# Pattern match on lists (if supported)
fn sum(lst: Vec<Int>) -> Int:
    match lst:
        case []: 0
        case [h, ...t]: h + sum(t)
```

**Key insight:** Erlang doesn't need `match` keyword - pattern is in the function head itself.

**Simpler proposal (Erlang-style):**
```simple
fn factorial:
    (0) -> 1
    (n) -> n * factorial(n - 1)

fn area:
    (Circle(r)) -> 3.14159 * r * r
    (Rectangle(w, h)) -> w * h
    (Triangle(b, h)) -> 0.5 * b * h
```

---

### 2.2 Guard Clauses

```erlang
%% Erlang guards
max(X, Y) when X > Y -> X;
max(X, Y) -> Y.

%% Multiple guards
classify(N) when N < 0 -> negative;
classify(N) when N == 0 -> zero;
classify(N) when N > 0 -> positive.
```

**Proposed Simple:**
```simple
# Guard clauses with 'when'
fn max(x: Int, y: Int) -> Int when x > y:
    x
fn max(x: Int, y: Int) -> Int:
    y

# Or inline guards in match
fn classify(n: Int) -> String:
    match n:
        case _ when n < 0: "negative"
        case 0: "zero"
        case _ when n > 0: "positive"

# Compact guard syntax
fn abs(n: Int) -> Int:
    | n < 0  -> -n
    | else   -> n
```

---

### 2.3 List Comprehensions with Multiple Generators

```erlang
%% Erlang list comprehension
[ {X, Y} || X <- [1,2,3], Y <- [a,b], X > 1 ].
%% Result: [{2,a},{2,b},{3,a},{3,b}]

%% Pythagorean triples
[ {A,B,C} || A <- lists:seq(1,N), 
             B <- lists:seq(A,N), 
             C <- lists:seq(B,N), 
             A*A + B*B == C*C ].
```

**Proposed Simple:**
```simple
# Multiple generators
[(x, y) for x in [1,2,3], y in ["a","b"] if x > 1]
# => [(2,"a"), (2,"b"), (3,"a"), (3,"b")]

# Pythagorean triples
[(a,b,c) for a in 1..n, b in a..n, c in b..n if a*a + b*b == c*c]

# Erlang-style syntax alternative
[(x, y) | x <- 1..3, y <- ["a","b"], x > 1]
```

---

### 2.4 Binary Pattern Matching ⭐⭐⭐⭐

**Unique Erlang feature for parsing binary data.**

```erlang
%% Parse IP packet header
<<Version:4, IHL:4, DSCP:6, ECN:2, 
  TotalLength:16, 
  Identification:16,
  Flags:3, FragmentOffset:13,
  TTL:8, Protocol:8, 
  HeaderChecksum:16,
  SourceIP:32, DestIP:32,
  Rest/binary>> = Packet.

%% Simple RGB parsing
<<R:8, G:8, B:8>> = Color.
```

**Proposed Simple:**
```simple
# Binary pattern matching (if Simple supports binary data)
match packet:
    case <<version:4, ihl:4, dscp:6, ecn:2,
           total_len:16, id:16,
           flags:3, frag_offset:13,
           ttl:8, protocol:8,
           checksum:16,
           src_ip:32, dst_ip:32,
           rest:binary>>:
        # use parsed fields

# Simple RGB
match color:
    case <<r:8, g:8, b:8>>:
        RGB(r, g, b)
```

**Recommendation:** High value for systems programming, but complex to implement. Consider as future feature.

---

### 2.5 Message Passing & Receive

```erlang
%% Erlang actor message handling
loop() ->
    receive
        {add, X, Y, From} ->
            From ! {result, X + Y},
            loop();
        stop ->
            ok
    end.
```

**Proposed Simple (already has actor model):**
```simple
# Already in Simple spec - verify syntax aligns
actor Calculator:
    fn receive:
        case Add(x, y, from):
            from ! Result(x + y)
            receive()
        case Stop:
            ()
```

---

### 2.6 Pipe Operator with Placeholder (Elixir)

```elixir
# Elixir pipe operator
"hello world"
|> String.upcase()
|> String.split()
|> Enum.map(&String.reverse/1)

# With capture operator
[1,2,3] |> Enum.map(&(&1 * 2))  # [2, 4, 6]
```

**Simple already has `->` pipeline:**
```simple
"hello world"
    ->up
    ->split
    ->map(\s: s.rev)

# With placeholder (proposed enhancement)
"hello world"
    ->up
    ->split
    ->map(_.rev)
```

---

### 2.7 Hot Code Reloading

Erlang's ability to update code without stopping the system. This is more of a runtime feature than syntax, but worth noting for Simple's actor model.

---

## 3. Combined Feature Priority Matrix

### Tier 1: High Impact, Low-Medium Effort (Implement First)

| Feature | Example | Notes |
|---------|---------|-------|
| **Placeholder `_`** | `nums.map(_ * 2)` | Single most impactful |
| **Default arguments** | `fn f(x: Int = 0)` | Common need |
| **Named arguments** | `f(name: "Alice")` | Improves readability |
| **Guard clauses** | `fn f(x) when x > 0:` | Cleaner than if-else |

### Tier 2: High Impact, Higher Effort

| Feature | Example | Notes |
|---------|---------|-------|
| **Pattern matching in fn heads** | `fn f(0) -> 1; fn f(n) -> n * f(n-1)` | Major expressivity gain |
| **List comprehensions** | `[x*2 for x in lst if x > 0]` | Very common pattern |
| **Data classes** | `data User: name, age` | Reduces boilerplate |
| **Extension methods** | `extend String: fn words...` | API extensibility |

### Tier 3: Nice to Have

| Feature | Example | Notes |
|---------|---------|-------|
| **Lazy values** | `lazy x = expensive()` | Optimization |
| **Infix methods** | `list contains x` | Readability |
| **Binary patterns** | `<<r:8, g:8, b:8>>` | Systems programming |
| **Zip generators** | `[x+y for x, y in zip(xs, ys)]` | Parallel iteration |

---

## 4. Concrete Syntax Proposals

### 4.1 Placeholder Lambda (Highest Priority)

```simple
# Grammar addition
lambda_expr := "\" params ":" expr
             | placeholder_expr

placeholder_expr := expr containing "_"
# Each _ becomes a parameter, left-to-right

# Examples
_.name              # \x: x.name
_ + 1               # \x: x + 1  
_ + _               # \x, y: x + y
_.method(arg)       # \x: x.method(arg)
f(_, fixed)         # \x: f(x, fixed)
```

### 4.2 Guard Clauses

```simple
# Option A: Erlang-style in function head
fn abs(n: Int) -> Int when n < 0: -n
fn abs(n: Int) -> Int: n

# Option B: In match expressions
match x:
    case n when n < 0: "negative"
    case 0: "zero"
    case n: "positive"

# Option C: Standalone guard syntax
fn classify(n: Int) -> String:
    | n < 0  -> "negative"
    | n == 0 -> "zero"
    | else   -> "positive"
```

### 4.3 List Comprehension

```simple
# Python-style (recommended - familiar)
[expr for pattern in iterable if condition]
[x * 2 for x in nums if x > 0]
[(x, y) for x in xs for y in ys]

# Dict comprehension
{k: v for (k, v) in items if v > 0}

# Set comprehension  
{x for x in items if predicate(x)}
```

### 4.4 Data Classes

```simple
# Minimal syntax
data Point(x: Int, y: Int)

# With methods
data User:
    name: String
    age: Int
    
    fn adult(self) -> Bool:
        self.age >= 18

# Auto-generates:
# - Constructor: User(name, age) or User(name: "Alice", age: 30)
# - Equality: == compares all fields
# - Copy: user.with(age: 31)
# - Pattern match: case User(n, a): ...
# - String: str(user) -> "User(name=\"Alice\", age=30)"
```

---

## 5. Implementation Roadmap

### Phase 1: Quick Wins (Parser Only)
1. **Placeholder `_` in lambdas** - High value, parser change only
2. **Default arguments** - Parser + minor codegen
3. **Named arguments** - Parser + call resolution

### Phase 2: Pattern Matching Enhancement
4. **Guard clauses in match** - Parser + match codegen
5. **List comprehensions** - Parser + desugar to map/filter

### Phase 3: Type System
6. **Data classes** - Type system + code generation
7. **Extension methods** - Type resolution changes

### Phase 4: Advanced (Optional)
8. **Pattern matching in function heads** - Major grammar change
9. **Binary pattern matching** - If binary types added
10. **Lazy values** - Runtime support needed

---

## 6. Code Comparison: Before and After

### Example 1: Transform and Filter

**Before (verbose):**
```simple
users
    .filter(\u: u.age >= 18)
    .map(\u: u.name)
    .sort_by(\n: n.len)
```

**After (with placeholders):**
```simple
users
    .filter(_.age >= 18)
    .map(_.name)
    .sort_by(_.len)
```

### Example 2: Reduce

**Before:**
```simple
nums.reduce(\acc, x: acc + x)
```

**After:**
```simple
nums.reduce(_ + _)
```

### Example 3: Conditional Function

**Before:**
```simple
fn factorial(n: Int) -> Int:
    if n == 0:
        1
    else:
        n * factorial(n - 1)
```

**After (with guards):**
```simple
fn factorial(n: Int) -> Int:
    | n == 0 -> 1
    | else   -> n * factorial(n - 1)
```

### Example 4: Data Extraction

**Before:**
```simple
struct Point:
    x: Int
    y: Int

fn make_point(x: Int, y: Int) -> Point:
    Point { x: x, y: y }

fn eq(p1: Point, p2: Point) -> Bool:
    p1.x == p2.x and p1.y == p2.y
```

**After (with data class):**
```simple
data Point(x: Int, y: Int)
# Constructor, equality, copy all auto-generated
```

### Example 5: List Comprehension

**Before:**
```simple
1_to_10
    .filter(\x: x % 2 == 0)
    .map(\x: x * x)
```

**After:**
```simple
[x * x for x in 1..10 if x % 2 == 0]
```

---

## 7. Summary: Top 5 Features to Add

| Rank | Feature | Syntax | Why |
|------|---------|--------|-----|
| 1 | **Placeholder `_`** | `_.name`, `_ + _` | Biggest conciseness gain |
| 2 | **List comprehension** | `[x*2 for x in lst]` | Universal pattern |
| 3 | **Guard clauses** | `when` or `\|` | Cleaner conditionals |
| 4 | **Data classes** | `data Point(x, y)` | Reduce boilerplate |
| 5 | **Default/named args** | `fn f(x = 0)` | API ergonomics |

---

## 8. References

- Scala Documentation: https://docs.scala-lang.org/
- Learn You Some Erlang: https://learnyousomeerlang.com/
- Elixir Getting Started: https://elixir-lang.org/getting-started/
- Scala Collections API: https://www.scala-lang.org/api/current/scala/collection/
- Erlang Reference Manual: https://www.erlang.org/doc/reference_manual/
