# Simple Language Syntax Quick Reference

**Last Updated:** 2026-01-24

A comprehensive reference for Simple's syntax features. All features listed here are **implemented and working**.

---

## Table of Contents

- [Variables](#variables)
- [Strings](#strings)
- [Numbers](#numbers)
- [Collections](#collections)
- [Slicing & Indexing](#slicing--indexing)
- [Comprehensions](#comprehensions)
- [Optional & Null Handling](#optional--null-handling)
- [Functions](#functions)
- [Pattern Matching](#pattern-matching)
- [Control Flow](#control-flow)
- [Operators](#operators)
- [Ranges](#ranges)

---

## Variables

```simple
# Immutable (preferred)
val name = "Alice"
let count = 42

# Mutable
var total = 0
let mut items = []

# Type annotations (optional in interpreter, required in compiler mode)
val name: text = "Alice"
var count: i64 = 0
```

---

## Strings

### String Interpolation (Default)

```simple
val name = "world"
val count = 42
print "Hello, {name}!"              # Hello, world!
print "Count: {count + 1}"          # Count: 43
print "Result: {compute()}"         # Expressions allowed
```

### Raw Strings (No Interpolation)

```simple
# Single quotes = raw string
val regex = '[a-z]+\d{2,3}'         # No escaping needed
val path = 'C:\Users\name'          # Backslashes are literal

# r"..." prefix also works
val pattern = r"no\escape"
```

### Typed String Literals

```simple
val config = "/etc/config.json"_file
val server = "192.168.1.1"_ip
val api = "https://api.example.com"_http
val endpoint = "127.0.0.1:8080"_sock
val pattern = "[a-z]+"_re           # Regex
```

---

## Numbers

### Integer Literals

```simple
val decimal = 1_000_000             # Underscores for readability
val hex = 0xFF5733                  # Hexadecimal
val binary = 0b1010_0101            # Binary
val octal = 0o755                   # Octal
```

### Float Literals

```simple
val pi = 3.14159
val avogadro = 6.022e23             # Scientific notation
val tiny = 1.5e-10
```

### Typed Numbers

```simple
val a = 42i32                       # i32
val b = 100u64                      # u64
val c = 3.14f32                     # f32
val d = 2.718f64                    # f64
```

### Unit Literals

```simple
val distance = 100_km               # Length
val duration = 2_hr                 # Time
val weight = 5_kg                   # Mass
val discount = 20_pct               # Percentage (stored as 0.2)
```

---

## Collections

### Arrays/Lists

```simple
val nums = [1, 2, 3, 4, 5]
val empty: [i64] = []
val mixed = [1, "two", 3.0]         # Interpreter mode
```

### Dictionaries

```simple
val person = {"name": "Alice", "age": 30}
val scores: {text: i64} = {}
```

### Sets

```simple
val unique = {1, 2, 3}
```

### Spread Operator

```simple
val a = [1, 2, 3]
val b = [0, ...a, 4]                # [0, 1, 2, 3, 4]

val d1 = {"a": 1}
val d2 = {**d1, "b": 2}             # {"a": 1, "b": 2}
```

---

## Slicing & Indexing

### Basic Indexing

```simple
val lst = [10, 20, 30, 40, 50]
lst[0]                              # 10 (first)
lst[2]                              # 30 (third)
```

### Negative Indexing

```simple
lst[-1]                             # 50 (last)
lst[-2]                             # 40 (second to last)
```

### Slicing

```simple
lst[1:4]                            # [20, 30, 40] (index 1 to 3)
lst[:3]                             # [10, 20, 30] (first 3)
lst[2:]                             # [30, 40, 50] (from index 2)
lst[:-1]                            # [10, 20, 30, 40] (all but last)
```

### Slice with Step

```simple
lst[::2]                            # [10, 30, 50] (every other)
lst[1::2]                           # [20, 40] (odd indices)
lst[1:5:2]                          # [20, 40] (slice with step)
lst[::-1]                           # [50, 40, 30, 20, 10] (reversed)
```

### String Slicing

```simple
val s = "Hello, World!"
s[0:5]                              # "Hello"
s[7:]                               # "World!"
s[-6:-1]                            # "World"
```

---

## Comprehensions

### List Comprehension

```simple
# Basic
val squares = [x * x for x in 0..10]

# With filter
val evens = [x for x in 0..20 if x % 2 == 0]

# With transformation and filter
val result = [x * 2 for x in items if x > 0]
```

### Dict Comprehension

```simple
# Basic
val squares = {x: x * x for x in 1..=5}
# {1: 1, 2: 4, 3: 9, 4: 16, 5: 25}

# With filter
val filtered = {k: v for k, v in items if v > 0}

# Transform keys
val upper = {k.upper(): v for k, v in data}
```

---

## Optional & Null Handling

### Safe Navigation (`?.`)

```simple
# Returns nil if any part is nil
user?.address?.city
user?.profile?.settings?.theme

# Safe method calls
result?.process()?.validate()

# Safe indexing
data?.items?[0]
```

### Null Coalescing (`??`)

```simple
# Provide default value
val name = user?.name ?? "Unknown"
val port = config["port"] ?? 8080
val theme = settings?.theme ?? "light"

# Chain with safe navigation
val city = user?.address?.city ?? "N/A"
```

### Combining `?.` and `??`

```simple
# Complete nil-safe access with default
val display = user?.profile?.display_name ?? user?.name ?? "Anonymous"
```

### Existence Check (`.?`)

The `.?` operator checks if a value is **present** (not nil AND not empty):

```simple
# Option types
opt.?                         # true if Some, false if None

# Collections
list.?                        # true if non-empty
dict.?                        # true if non-empty
set.?                         # true if non-empty

# Strings
str.?                         # true if non-empty string

# Primitives (always true - they are values)
num.?                         # true (0 is still a value)
flag.?                        # true (false is still a value)

# Negation patterns
not opt.?                     # true if None (replaces is_none())
not list.?                    # true if empty (replaces is_empty())
```

### Result with `.?`

```simple
# Result.ok returns Option, Result.err returns Option
result.ok.?                   # true if Ok (replaces is_ok())
result.err.?                  # true if Err (replaces is_err())

# Example
val r: Result<i32, text> = Ok(42)
if r.ok.?:
    print "Success: {r!}"
```

### No-Paren Method Calls

Methods with no arguments can be called without parentheses:

```simple
# These are equivalent
list.first()                  # with parens
list.first                    # without parens (Ruby-like)

# More examples
str.len                       # same as str.len()
str.trim                      # same as str.trim()
str.upper                     # same as str.upper()
list.last                     # same as list.last()

# Chaining without parens
text.trim.upper.split(",")    # split needs parens (has arg)
```

### Combining `.?` with No-Paren

```simple
# Check if first element exists
list.first.?                  # true if list has first element

# Check if trimmed string is non-empty
str.trim.?                    # true if trimmed result is non-empty

# Full pattern
if user?.profile?.tags.?:
    for tag in user!.profile!.tags:
        print tag.upper.trim
```

### Refactoring Patterns

| Verbose | Concise | Notes |
|---------|---------|-------|
| `opt.is_some()` | `opt.?` | Existence check |
| `opt.is_none()` | `not opt.?` | Negated existence |
| `result.is_ok()` | `result.ok.?` | `ok` returns Option |
| `result.is_err()` | `result.err.?` | `err` returns Option |
| `list.is_empty()` | `not list.?` | Empty = not present |
| `list.first().is_some()` | `list.first.?` | No-paren + existence |

---

## Functions

### Basic Functions

```simple
fn add(a: i64, b: i64) -> i64:
    a + b                           # Implicit return

fn greet(name: text):
    print "Hello, {name}!"
```

### Default Parameters

```simple
fn connect(host: text, port: i64 = 8080, timeout: i64 = 30):
    # port defaults to 8080, timeout to 30
    ...
```

### Named Arguments

```simple
connect("localhost", port: 3000)
connect(host: "example.com", timeout: 60, port: 443)
```

### Variadic Parameters

```simple
fn sum(numbers...):
    numbers.reduce(0, \a, b: a + b)

sum(1, 2, 3, 4, 5)                  # 15
```

### Lambda Syntax

```simple
# Short form
val double = \x: x * 2
val add = \a, b: a + b

# With type annotations
val parse = \s: text: s.to_int()

# Block form
val process = \x:
    val result = compute(x)
    result * 2
```

### Trailing Lambda

```simple
items.map \x: x * 2
items.filter \x: x > 0
items.each \item:
    print "Item: {item}"
```

---

## Pattern Matching

### Basic Match

```simple
match value:
    case 0:
        print "zero"
    case 1:
        print "one"
    case n:
        print "other: {n}"
```

### Pattern Guards

```simple
match value:
    case n if n < 0:
        print "negative"
    case n if n == 0:
        print "zero"
    case n if n > 0:
        print "positive"
```

### Destructuring Patterns

```simple
# Tuple destructuring
match point:
    case (0, 0):
        print "origin"
    case (x, 0):
        print "on x-axis at {x}"
    case (0, y):
        print "on y-axis at {y}"
    case (x, y):
        print "at ({x}, {y})"

# Struct destructuring
match person:
    case {name: n, age: a} if a >= 18:
        print "{n} is an adult"
    case {name: n}:
        print "{n} is a minor"
```

### Let Destructuring

```simple
let (x, y) = get_point()
let (first, second, ...rest) = items
let [a, b, c] = triple
let {name, age} = person
```

---

## Control Flow

### If/Else

```simple
if condition:
    do_something()
else if other_condition:
    do_other()
else:
    do_default()

# Expression form
val result = if x > 0: "positive" else: "non-positive"
```

### Chained Comparisons

```simple
# These are equivalent:
if 0 < x < 10:
    print "in range"

if 0 < x and x < 10:
    print "in range"

# Multiple chains work too
if 0 <= x <= y <= 100:
    print "valid range"
```

### For Loops

```simple
for item in items:
    process(item)

for i in 0..10:
    print i

for key, value in dict.items():
    print "{key}: {value}"
```

### While Loops

```simple
while condition:
    process()

while let Some(item) = iterator.next():
    process(item)
```

### With Statement (Context Managers)

```simple
with File.open("data.txt") as f:
    content = f.read()
# File automatically closed

with Connection.open(url) as conn:
    data = conn.fetch()
# Connection automatically closed

# Multiple resources
with File.open("in.txt") as input, File.create("out.txt") as output:
    output.write(input.read())
```

---

## Operators

### Arithmetic

```simple
a + b       # Addition
a - b       # Subtraction
a * b       # Multiplication
a / b       # Division
a % b       # Modulo
a ** b      # Power
```

### Comparison

```simple
a == b      # Equal
a != b      # Not equal
a < b       # Less than
a <= b      # Less or equal
a > b       # Greater than
a >= b      # Greater or equal
```

### Logical

```simple
a and b     # Logical AND
a or b      # Logical OR
not a       # Logical NOT
```

### Bitwise

```simple
a & b       # Bitwise AND
a | b       # Bitwise OR
a ^ b       # Bitwise XOR
~a          # Bitwise NOT
a << n      # Left shift
a >> n      # Right shift
```

### Assignment Operators

```simple
a += b      # a = a + b
a -= b      # a = a - b
a *= b      # a = a * b
a /= b      # a = a / b
a %= b      # a = a % b
a **= b     # a = a ** b
```

### Special Operators

```simple
# Functional update (reassignment sugar)
data->normalize()               # data = data.normalize()
data->filter(min: 0)->sort()    # Chainable

# Optional operators
x?.y        # Safe navigation
x ?? y      # Null coalescing
x.?         # Existence check (is present/non-empty)
```

---

## Ranges

### Exclusive Range (`..`)

```simple
0..10       # 0, 1, 2, ..., 9 (excludes 10)

for i in 0..5:
    print i     # 0, 1, 2, 3, 4
```

### Inclusive Range (`..=`)

```simple
0..=10      # 0, 1, 2, ..., 10 (includes 10)

for i in 1..=5:
    print i     # 1, 2, 3, 4, 5
```

### Range in Collections

```simple
# Create list from range
val nums = [for i in 1..=10: i]     # [1, 2, ..., 10]

# Check membership (stdlib method needed)
if (1..100).contains(x):
    print "valid"
```

---

## Not Yet Implemented

These features are **not available**:

| Feature | Workaround |
|---------|------------|
| Byte strings `b"..."` | Use array of bytes |
| For-else | Use flag variable |
| Pipeline `\|>` | Use method chaining or `->` |
| Elvis `?:` | Use `??` instead |

---

## See Also

- [doc/spec/generated/syntax.md](../spec/generated/syntax.md) - Auto-generated syntax spec
- [doc/guide/fn_lambda_syntax.md](fn_lambda_syntax.md) - Detailed function/lambda guide
- [doc/guide/coding_style.md](coding_style.md) - Coding conventions
- [CLAUDE.md](../../CLAUDE.md) - Quick syntax reference in project instructions
