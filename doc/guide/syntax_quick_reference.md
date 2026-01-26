# Simple Language Syntax Quick Reference

**Last Updated:** 2026-01-26

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
- [Pipeline Operators](#pipeline-operators)
- [Tensor & Matrix Operators](#tensor--matrix-operators)
- [Ranges](#ranges)
- [Resource Cleanup](#resource-cleanup)

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

Two syntaxes are supported. **Erlang-style `| ->` is preferred** (shorter):

```simple
# Preferred: Erlang-style (shorter, cleaner)
match value:
    | 0 -> "zero"
    | 1 -> "one"
    | _ -> "other"

# Traditional: case syntax (also valid)
match value:
    case 0: "zero"
    case 1: "one"
    case _: "other"
```

### Pattern Guards

```simple
# Preferred: | -> with guards
match value:
    | n if n < 0 -> "negative"
    | 0 -> "zero"
    | n if n > 0 -> "positive"

# Traditional: case with guards
match value:
    case n if n < 0: "negative"
    case 0: "zero"
    case n if n > 0: "positive"
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

## Pipeline Operators

Pipeline operators enable functional programming patterns and neural network composition.

### Pipe Forward (`|>`)

Pass value to function:

```simple
# x |> f is equivalent to f(x)
val result = 5 |> double |> square |> to_string
# Same as: to_string(square(double(5)))

# Data processing pipeline
val output = data
    |> preprocess
    |> validate
    |> transform
```

### Function Composition (`>>`, `<<`)

Create new functions by composition:

```simple
# f >> g means: λx. g(f(x))
val pipeline = normalize >> augment >> to_tensor
val result = pipeline(data)

# << is backward composition (like Haskell's .)
val same = to_tensor << augment << normalize
```

### Parallel (`//`)

Run operations in parallel:

```simple
# f // g runs both and returns tuple
val both = encode_audio // encode_video
val (audio, video) = both(raw_audio, raw_video)
```

### Layer Connect (`~>`)

Compose neural network layers with **dimension checking**:

```simple
# Dimension-checked pipeline
val model = Linear(784, 256) ~> ReLU() ~> Linear(256, 10)
# Type: Layer<[batch, 784], [batch, 10]>

# Compile-time error on mismatch:
val bad = Linear(784, 256) ~> Linear(128, 64)
# ERROR: output [batch, 256] != input [batch, 128]
```

### Pipeline Precedence (Low to High)

```
|>, ~>    (lowest - pipeline)
//        (parallel)
>>        (composition)
or, ||    (logical or)
and, &&   (logical and)
...       (other operators)
```

---

## Tensor & Matrix Operators

### Matrix Multiplication (`@`)

```simple
val C = A @ B           # Matrix multiply
# [M, K] @ [K, N] -> [M, N]

val batched = X @ W     # Batched matmul
# [batch, M, K] @ [K, N] -> [batch, M, N]
```

### Broadcast Operators (`.+`, `.-`, `.*`, `./`, `.^`)

Element-wise operations with broadcasting:

```simple
val result = A .+ B     # Broadcast add
val scaled = X .* 2.0   # Scalar broadcast
val powered = M .^ 2    # Element-wise power

# Broadcasting rules (NumPy-style):
# [3, 4] .+ [1, 4] -> [3, 4]  (1 broadcasts to 3)
# [3, 4] .+ [4]    -> [3, 4]  (missing dim = 1)
```

### Power Operators

```simple
# Outside math blocks: use **
val x = 2 ** 10         # 1024

# Inside m{} blocks: use ^
val formula = m{ x^2 + 2*x*y + y^2 }
```

### XOR Operator

```simple
val result = 5 xor 3    # Bitwise XOR: 6
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

## Resource Cleanup

### The Resource Trait

Resources like files, sockets, and threads implement the `Resource` trait:

```simple
trait Resource:
    fn close()              # Close and release the resource
    fn is_open() -> bool    # Check if still open
    fn resource_name() -> text  # Name for error reports
```

### defer Statement

Schedule cleanup to run at scope exit:

```simple
val file = File.open("data.txt")?
defer file.close()           # Runs when scope exits
# ... use file ...
# close() called automatically here
```

Multiple defers run in LIFO order:

```simple
val a = open_a()
defer close_a()  # Third

val b = open_b()
defer close_b()  # Second

val c = open_c()
defer close_c()  # First

# Order: close_c, close_b, close_a
```

### with Statement for Resources

Automatic cleanup with context managers:

```simple
# File automatically closed when block exits
with File.open("data.txt") as file:
    val content = file.read()
# file.close() called automatically

# Multiple resources
with File.open("in.txt") as input, File.create("out.txt") as output:
    output.write(input.read())
```

### Async with Statement

For async resources (network sockets, etc.):

```simple
async with await TcpStream.connect_str("127.0.0.1:8080") as stream:
    await stream.write_all(data)?
    val response = await stream.read()?
# stream.close() called automatically
```

### Leak Detection

Check for unclosed resources:

```simple
use core.resource_registry.ResourceRegistry

val leaks = ResourceRegistry.check_leaks()
if leaks.len() > 0:
    print ResourceRegistry.leak_report()
```

### LeakTracked Mixin

Add automatic tracking to custom resources:

```simple
use core.leak_tracked.LeakTracked

struct MyResource with LeakTracked:
    handle: i64

impl MyResource:
    static fn open() -> MyResource:
        var r = MyResource(handle: native_open())
        r._start_tracking("MyResource.open()")
        return r

    fn close():
        self._stop_tracking()
        native_close(self.handle)
```

---

## Not Yet Implemented

These features are **not available**:

| Feature | Workaround |
|---------|------------|
| Byte strings `b"..."` | Use array of bytes |
| For-else | Use flag variable |
| Elvis `?:` | Use `??` instead |

---

## See Also

- [doc/spec/generated/syntax.md](../spec/generated/syntax.md) - Auto-generated syntax spec
- [doc/guide/fn_lambda_syntax.md](fn_lambda_syntax.md) - Detailed function/lambda guide
- [doc/guide/resource_cleanup.md](resource_cleanup.md) - Resource management guide
- [doc/guide/coding_style.md](coding_style.md) - Coding conventions
- [doc/guide/dimension_errors_guide.md](dimension_errors_guide.md) - Dimension error reference
- [doc/design/pipeline_operators_design.md](../design/pipeline_operators_design.md) - Pipeline operator design
- [CLAUDE.md](../../CLAUDE.md) - Quick syntax reference in project instructions
