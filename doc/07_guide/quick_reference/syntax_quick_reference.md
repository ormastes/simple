# Simple Language Syntax Quick Reference

**Last Updated:** 2026-05-29

A concise reference for the canonical public Simple syntax. Legacy or parser-compatibility forms are called out explicitly instead of being presented as current style.

**See also:** [Grammar keyword reference](../../06_spec/app/compiler/modules/grammar/keyword_reference.md) — keyword/status tables generated from the grammar registry.

---

## Table of Contents

- [Variables](#variables)
- [Short Grammar](#short-grammar)
- [Type & Function Aliases](#type--function-aliases)
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
- [Traits](#traits)
- [Visibility & Friend Access](#visibility--friend-access)

---

## Short Grammar

Simple supports compact expression forms that are intended to replace boilerplate,
not clarity. Prefer them for small, local, single-expression transformations:

```simple
fn double(x: i64) -> i64: x * 2
items.map(_ * 2)
items.zip(other).map(_1 + _2)
items.map(\_: 0)  # canonical compact form for ignored callback arguments
words.map(&:len)
[for x in items if x > 0: x * x]
user?.name ?? "Anonymous"
```

Runtime notes:

- `|>` pipe-forward and `>>` composition work in interpreter mode, including placeholder-lambda forms (`5 |> (_1 * 3)`). Native (compiled) support must still be proven with `SIMPLE_NO_STUB_FALLBACK=1`.
- `:=` is documented as a walrus-style `val` shorthand in older guidance, but current executable coverage does not prove the actual token. Use `val name = expr` until parser/runtime tests pass.
- Keep `\_:` for constant callbacks that must still be functions, such as `headers.map(\_: "---")`; replacing them with the constant expression would change the value passed to the higher-order call.
- Use explicit lambdas or helper functions once the expression has side effects, nested decisions, or non-obvious runtime behavior.

---

## Variables

```simple
# Immutable (preferred)
val name = "Alice"
val count = 42

# Mutable
var total = 0
var items = []

# Type annotations (optional in interpreter, required in compiler mode)
val name: text = "Alice"
var count: i64 = 0
```

---

## Type & Function Aliases

Create alternative names for existing types and functions. Useful for:
- **API evolution** (keep old names while transitioning)
- **Convenience** (shorter names for frequently-used items)
- **Compatibility** (platform-specific naming)

### Function Alias

**Status:** ⚠️ **Parser structure exists, runtime implementation incomplete**

```simple
# Syntax (not yet working in runtime):
fn println = print
fn each = iter

# Current workaround (use delegation):
fn println(msg):
    print(msg)
```

### Type Alias

```simple
# Simple type alias (using 'type' keyword)
type Point2D = Point
type StringList = List<text>
type ErrorCode = i64

# Generic type aliases
type IntList = List<i64>
type StringMap<V> = Map<text, V>

# Complex type aliases
type Result<T> = Option<T>
type Handler = fn(Event) -> ()
```

**Generic type arg parsing** — calling static methods on a fully-instantiated
generic type (`Map<text, i64>.new()`) now parses correctly in interpreter mode
as of 2026-05-29. The `<…>` is recognised as type arguments, not comparison
operators, when immediately followed by `.`:

```simple
val m = Map<text, i64>.new()         # previously failed to parse
val s = Set<text>.new()
val v = Vec<Point>.with_capacity(16)
```

### Class Alias

**Note:** `alias` creates an alternative **name** for an existing class. It is not inheritance. See [Not Part of Simple's Design](#not-part-of-simples-design) for the supported alternatives.

```simple
# Class/struct alias (using 'alias' keyword)
alias Optional = Option
alias Vec = Vector

# With visibility
pub alias PublicPoint = InternalPoint

# Generic class alias
alias IntSet = Set<i64>
```

### Deprecation Pattern

```simple
# Mark old API as deprecated, provide alias to new one
@deprecated("Use new_func instead")
fn old_func = implementation

fn new_func = old_func  # Non-deprecated alias

# Usage generates warning: "old_func is deprecated. Use new_func instead"
```

**Note:** Aliases are resolved at compile-time to their targets. No runtime overhead.

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

### `int(text)` Semantics (Task #118)

`int(text)` is a **total function** — it never errors, in interpret mode or
compiled mode. It skips leading whitespace, an optional `+`/`-` sign, then
parses the longest run of leading decimal digits and stops at the first
non-digit. If no digits are found at all, the result is `0`.

| Input | Result | Why |
|-------|--------|-----|
| `int("42")` | `42` | plain integer |
| `int("4.2")` | `4` | parses leading digits, stops at `.` (truncation) |
| `int("abc")` | `0` | no leading digits |
| `int("")` | `0` | no leading digits |
| `int(" 42 ")` | `42` | leading/trailing whitespace ignored |
| `int("-7")` | `-7` | leading sign honored |

This matrix is identical across all execution paths: the flat-AST interpreter
(`eval_int_parse_lenient` in `eval_builtins.spl`), the Rust seed's tree-walk
interpreter (`parse_int_lenient` in `interpreter_call/builtins.rs`), and both
compiled backends (`cranelift_codegen_adapter.spl`'s `cl_translate_cast` and
`codegen/instr/basic_ops.rs`), which route through the shared C-runtime
`rt_string_to_int()` (strtoll-based). The compiled-backend assertions above
require redeploying `bin/release/<triple>/simple` from a rebuilt bootstrap to
take effect for the self-hosted binary; the interpreter-mode assertions are
correct today.

If you need to *detect* garbage input instead of silently coercing it to `0`,
use the checked alternative: `text.parse_int()` returns `Option<i64>`
(`None` on any non-numeric or partially-numeric input), typically used as
`s.trim().parse_int() ?? -1` (see `src/lib/common/text.spl`'s `parse_i64`).

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

### Array Methods (Interpreter)

`map`, `filter`, `flat_map`, `any`, `all`, and `enumerate` are available on
arrays in interpreter mode as of 2026-05-29. Use short-grammar placeholders or
explicit lambdas:

```simple
val nums = [1, 2, 3, 4, 5]
nums.map(_ * 2)                     # [2, 4, 6, 8, 10]
nums.filter(_ > 2)                  # [3, 4, 5]
nums.any(_ > 4)                     # true
nums.all(_ > 0)                     # true
nums.flat_map(x => [x, x * 10])    # [1, 10, 2, 20, ...]
nums.enumerate()                    # [(0, 1), (1, 2), ...]
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

### Bitfield Slicing (`int.bits[lo..hi]`)

Read or write a contiguous bit range on an integer using `.bits[lo..hi]`,
where `lo` is the inclusive low bit and `hi` is the exclusive high bit
(field width is `hi - lo`).

```simple
val state = 0xDEADBEEF
state.bits[24..32]                  # 0xDE  (top byte)
state.bits[0..8]                    # 0xEF  (low byte)
state.bits[4..8]                    # 0xE   (4-bit nibble)

var word = 0x12345600
word.bits[0..8]  = 0xEF             # word == 0x123456EF
word.bits[24..32] = 0xAB            # word == 0xAB3456EF

# Augmented assigns (Phase 2) — arithmetic only:
var counter = 0
counter.bits[0..8] = 0x10
counter.bits[0..8] += 5             # counter.bits[0..8] == 0x15
counter.bits[0..8] -= 1             # 0x14
counter.bits[0..8] *= 2             # 0x28
counter.bits[0..8] /= 4             # 0x0A
counter.bits[0..8] %= 3             # 0x01
```

Desugars at parse time to plain shift+mask:

| Sugar                          | Lowering                                                      |
|--------------------------------|---------------------------------------------------------------|
| `x.bits[lo..hi]`               | `(x >> lo) & ((1 << (hi - lo)) - 1)`                          |
| `x.bits[lo..hi] = v`           | `x = (x & ~(mask << lo)) \| ((v & mask) << lo)`               |
| `x.bits[lo..hi] <op>= v`       | `x = clear \| ((((x >> lo) & mask) <op> v) & mask) << lo`     |

Notes:
- The source value of a write is masked to the field width — bits above
  the field cannot bleed into adjacent fields. The same final `& mask`
  applies to augmented forms, so e.g. `+= 1` on a saturated field wraps
  the field to 0 without disturbing the next field up.
- Inclusive ranges (`bits[0..=7]`) are accepted and equivalent to
  `bits[0..8]`.
- Supported augmented ops are `+=`, `-=`, `*=`, `/=`, `%=` — the same
  set the language already defines on integers. Bitwise augmented forms
  (`&=`, `|=`, `^=`) are NOT supported — the language has no token for
  them. Suspend forms (`~=`, `~+=`, ...) on a bitfield slice are
  intentionally rejected since their semantics on a synthetic L-value
  are ambiguous.
- Side-effecting receivers (e.g. `arr[next()].bits[…]` with a mutating
  `next()`) are rejected at parse time as of B4-sugar Phase 3
  (2026-04-25) with a "bind to a temp first" diagnostic — the rewrite
  duplicates the lvalue 2-3 times, so calls on the lvalue spine would
  re-execute their side effects. Workaround:

  ```simple
  var t = arr[next()]
  t.bits[lo..hi] = v
  arr[idx] = t
  ```

  Full single-eval temp binding inside the desugar is deferred (it
  needs multi-statement lowering the parse-time AST rewrite cannot
  synthesise on its own).
- `defer x.bits[lo..hi] = v` (single-line defer) and the equivalent
  block form `defer:\n    x.bits[lo..hi] = v` both desugar correctly
  as of B4-sugar Phase 3. Single-line defer bodies only support plain
  `=` (consistent with `parse_defer_body` itself); for augmented
  forms inside defer use the block form.
- Pure-Simple equivalents `extract_bits` / `insert_bits` /
  `get_byte` / `set_byte` live in `std.bitwise_utils` and remain
  available for cases where a function call is preferable.

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

### Existence Check (`.?`) — Returns `T?`

The `.?` operator checks if a value is **present** (not nil AND not empty).
It returns `T?` — the value itself if present, `nil` if absent. This enables
pattern binding with `if val`:

Compiler/backend note: `nil` means missing metadata. Backend emitters must not
stringify it as a target type or symbol. Normalize optional compiler metadata
with the target backend guard (for LLVM, `valid_llvm_type(...)`) before emitting
call, phi, cast, load/store result, or serialized MIR text. `simple lint` reports
`LLVM001` when LLVM result type metadata is read with raw `get_local_type(...)`
in known result-type positions.
LLVM pointer-producing instructions must also mark the destination through
`mark_ptr_local(...)`, so later `Copy`/`Move` lowering preserves pointer IR
instead of falling back to integer arithmetic.

```simple
# Returns T? (value if present, nil if absent)
opt.?                         # T?:    pass-through (already optional)
list.?                        # [T]?:  Some(list) if non-empty, nil if []
dict.?                        # {K:V}?: Some(dict) if non-empty, nil if {}
str.?                         # text?: Some(str) if non-empty, nil if ""
num.?                         # i64?:  Some(num) — primitives always present
flag.?                        # bool?: Some(flag) — primitives always present

# Pattern binding — the key benefit
if val name = input.?:
    process(name)             # bound, guaranteed non-empty

# Nil coalescing — one-liner defaults
val host = config_host.? ?? env_host.? ?? "localhost"

# Still works in boolean context (truthiness of T?)
if str.?:                     # truthy if non-nil, non-empty
    use(str)
```

### `presence` / `presence_trimmed` — Text Presence Functions

Named alternatives to `.?` for text, providing readable presence checks:

```simple
# Returns text? — value if non-empty, nil if empty
presence("hello")             # "hello" (text?)
presence("")                  # nil

# Returns text? — value if non-blank, nil if empty/whitespace
presence_trimmed("hello")     # "hello" (text?)
presence_trimmed("  ")        # nil

# Pattern binding
if val name = input.presence:
    process(name)

# Nil coalescing
val display = input.presence ?? "Anonymous"

# Trimmed variant — skips whitespace-only strings
val query = user_input.presence_trimmed ?? "default search"
```

### Result with `.?`

```simple
# Result.ok returns Option, Result.err returns Option
result.ok.?                   # T? if Ok (replaces is_ok())
result.err.?                  # E? if Err (replaces is_err())

# Example: pattern binding with Result
val r: Result<i32, text> = Ok(42)
if val value = r.ok.?:
    print "Success: {value}"
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
# Extract first element if present
if val first = list.first.?:
    process(first)

# Extract trimmed string if non-empty
if val trimmed = str.trim.?:
    search(trimmed)

# Full pattern with optional chaining + existence + binding
if val tags = user?.profile?.tags.?:
    for tag in tags:
        print tag.upper.trim
```

### Refactoring Patterns

| Verbose | Concise | Notes |
|---------|---------|-------|
| `if opt.is_some(): use(opt!)` | `if val x = opt.?: use(x)` | Bind + use |
| `opt.is_none()` | `not opt.?` | Negated existence |
| `if s.not_empty: use(s)` | `if val s = s.?: use(s)` | Bind non-empty text |
| `if s.not_empty: use(s) else: use(d)` | `val s = s.presence ?? d` | With fallback |
| `s.not_empty` (bool) | `s.presence` (text?) | Value-returning check |
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

### Multi-Return Tuples

**NOTE:** Labeled-tuple returns (`-> (name: type, ...)`) are currently **NOT parseable** by either the seed or self-hosted parser. Use unlabeled tuples with `.0`/`.1` accessors instead. See [doc/08_tracking/bug/labeled_tuple_return_parser_gap_2026_07_17.md](../../08_tracking/bug/labeled_tuple_return_parser_gap_2026_07_17.md).

```simple
fn div_rem(n: i64, d: i64) -> (i64, i64):
    return (n / d, n % d)

val r = div_rem(10, 3)
print r.0  # quotient
print r.1  # remainder
```

**⚠️ WARNING: Labeled-tuple return syntax is currently unparseable.** Both seed and self-hosted compilers reject `-> (label: type, ...)` syntax. See `doc/08_tracking/bug/seed_parser_labeled_tuple_return_type_gap_2026-07-17.md` for details. Use the anonymous tuple form below + destructure with typed bindings as the current workaround.

Anonymous tuple returns remain valid when the fields are not ambiguous:

```simple
fn bounds(x: i64) -> (i64, bool):
    return (x, x == 0)
```

Functions may not return repeated same-type anonymous tuple fields such as
`-> (u8, u8)`; label those fields instead.

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

### Placeholder Lambda

```simple
# `_` stands for each successive parameter
items.map(_ * 2)                     # \__p0: __p0 * 2
items.filter(_ > 3)                  # \__p0: __p0 > 3
items.reduce(_ + _)                  # \__p0, __p1: __p0 + __p1

# Numbered placeholders: explicit parameter ordering
items.map(_1 * 10)                   # \__p0: __p0 * 10
pairs.reduce(_2 - _1)               # \__p0, __p1: __p1 - __p0

# Nested scoping: each call's args are independent
_.items.any(_ > 3)                   # outer: \__p0: __p0.items.any(INNER)
                                     # inner: \__p0: __p0 > 3
```

### Method Reference

```simple
# &:method → \__p0: __p0.method()
words.map(&:len)                     # [2, 5, 3]
nums.map(&:to_s)                     # ["1", "2", "3"]
val get_len = &:len                  # store as value
```

### Curry and Partial Application

```simple
use std.common.functions.{curry2, curry3, partial1, partial2}

val curried_add = curry2(add)        # curry2(f) → \a: \b: f(a, b)
val add5 = curried_add(5)            # \b: add(5, b)
add5(3)                              # 8

val inc = partial1(add, 1)           # partial1(f, a) → \b: f(a, b)
[1, 2, 3].map(inc)                   # [2, 3, 4]
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
    case _("all remaining values use the fallback label"): "other"
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

### Binding Destructuring & Tuple Unpacking

```simple
# Tuple destructuring — both literal and non-literal initializers
val (x, y) = get_point()                    # function result
val (a, b, c) = (1, 2, 3)                   # literal tuple
val (first, second, ...rest) = items        # variable destructuring

# Single evaluation guarantee: non-literal initializers eval exactly once
val (a, b) = expensive_fn()                 # fn called once, indexed results extracted

# Underscore skips unwanted fields
val (x, _, z) = get_coords()

# Array & dict destructuring
val [a, b, c] = triple
val {name, age} = person
```

**Native Path Support** (2026-07-11 redeploy):
- Literal tuples: per-element lowering with arity checking.
- Non-literal initializers: desugared to temp variable + indexed extraction, guaranteeing single evaluation.
- Parser fix: plain identifiers in patterns no longer become literal names (was a `parse_pattern` bug).

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

loop:
    match iterator.next():
        Some(item): process(item)
        nil: break
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

### Empty Statements / No-op

**Both `()` and `pass` are valid and equivalent** - use whichever is clearer in context:

```simple
# Unit value () - expression-oriented style (Rust-like)
match value:
    Some(x):
        process(x)
    nil:
        ()  # Do nothing, return unit value

# pass keyword - statement style (Python-like)
match value:
    Some(x):
        process(x)
    nil:
        pass  # Do nothing

# Both are synonyms - choose based on preference:
# - () is more consistent with expression-oriented design
# - pass is more explicit about intent "intentionally doing nothing"

# In match arms (both work identically):
match result:
    Ok(value): value
    Err(_): ()       # Returns unit value

match result:
    Ok(value): value
    Err(_): pass     # No-op statement
```

**Design Note:** Simple supports both for flexibility:
- **`()`** - Unit value (type is `()`), follows Rust/Scala conventions
- **`pass`** - No-op statement, familiar to Python developers

They compile to identical code. Use `()` for expression contexts, `pass` for clarity in statement contexts.

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

### Placeholder Lambdas in Pipes

Parenthesised placeholder expressions (`_1`, `_2`) are transformed into lambdas
automatically inside a pipe. Fixed in parser as of 2026-05-29.

```simple
# These now parse correctly in interpreter mode:
val result = 5 |> (_1 * 3)             # 15
val clamped = values |> (_1.max(0))    # clamp negatives
pairs |> (_1 + _2)                     # binary placeholder
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

## Traits

The `trait` keyword defines an interface as a struct-with-fn-fields. Traits desugar at compile time
via the desugar pass (`src/app/desugar/trait_scanner.spl`, `src/app/desugar/forwarding.spl`).

### Declaring a Trait

```simple
trait OrderRepo:
    fn save(order: text)
    fn find(id: text) -> text
    fn list() -> [text]
```

Abstract methods (no body) become fn-fields in the generated struct. Methods with a default body are
skipped -- concrete implementations provide them.

### Implementing a Trait

```simple
impl OrderRepo for sql:
    fn save(order: text): sql_insert(order)
    fn find(id: text) -> text: sql_select(id)
    fn list() -> [text]: sql_select_all()
```

This generates a factory function `sql_as_OrderRepo() -> OrderRepo` that constructs the struct with
the provided implementations.

### Forwarding a Trait to a Field

Use `alias Trait = field` inside a class body to forward all abstract methods of the trait to a
composed field:

```simple
class Logger with Printable, Clickable:
    printer: Printer
    handler: Handler
    alias Printable = printer    # all Printable abstract methods forwarded to printer
    alias Clickable = handler    # all Clickable abstract methods forwarded to handler
    fn on_click(event: Event):   # explicit fn overrides forwarded method
        handle_click(event)
```

See [No-Inheritance Ergonomics](../research/no_inheritance_ergonomics_2026-02-16.md) for full
forwarding syntax and design rationale.

### Existing Trait Example (Resource)

The built-in `Resource` trait uses the same syntax:

```simple
trait Resource:
    fn close()
    fn is_open() -> bool
    fn resource_name() -> text
```

---

## Visibility & Friend Access

Control symbol visibility across packages and layers.

### Visibility Modifiers

```simple
# Public — visible everywhere (default for exported symbols)
pub fn public_api() -> text: "hello"

# Friend-visible — accessible by declared friend packages only
pub(friend) fn internal_helper() -> text: "internal"

# Peer-visible — accessible from same-path sibling layers only
pub(peer) fn sibling_helper() -> text: "peer"

# Parent-visible — accessible from the immediate parent facade only
pub(up) fn parent_helper() -> text: "up"

# Package-visible — accessible within the same package only
pub(package) fn package_util() -> text: "package"

# Private — accessible within the same file only (default)
fn private_impl() -> text: "private"
```

### Friend Declarations (in `__init__.spl`)

```simple
# Declare which packages can access internal symbols
friend types
friend traits
friend mir

# Export symbols publicly
export HirModule, HirExpr, HirStmt

# Export symbols to friends only
internal_export HirLowering, HirBuilder
```

### Semantics

- **Non-transitive:** A's friend seeing B's friend's internals is NOT allowed
- **Unidirectional:** `friend X` means X can see our internals, not vice versa
- **Non-inherited:** Friend status does not extend to subpackages
- **Scoped sibling access:** `pub(peer)` is for same-path modules in different numbered layers
- **Scoped parent access:** `pub(up)` is for the nearest parent `__init__.spl`
- **Compatibility mode:** sibling access to a private symbol still warns until it is migrated to `pub(peer)`

See [Friend Access Control](../design/friend_access_control.md) and [Layered Compiler Architecture](../design/layered_compiler_architecture.md).

### Module Resolution: File vs Package (known-inconsistent — read before relying on it)

When a directory contains both `name/__init__.spl` (a package) and a sibling
`name.spl` file with the same leaf name, which one `use foo.name` resolves
to is **not consistent** across the interpreter's resolution strategies, and
for `use std.<name>` specifically a seed-bundled stdlib copy
(`src/compiler_rust/lib/std/src`) is consulted *before* your project's own
`src/lib/`, so a same-named package there can win regardless of what
`src/lib/<family>/` contains. Do not assume file-wins or package-wins as a
blanket rule. Two concrete, opposite examples in the current stdlib:

- `std.spec`: the canonical BDD framework is the **file**
  (`src/lib/<family>/spec.spl`), with a same-named `spec/` package holding
  only the skip/ignore-decorator submodules. `print_summary`/`get_exit_code`/
  `get_executed_test_count` currently are NOT reliably reachable via
  `use std.spec.{...}` — see the bug doc below for why.
- `std.io`: the canonical implementation is the **package**
  (`src/lib/<family>/io/__init__.spl`, with real submodules like
  `file_ops.spl`/`env_ops.spl`); the sibling `io.spl` file is a thin facade
  that re-exports from the package via a fully-qualified import, and
  deliberately depends on package-first resolution to avoid resolving back
  to itself.

Multi-segment imports that name a submodule directly (`use
std.spec.decorators.{skip}`) are unaffected either way — they resolve
`decorators.spl` inside the `spec/` directory as a plain file, never hitting
the file/package ambiguity at the leaf name itself. A package `__init__.spl`
can only bare-`export` names defined by files inside its own directory — it
cannot re-export names from an external same-named sibling file.

Full root-cause analysis, evidence, and what has/hasn't been fixed:
`doc/08_tracking/bug/std_spec_package_shadows_file_print_summary_2026-07-17.md`.

---

## Method Chaining / Fluent API

Methods exist on classes and can be called as `receiver.method(args)`. However, the `.claude/rules/language.md` runtime rule states:

> **Chained methods broken — use intermediate `var`**

Until `doc/05_design/compiler_rfc_method_chain_fix.md` lands, write each call as a separate assignment:

```simple
# Correct — intermediate var pattern
var node = WidgetNode(kind: WidgetKind.Panel, layout: LayoutKind.Column)
node = node.width(320)
node = node.label("Settings")
node = node.padding(theme, Spacing.Lg)
node = node.child(body_node)

# NOT YET WORKING — chained form (conditional on chain-fix RFC)
# val node = WidgetNode(...).width(320).label("Settings").padding(theme, Spacing.Lg)
```

The intermediate-var form will continue to compile correctly after the chain-fix RFC lands.

See also: `doc/05_design/ui_typed_core_rfc.md` Phase 3 for the full list of fluent methods on `WidgetNode`.

---

## Enum Construction & Inference

Today, enum variants must be fully qualified:

```simple
use std.ui.{WidgetKind, LayoutKind, Spacing, SurfaceRole}

val kind = WidgetKind.Panel          # qualified — works today
val layout = LayoutKind.Column       # qualified — works today
val space = Spacing.Md               # qualified — works today
val role = SurfaceRole.Card          # qualified — works today
```

**Future — bare enum literals** (pending `doc/05_design/compiler_rfc_bare_enum_literals.md`): once that RFC lands, the compiler will infer the enum type from context and bare names will work:

```simple
# Future only — not available yet
val node = WidgetNode(kind: Panel, layout: Column)
node = node.padding(theme, Md)
```

Until the RFC ships, always write the fully-qualified `Foo.Bar` form.

---

## Not Yet Implemented

These features are **not available**:

| Feature | Workaround |
|---------|------------|
| Byte strings `b"..."` | Use array of bytes |
| For-else | Use flag variable |
| Elvis `?:` | Use `??` instead |

### Not Part of Simple's Design

**Class inheritance (`class Child(Parent):`) is NOT supported** and will not be implemented. Simple intentionally avoids implementation inheritance. Use these patterns instead:

| Pattern | Syntax | Purpose |
|---------|--------|---------|
| **Composition** | `class X: inner: OtherType` | Embed and delegate to fields |
| **Alias forwarding** | `alias TraitName = field` | Auto-forward trait methods to a field |
| **Traits/mixins** | `struct X with Mixin:` | Mix in shared behavior |
| **Type alias** | `type NewName = Existing` | Create alternative type names |
| **Class alias** | `alias NewName = Existing` | Create alternative class names |

See [coding_style.md](../language/coding_style.md) for the current inheritance policy and migration guidance.

---

## See Also

- [language/syntax.md](../language/syntax.md) - Main syntax guide
- [language/error_handling.md](../language/error_handling.md) - `Result`, `Option`, and `?`
- [language/coding_style.md](../language/coding_style.md) - Canonical style rules
- [../../06_spec/app/compiler/modules/grammar/grammar_reference.md](../../06_spec/app/compiler/modules/grammar/grammar_reference.md) - Grammar registry output
- [../import_quick_reference.md](import_quick_reference.md) - Import patterns
- [../../05_design/pipeline_operators_design.md](../../05_design/pipeline_operators_design.md) - Pipeline operator design
