# Simple Standard Library API Improvements

Based on lessons learned from Rust, Python, Ruby, Scala, Go, and Java API design regrets.

---

## 1. Option/Result API Improvements

### 1.1 Rename `unwrap()` to Explicit Panic Methods

**Problem:** `unwrap()` hides panic possibility, encourages careless use.

**Current (Bad):**
```simple
let value = opt.unwrap()  # Panics silently
```

**Improved:**
```simple
# Option 1: Only provide expect()
let value = opt.expect("user must be logged in")

# Option 2: Explicit panic name
let value = opt.unwrap_or_panic()

# Option 3: Unsafe marker
let value = opt.unwrap!()  # ! indicates danger
```

**Recommendation:** Remove `unwrap()`, only provide `expect(msg: str)`.

### 1.2 Consistent Unwrap Family

| Method | Returns | On None/Err |
|--------|---------|-------------|
| `expect(msg)` | `T` | Panic with message |
| `unwrap_or(default)` | `T` | Return default |
| `unwrap_or_else(f)` | `T` | Call f() |
| `unwrap_or_default()` | `T` | T::default() |
| `ok()` | `Option[T]` | Convert Result→Option |
| `err()` | `Option[E]` | Get error if present |

### 1.3 Add `try_*` Variants

For methods that might fail, provide non-panicking alternatives:

```simple
# Instead of panicking on index out of bounds
fn get(self, idx: usize) -> Option[T]      # Safe
fn get_unchecked(self, idx: usize) -> T    # Unsafe, no bounds check

# Instead of panicking on parse failure
fn parse[T](s: str) -> Result[T, ParseError]  # Always use Result
```

---

## 2. Naming Conventions

### 2.1 Standardize Size/Length

**Problem:** Languages use `size`, `length`, `count`, `len` inconsistently.

**Decision:** Use `len()` everywhere.

```simple
# Correct
array.len()
string.len()
map.len()
set.len()

# Never use
array.size()      # Wrong
string.length()   # Wrong
map.count()       # Wrong
```

### 2.2 Standardize Existence Checks

| Method | Returns | Use Case |
|--------|---------|----------|
| `contains(item)` | `bool` | Check if item exists |
| `contains_key(key)` | `bool` | Check if key exists (maps) |
| `is_empty()` | `bool` | Check if len == 0 |
| `is_some()` | `bool` | Option has value |
| `is_ok()` | `bool` | Result is success |

**Avoid:** `has()`, `includes()`, `exists()` - use `contains()`.

### 2.3 Standardize Retrieval Methods

| Method | Returns | Behavior |
|--------|---------|----------|
| `get(key)` | `Option[T]` | Safe lookup |
| `get_or(key, default)` | `T` | With default |
| `get_mut(key)` | `Option[&mut T]` | Mutable reference |
| `first()` | `Option[T]` | First element |
| `last()` | `Option[T]` | Last element |

**Never:** `get()` that panics. Use `expect()` explicitly if panic desired.

### 2.4 Standardize Removal Methods

| Method | Returns | Behavior |
|--------|---------|----------|
| `remove(key)` | `Option[T]` | Remove and return |
| `remove_at(idx)` | `Option[T]` | Remove by index |
| `pop()` | `Option[T]` | Remove last |
| `pop_front()` | `Option[T]` | Remove first |
| `clear()` | `()` | Remove all |
| `retain(predicate)` | `()` | Keep matching |

### 2.5 Mutable vs Immutable Method Names

| Operation | Mutable (in-place) | Immutable (returns new) |
|-----------|-------------------|------------------------|
| Sort | `sort()` | `sorted()` |
| Reverse | `reverse()` | `reversed()` |
| Filter | `filter_in_place(p)` | `filtered(p)` |
| Map | N/A | `mapped(f)` |
| Append | `push(x)` | `appended(x)` / `with(x)` |
| Update | `set(i, v)` | `with_index(i, v)` |
| Trim | `trim()` | `trimmed()` |
| Upper | `make_uppercase()` | `uppercased()` |
| Lower | `make_lowercase()` | `lowercased()` |

### 2.6 `as_` vs `to_` Convention (IMPORTANT)

**Rule:** Use `as_` for cheap/borrowed views, `to_` for expensive/owned conversions.

| Prefix | Cost | Ownership | Examples |
|--------|------|-----------|----------|
| `as_` | O(1), cheap | Borrows, returns reference | `as_str()`, `as_bytes()`, `as_slice()` |
| `to_` | O(n), may allocate | Creates new owned value | `to_string()`, `to_array()`, `to_vec()` |

**Examples:**
```simple
# as_ - cheap reference conversion (no allocation)
let s: &str = string.as_str()       # O(1), borrows
let b: &[u8] = string.as_bytes()    # O(1), borrows
let slice: &[T] = vec.as_slice()    # O(1), borrows

# to_ - creates new owned value (may allocate)
let s: String = value.to_string()   # O(n), allocates
let arr: Array[T] = iter.to_array() # O(n), allocates
let set: Set[T] = arr.to_set()      # O(n), allocates
```

**Never mix these up:**
```simple
# WRONG - these should be as_ since they're cheap
string.to_str()      # Wrong! Use as_str()
vec.to_slice()       # Wrong! Use as_slice()

# WRONG - these should be to_ since they allocate
bytes.as_string()    # Wrong! Use to_string()
iter.as_array()      # Wrong! Use to_array()
```

**For type conversions:**
```simple
# Numeric conversions use to_ (creates new value)
i32.to_i64()         # Widening conversion
i64.to_i32()         # Narrowing (returns Option)
f64.to_string()      # Format as string

# Reference conversions use as_
value.as_ref()       # Borrow as reference
slice.as_ptr()       # Get raw pointer (no copy)
```

---

## 3. Collections API

### 3.1 Clear Collection Types

| Type | Mutability | Allocation | Use Case |
|------|------------|------------|----------|
| `Array[T]` | Mutable | Heap, growable | General purpose |
| `List[T]` | Immutable | Heap, persistent | Functional style |
| `StaticVec[T, N]` | Immutable API | Stack, fixed | No-GC contexts |
| `Slice[T]` | Borrowed | None | Views into arrays |

### 3.2 Consistent Constructors

```simple
# Empty
Array[i32].new()
Array[i32].with_capacity(100)

# From elements
Array.of(1, 2, 3)
Array.from_iter(iter)
Array.from_slice(slice)

# Filled
Array.filled(0, count: 10)      # [0, 0, 0, ...]
Array.filled_with(|| rand(), count: 10)
```

### 3.3 Single Add-Element Method

**Problem:** Python's `append()` vs `extend()` confusion.

**Solution:**
```simple
# Single element
array.push(item)

# Multiple elements - explicit about iterable
array.push_all(other_array)
array.push_slice(slice)

# Never
array.push([1, 2, 3])  # Compile error: expected T, got Array[T]
```

### 3.4 Iterator Methods Return Concrete Types

**Problem:** Rust's `.collect::<Vec<_>>()` turbofish is awkward.

**Solution:**
```simple
# Instead of
let vec = iter.collect::<Array<_>>()

# Provide explicit constructors
let vec = Array.from_iter(iter)

# Or return concrete type when unambiguous
let vec = (1..10).to_array()
let set = array.to_set()
let map = pairs.to_map()
```

---

## 4. String API

### 4.1 Single String Type

**Problem:** Rust's `String` vs `&str` confusion.

**Solution:** Single `str` type with internal ownership tracking.

```simple
# All strings are `str`
let s: str = "hello"
let s: str = str.from_utf8(bytes)?
let s: str = format("{} {}", first, last)

# Borrowing is automatic
fn greet(name: str):  # Accepts owned or borrowed
    print("Hello, {name}")
```

### 4.2 Text vs Binary

```simple
# Text (UTF-8, always valid)
let text: str = "hello"

# Binary data
let data: Bytes = file.read_bytes()?

# Explicit conversion (follows as_/to_ convention)
let text = str.from_utf8(data)?        # May fail (to_ would be wrong - this is parsing)
let text = str.from_utf8_lossy(data)   # Replace invalid
let bytes: &[u8] = text.as_bytes()     # O(1), cheap borrow
let owned: Bytes = text.to_bytes()     # O(n), allocates new Bytes
```

### 4.3 String Methods

```simple
# Searching
s.contains(sub)         # bool
s.starts_with(prefix)   # bool
s.ends_with(suffix)     # bool
s.find(sub)            # Option[usize]
s.find_all(sub)        # Iterator[usize]

# Transformation (immutable - return new string)
s.trimmed()
s.uppercased()
s.lowercased()
s.replaced(old, new)
s.split(sep)           # Iterator[str]

# Building
str.join(sep, parts)   # Join iterable
format("{} {}", a, b)  # Formatting
```

---

## 5. Numeric API

### 5.1 No Implicit Numeric Conversions

**Problem:** Silent precision loss, overflow behavior changes.

```simple
# Bad (other languages)
let x: f64 = 5 / 2      # 2.0 or 2.5? Depends on language!

# Good (Simple)
let x: f64 = 5.0 / 2.0  # 2.5 (float division)
let x: i32 = 5 / 2      # 2 (integer division)
let x: f64 = (5).to_f64() / 2.0  # Explicit conversion
```

### 5.2 Explicit Conversion Methods

```simple
# Widening (always safe)
i32.to_i64()
f32.to_f64()

# Narrowing (may fail)
i64.to_i32() -> Option[i32]     # None if overflow
f64.to_f32() -> f32             # May lose precision (warn?)

# Truncating (explicit loss)
i64.truncate_to_i32() -> i32    # Wraps on overflow
f64.truncate_to_i64() -> i64    # Truncates decimal

# Checked arithmetic
a.checked_add(b) -> Option[T]
a.checked_mul(b) -> Option[T]
a.saturating_add(b) -> T        # Clamps to MAX/MIN
a.wrapping_add(b) -> T          # Wraps around
```

### 5.3 Division Clarity

```simple
# Integer division
5 / 2           # 2 (truncates toward zero)
5.div_floor(2)  # 2 (truncates toward negative infinity)
5 % 2           # 1 (remainder)
5.mod(2)        # 1 (modulo, always positive)

# Float division
5.0 / 2.0       # 2.5
5.0 / 0.0       # inf (not panic)
```

---

## 6. Error Handling API

### 6.1 Result Methods

```simple
# Transforming
result.map(f)           # Transform Ok value
result.map_err(f)       # Transform Err value
result.and_then(f)      # Chain operations

# Extracting
result.expect(msg)      # Panic with message if Err
result.unwrap_or(default)
result.unwrap_or_else(f)
result.ok()             # Option[T]
result.err()            # Option[E]

# Checking
result.is_ok()
result.is_err()

# The ? operator
let value = fallible_operation()?  # Early return on Err
```

### 6.2 Error Types

```simple
# Define specific errors
enum FileError:
    NotFound(path: FilePath)
    PermissionDenied(path: FilePath)
    IoError(msg: str)

impl FileError:
    fn message(self) -> str:
        match self:
            NotFound(p) => format("file not found: {p}")
            PermissionDenied(p) => format("permission denied: {p}")
            IoError(m) => m

# Implement Error trait
impl Error for FileError:
    fn description(self) -> str:
        self.message()
```

### 6.3 Context/Wrapping

```simple
# Add context to errors
let content = read_file(path)
    .with_context(|| format("failed to read config from {path}"))?

# Convert error types
let value = parse_int(s)
    .map_err(|e| ConfigError.InvalidValue(e.message()))?
```

---

## 7. I/O API

### 7.1 Async by Default (for host platform)

```simple
# Async I/O (default for host)
async fn read_file(path: FilePath) -> Result[str, IoError]
async fn write_file(path: FilePath, content: str) -> Result[(), IoError]

# Blocking variants available
fn read_file_sync(path: FilePath) -> Result[str, IoError]
```

### 7.2 Resource Management

```simple
# RAII-style with use/defer
use file = File.open(path)?:
    let content = file.read_all()?
    # file automatically closed

# Or explicit
let file = File.open(path)?
defer file.close()
let content = file.read_all()?
```

### 7.3 Path API with Unit Types

```simple
# Type-safe paths
let file: FilePath = FilePath.from("config.toml")
let dir: DirPath = DirPath.from("/home/user")

# Operations
let full = dir.join(file)           # DirPath + FilePath -> FilePath
let parent = file.parent()          # Option[DirPath]
let name = file.file_name()         # FileName
let ext = file.extension()          # Option[FileExt]

# Never bare strings for paths
fn read_config(path: FilePath) -> Result[Config, Error]
# NOT: fn read_config(path: str)
```

---

## 8. Concurrency API

### 8.1 Clear Sync/Async Boundary

```simple
# Mark async functions clearly
async fn fetch_data() -> Data

# Easy bridging
fn main():
    # Block on async from sync context
    let data = block_on(fetch_data())

    # Or spawn
    let handle = spawn(fetch_data())
    let data = handle.await
```

### 8.2 Actor API

```simple
# Define actor
actor Counter:
    var count: i32 = 0

    fn increment(self):
        self.count += 1

    fn get(self) -> i32:
        self.count

# Use actor
let counter = Counter.spawn()
counter.send(Counter.increment)
let value = counter.ask(Counter.get).await
```

### 8.3 Channel API

```simple
# Bounded channel
let (tx, rx) = channel[Message](capacity: 100)

# Send (async, waits if full)
tx.send(msg).await

# Receive
match rx.recv().await:
    Some(msg) => process(msg)
    None => break  # Channel closed

# Try variants (non-blocking)
tx.try_send(msg) -> Result[(), SendError]
rx.try_recv() -> Option[Message]
```

---

## 9. Testing API

### 9.1 Clear Test Assertions

```simple
# Basic assertions
assert(condition)
assert_eq(actual, expected)
assert_ne(actual, expected)

# With messages
assert(condition, "user should be valid")
assert_eq(result, 42, "calculation failed")

# Approximate equality (floats)
assert_approx(actual, expected, epsilon: 0.001)

# Collection assertions
assert_contains(collection, item)
assert_empty(collection)
assert_len(collection, expected_len)
```

### 9.2 Result/Option Assertions

```simple
# Option
assert_some(opt)
assert_none(opt)
let value = assert_some(opt)  # Returns inner value

# Result
assert_ok(result)
assert_err(result)
let value = assert_ok(result)  # Returns Ok value
let error = assert_err(result) # Returns Err value
```

### 9.3 Panic Testing

```simple
#[test]
fn test_panic():
    assert_panics(|| dangerous_operation())
    assert_panics_with("index out of bounds", || array[999])
```

---

## 10. Documentation Standards

### 10.1 Every Public Item Documented

```simple
/// Reads the entire contents of a file into a string.
///
/// # Arguments
/// * `path` - The path to the file to read
///
/// # Returns
/// The file contents as a UTF-8 string, or an error if:
/// - The file does not exist
/// - The file is not valid UTF-8
/// - An I/O error occurs
///
/// # Example
/// ```
/// let content = read_file(FilePath.from("config.toml"))?
/// ```
async fn read_file(path: FilePath) -> Result[str, IoError]
```

### 10.2 Document Panics

```simple
/// Returns the element at the given index.
///
/// # Panics
/// Panics if `index >= self.len()`.
///
/// # See Also
/// Use `get(index)` for a non-panicking alternative.
fn index(self, index: usize) -> T
```

---

---

## 11. Ruby-Inspired Convenience Features

### 11.1 Expressive Integer Methods (Ruby `times`, `upto`, `downto`)

**Ruby Philosophy:** "Optimized for programmer happiness" - Matz

```simple
# Ruby-style iteration on integers
5.times(|i| print(i))              # 0, 1, 2, 3, 4
5.times(|| print("hello"))         # prints "hello" 5 times

1.upto(5, |i| print(i))            # 1, 2, 3, 4, 5
10.downto(1, |i| print(i))         # 10, 9, 8, 7, 6, 5, 4, 3, 2, 1

# With step
0.step(to: 10, by: 2, |i| print(i))  # 0, 2, 4, 6, 8, 10

# As iterators
for i in 5.times():
    print(i)

for i in 1.upto(10):
    print(i)
```

### 11.2 Method Chaining Helpers (Ruby `tap`, `then`)

```simple
# tap: Execute block, return self (for side effects in chains)
let user = User.new()
    .tap(|u| print("Creating user: {u.name}"))
    .validate()
    .tap(|u| log.info("User validated"))
    .save()

# then/pipe: Transform value through function (like |> in Elixir)
let result = input
    .then(|x| parse(x))
    .then(|x| validate(x))
    .then(|x| process(x))

# Equivalent to:
let result = process(validate(parse(input)))
```

### 11.3 Collection Transformation (Ruby `map`, `select`, `reject`)

```simple
# map with index (Ruby's each_with_index / map.with_index)
array.map_with_index(|item, idx| "{idx}: {item}")

# select (alias for filter) - keeps items where predicate is true
numbers.select(|n| n > 5)

# reject - keeps items where predicate is false (opposite of select)
numbers.reject(|n| n > 5)

# partition - split into two arrays
let (evens, odds) = numbers.partition(|n| n % 2 == 0)

# compact - remove None values from Option array
let values: Array[i32] = options.compact()

# flatten - flatten nested arrays
let flat = nested.flatten()        # one level
let flat = nested.flatten_deep()   # all levels
```

### 11.4 Hash/Map Conveniences (Ruby `dig`, `transform_keys`, `transform_values`)

```simple
# dig - safe nested access
let value = config.dig("database", "host", "port")  # Option[T]

# Instead of:
let value = config.get("database")
    .and_then(|db| db.get("host"))
    .and_then(|host| host.get("port"))

# transform_keys - modify all keys
let screaming = map.transform_keys(|k| k.uppercased())

# transform_values - modify all values
let doubled = map.transform_values(|v| v * 2)

# merge with conflict resolution
let merged = map1.merge(map2, |key, v1, v2| v1 + v2)

# fetch with default block (Ruby-style)
let value = map.fetch("key", || expensive_default())
```

### 11.5 Predicate Methods (Ruby naming style)

```simple
# Boolean methods end with ?-like naming (use is_ prefix)
array.is_empty()
string.is_blank()       # empty or only whitespace
option.is_some()
option.is_none()
result.is_ok()
result.is_err()
number.is_positive()
number.is_negative()
number.is_zero()
number.is_even()
number.is_odd()

# Also for strings
string.is_numeric()     # "123" -> true
string.is_alphabetic()  # "abc" -> true
string.is_alphanumeric()
```

### 11.6 Destructive vs Non-Destructive (Ruby `!` convention)

```simple
# In Simple, use clear naming instead of ! suffix
# Mutable (in-place)
array.sort()            # sorts in place, returns ()
array.reverse()         # reverses in place

# Immutable (returns new)
array.sorted()          # returns new sorted array
array.reversed()        # returns new reversed array

# Or use _in_place suffix for clarity
array.sort_in_place()
array.filter_in_place(predicate)
```

---

## 12. Python-Inspired Convenience Features

### 12.1 Built-in Aggregation Functions

**Python's Zen:** "Simple is better than complex"

```simple
# Top-level functions for common operations
sum(numbers)                    # Sum of iterable
max(numbers)                    # Maximum value
min(numbers)                    # Minimum value
any(booleans)                   # True if any is true
all(booleans)                   # True if all are true

# With key function
max(users, key: |u| u.age)      # User with highest age
min(files, key: |f| f.size)     # Smallest file

# With default for empty iterables
sum(empty, default: 0)
max(empty, default: none)
```

### 12.2 Enumeration and Zipping

```simple
# enumerate - get index with each item
for (idx, item) in array.enumerate():
    print("{idx}: {item}")

# zip - combine multiple iterables
for (a, b) in zip(list1, list2):
    print("{a} + {b}")

# zip with different lengths
zip_shortest(a, b, c)           # stops at shortest
zip_longest(a, b, c, fill: 0)   # pads shorter ones

# unzip - split array of tuples
let (names, ages) = pairs.unzip()

# enumerate + zip combined
for (idx, (a, b)) in zip(list1, list2).enumerate():
    print("{idx}: {a} + {b}")
```

### 12.3 List Comprehension Syntax

```simple
# Python-style comprehensions
let squares = [x * x for x in 1..10]
let evens = [x for x in numbers if x % 2 == 0]
let pairs = [(x, y) for x in 1..3 for y in 1..3]

# Dict comprehension
let squared = {x: x * x for x in 1..10}

# Set comprehension
let unique = {x.lowercased() for x in words}

# With transformation and filter
let processed = [
    process(x)
    for x in items
    if x.is_valid()
]
```

### 12.4 Slicing Syntax

```simple
# Python-style slicing
array[1:5]          # elements 1 to 4
array[:5]           # first 5 elements
array[5:]           # from index 5 to end
array[-3:]          # last 3 elements
array[::2]          # every 2nd element
array[::-1]         # reversed

# Also works on strings
string[0:5]         # first 5 characters
string[-5:]         # last 5 characters
```

### 12.5 String Conveniences

**Note:** String methods follow the `as_` vs `to_` convention:
- `as_str()`, `as_bytes()` - cheap borrows
- `to_string()`, `to_array()` - allocating conversions

```simple
# f-string style formatting (already supported)
let msg = f"Hello, {name}! You are {age} years old."

# Multi-line strings preserve indentation removal
let sql = """
    SELECT *
    FROM users
    WHERE active = true
""".dedent()

# split with maxsplit
"a,b,c,d".split(",", max: 2)    # ["a", "b", "c,d"]

# rsplit - split from right
"a.b.c.d".rsplit(".", max: 1)   # ["a.b.c", "d"]

# partition - split into (before, sep, after)
let (before, sep, after) = "hello=world".partition("=")

# join with separator
", ".join(items)                # "a, b, c"
str.join(", ", items)           # same thing

# strip variants
s.strip()           # both ends
s.lstrip()          # left only
s.rstrip()          # right only
s.strip("chars")    # specific chars
```

### 12.6 Itertools Equivalents

```simple
# chain - concatenate iterables
for item in chain(list1, list2, list3):
    process(item)

# flatten - flatten one level
let flat = nested.flatten()

# group_by - group consecutive elements (must be sorted)
for (key, group) in sorted_items.group_by(|x| x.category):
    print("{key}: {group.to_array()}")

# chunk - split into fixed-size chunks (Ruby: each_slice)
for chunk in items.chunks(3):
    print(chunk)    # [a, b, c], [d, e, f], ...

# windows - sliding window
for window in items.windows(3):
    print(window)   # [a, b, c], [b, c, d], ...

# take_while / drop_while
let prefix = items.take_while(|x| x < 10)
let suffix = items.drop_while(|x| x < 10)

# take / drop (simpler)
let first_five = items.take(5)
let rest = items.drop(5)

# cycle - repeat infinitely
for item in [1, 2, 3].cycle().take(10):
    print(item)     # 1, 2, 3, 1, 2, 3, 1, 2, 3, 1

# repeat
for x in repeat(42).take(5):
    print(x)        # 42, 42, 42, 42, 42
```

### 12.7 Dict/Map Conveniences

```simple
# get with default (Python-style)
let value = map.get("key", default: 0)

# setdefault - get or insert default
let value = map.setdefault("key", default: [])
value.push(item)    # now map["key"] contains [item]

# update - merge dicts
map.update(other_map)
map.update([("a", 1), ("b", 2)])

# items, keys, values as iterators
for (key, value) in map.items():
    print("{key}: {value}")

for key in map.keys():
    print(key)

for value in map.values():
    print(value)

# dict from pairs
let map = Map.from_pairs([("a", 1), ("b", 2)])

# invert - swap keys and values
let inverted = map.invert()     # {1: "a", 2: "b"}
```

---

## 13. Combined Best Practices: Ruby + Python + Rust

### 13.1 Design Philosophy Blend

| Aspect | Ruby | Python | Rust | Simple |
|--------|------|--------|------|--------|
| Goal | Programmer happiness | Readability | Safety | All three |
| Mutability | Mutable default | Mutable default | Immutable default | Configurable |
| Errors | Exceptions | Exceptions | Result types | Result types |
| Nil/None | nil everywhere | None | Option type | Option type |
| Naming | snake_case + ? ! | snake_case | snake_case | snake_case |

### 13.2 Convenience vs Safety Balance

```simple
# Safe (Rust-inspired) - always available
let value = array.get(5)           # Option[T]
let value = map.get("key")         # Option[T]

# Convenient (Ruby/Python-inspired) - opt-in via expect
let value = array.get(5).expect("index must exist")

# Very convenient (Python-inspired) - for scripts/REPL
#[allow(panic)]
let value = array[5]               # May panic, but concise

# Method chaining (Ruby-inspired)
let result = data
    .filter(|x| x.is_valid())
    .map(|x| x.process())
    .tap(|r| log.debug("Processed: {r.len()}"))
    .sorted()
    .take(10)
    .to_array()
```

### 13.3 Candidate API Methods Summary

| Category | Method | Inspired By | Description |
|----------|--------|-------------|-------------|
| Integer | `times()` | Ruby | Iterate n times |
| Integer | `upto(n)` | Ruby | Iterate from self to n |
| Integer | `downto(n)` | Ruby | Iterate from self down to n |
| Object | `tap(f)` | Ruby | Execute f(self), return self |
| Object | `then(f)` | Ruby/Elixir | Execute f(self), return result |
| Array | `select(p)` | Ruby | Alias for filter |
| Array | `reject(p)` | Ruby | Opposite of filter |
| Array | `partition(p)` | Ruby | Split by predicate |
| Array | `compact()` | Ruby | Remove None values |
| Array | `flatten()` | Ruby/Python | Flatten nested arrays |
| Array | `chunks(n)` | Ruby | Split into size-n chunks |
| Array | `windows(n)` | Rust | Sliding window |
| Map | `dig(keys...)` | Ruby | Safe nested access |
| Map | `transform_keys(f)` | Ruby | Map over keys |
| Map | `transform_values(f)` | Ruby | Map over values |
| Map | `setdefault(k, v)` | Python | Get or insert |
| Iter | `enumerate()` | Python | Add indices |
| Iter | `zip(other)` | Python | Pair elements |
| Iter | `chain(other)` | Python | Concatenate |
| Iter | `group_by(f)` | Python | Group consecutive |
| Iter | `take_while(p)` | Python | Take while true |
| Iter | `drop_while(p)` | Python | Drop while true |
| Global | `sum(iter)` | Python | Sum elements |
| Global | `max(iter)` | Python | Maximum element |
| Global | `min(iter)` | Python | Minimum element |
| Global | `any(iter)` | Python | Any true? |
| Global | `all(iter)` | Python | All true? |

---

## Summary: API Design Principles

1. **Explicit over implicit** - No hidden conversions, panics, or allocations
2. **Consistent naming** - One word per concept across entire stdlib
3. **Safe by default** - Unsafe operations require explicit opt-in
4. **Immutable by default** - Mutable operations clearly marked
5. **Type-safe** - Use unit types, not bare primitives
6. **Documented** - Every public item has docs with examples
7. **Testable** - Clear assertion API, easy mocking
8. **Async-friendly** - Easy bridging between sync/async
9. **Error-friendly** - Rich error types with context
10. **No legacy baggage** - Learn from others' mistakes
11. **Programmer happiness** (Ruby) - Expressive, chainable APIs
12. **Readability** (Python) - Simple, obvious, one way to do it
13. **Convenience methods** - Common operations should be one-liners
14. **`as_` vs `to_` convention** - `as_` for cheap borrows, `to_` for allocating conversions
