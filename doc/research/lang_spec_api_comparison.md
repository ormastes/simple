# Simple Language API Specification Comparison

**Status:** Research Document
**Date:** 2026-01-16
**Purpose:** Compare proposed Ruby-style API specification against current Simple implementation

---

## Executive Summary

This document analyzes the current Simple language implementation against a proposed API specification featuring:
- `in` operator for containment (replacing `contains`)
- `each` for character iteration (replacing `each_char`)
- Regex block `re{}` (no regex methods on String)
- Configurable sorting algorithms with `DEFAULT_DATASET_ALGORITHM`
- Abstract `Number` supertype with `Int`/`Float` hierarchy

**Overall Status:** Simple has strong foundational implementations but lacks several proposed features.

---

## 1. Regex Block (`re{}`)

### Proposed Specification
- Dedicated `re{}` block syntax for regex patterns
- NO regex methods on String type
- Pattern API: `compile()`, `match()`, `search()`, `findall()`, `sub()`, `split()`

### Current Implementation: ✅ **SUBSTANTIALLY COMPLETE**

| Component | Status | Location |
|-----------|--------|----------|
| Lexer support | ✅ Complete | `src/parser/src/lexer/identifiers.rs:225-325` |
| Parser AST | ✅ Complete | `src/parser/src/ast/nodes/core.rs:528-535` |
| Block handler | ✅ Complete | `src/compiler/src/blocks/regex.rs` |
| Stdlib NFA engine | ✅ Complete | `simple/std_lib/src/core/regex.spl` (44KB, 1,401 lines) |
| String regex methods | ✅ Correct | No regex on String (per spec) |
| Unit tests | ❌ Skipped | `simple/std_lib/test/unit/core/regex_spec.spl` (all 21 tests skipped) |

**Lexer Syntax:**
```simple
re{ pattern }
re{ (?P<name>capture) }
re{ pattern /imsx }   # flags
```

**Stdlib API Available:**
```simple
import core.regex: Pattern, compile, match, search, findall, sub, split, escape

val pattern = compile("\\d+")
val result = search(pattern, "abc123def")  # Match object
val all = findall("\\w+", text)            # List<Match>
val replaced = sub("old", "new", text)     # String
val parts = split("\\s+", text)            # List<String>
```

**Implementation Details:**
- NFA-based Thompson construction engine
- Supports: `\d`, `\w`, `\s`, anchors (`^`, `$`, `\b`), quantifiers (`*`, `+`, `?`, `{n,m}`)
- Named capture groups: `(?P<name>...)` and `(?<name>...)`
- Backreferences in replacement: `\1`, `\2`

**Gap:** Tests are skipped with comment "core.regex module is not yet implemented" - contradicts actual implementation.

---

## 2. Numeric Types

### Proposed Specification
```
abstract class Number
├── class Int : Number    (or abstract with I32, I64, U32, U64 concrete)
└── class Float : Number  (or abstract with F32, F64 concrete)

Number methods: abs(), clamp()
Int methods: is_even(), is_odd(), times(), upto(), downto()
Float methods: round(), floor(), ceil(), is_nan(), is_inf()
Checked arithmetic: checked_add(), etc.
```
> **Note:** Original proposals used Ruby-style `even?()`, `odd?()`, `nan?()`, `inf?()` but `?` is not allowed in method names per design decision. Use `is_*` prefix instead.

### Current Implementation: ⚠️ **PARTIAL**

| Feature | Status | Notes |
|---------|--------|-------|
| Numeric literals | ✅ Complete | Hex, octal, binary, scientific, type suffixes |
| Type suffixes | ✅ Complete | `42i32`, `3.14f64`, `100u8`, etc. |
| Primitive extensions | ✅ Complete | 50+ methods on `i64`/`f64` |
| Number supertype | ❌ Missing | No trait hierarchy |
| Multiple int types | ⚠️ Partial | Lexer supports, stdlib only implements `i64` |
| Unsigned types | ❌ Missing | No `u32`, `u64` extension methods |

**Current i64 Methods** (`simple/std_lib/src/core/primitives.spl`):
```simple
impl i64:
    fn abs() -> i64
    fn clamp(min: i64, max: i64) -> i64
    fn is_even() -> bool
    fn is_odd() -> bool
    fn is_positive() -> bool
    fn is_negative() -> bool
    fn is_zero() -> bool
    fn is_power_of_two() -> bool
    fn checked_add(other: i64) -> Option<i64>
    fn checked_sub(other: i64) -> Option<i64>
    fn checked_mul(other: i64) -> Option<i64>
    fn saturating_add(other: i64) -> i64
    fn wrapping_add(other: i64) -> i64
    # ... 20+ more methods
```

**Current f64 Methods:**
```simple
impl f64:
    fn abs() -> f64
    fn floor() -> f64
    fn ceil() -> f64
    fn round() -> f64
    fn trunc() -> f64
    fn sqrt() -> f64
    fn sin() -> f64
    fn cos() -> f64
    fn is_nan() -> bool
    fn is_infinite() -> bool
    fn is_finite() -> bool
    # ... 25+ more methods
```

**Missing vs Proposed:**

| Proposed | Current Status |
|----------|----------------|
| `Number` trait | ❌ Not implemented |
| `i.times(fn)` | ❌ Not implemented |
| `i.upto(j, fn)` | ❌ Not implemented |
| `i.downto(j, fn)` | ❌ Not implemented |
| `f.nan?` | ✅ `is_nan()` |
| `f.inf?` | ✅ `is_infinite()` |

**Design Decision:** Simple uses monomorphic function overloads rather than a numeric tower. This is intentional for explicit typing.

---

## 3. String Type (`text`)

### Proposed Specification
```
Str methods:
  len(), is_empty(), trim(), upper(), lower()
  split(), replace(old, new)
  each(fn) - iterate characters
  sub in s - containment via `in` operator
  NO regex methods
```
> **Note:** `empty?()` was originally proposed but `?` is not allowed in method names per design decision. Use `is_empty()` instead.

### Current Implementation: ✅ **MOSTLY COMPLETE**

| Feature | Status | Notes |
|---------|--------|-------|
| `len()` | ✅ Implemented | Byte length |
| `empty?` | ❌ Not Allowed | Use `.is_empty()` - `?` not allowed in method names per design decision |
| `trim()` | ✅ Implemented | Also `trim_start()`, `trim_end()` |
| `upper()` / `lower()` | ✅ Implemented | Also `uppercased()`, `lowercased()` |
| `split(delimiter)` | ✅ Implemented | Returns `List<text>` |
| `replace(old, new)` | ✅ Implemented | All occurrences |
| Character iteration | ✅ Implemented | `.chars()` returns list, `.iter()` for iteration |
| `each(fn)` | ⚠️ Partial | Use `.iter()` instead |
| Regex methods | ✅ Correct | None (per spec) |
| `in` operator | ❌ Missing | Use `.contains(substr)` |

**Current String Methods** (`simple/std_lib/src/core/string_core.spl`, `string_ops.spl`):
```simple
impl text:
    fn len() -> usize
    fn contains(substr: text) -> bool
    fn starts_with(prefix: text) -> bool
    fn ends_with(suffix: text) -> bool
    fn split(delimiter: text) -> List<text>
    fn replace(old: text, new: text) -> text
    fn trim() -> text
    fn trim_start() -> text
    fn trim_end() -> text
    fn upper() -> text
    fn lower() -> text
    fn substring(start: usize, end: usize) -> text
    fn char_at(idx: usize) -> char
    fn chars() -> List<char>
    fn find(substr: text) -> Option<usize>
    fn lines() -> List<text>
    fn char_count() -> usize
```

**Character Iteration:**
```simple
# Current approach (works)
for c in str.chars():
    process(c)

# Or via iterator
str.iter().for_each(|c| process(c))

# Proposed (not implemented)
str.each(|c| process(c))
```

---

## 4. Collections (`Seq[T]`)

### Proposed Specification
```simple
class Seq[T] : Ordered[T]:
  len() -> Int
  is_empty() -> Bool
  push(x: T)
  pop() -> T?
  map[U](fn) -> Seq[U]
  filter(fn) -> Seq[T]
  fold[U](init, fn) -> U
  sort(algorithm=DEFAULT_DATASET_ALGORITHM, stable=false)
  sort_by[K](key, algorithm=DEFAULT_DATASET_ALGORITHM, stable=false)

# Containment via `in` operator
x in xs
```
> **Note:** `empty?()` was originally proposed but `?` is not allowed in method names per design decision. Use `is_empty()` instead.

### Current Implementation: ⚠️ **MOSTLY COMPLETE**

| Feature | Status | Notes |
|---------|--------|-------|
| `len()` | ✅ Implemented | |
| `empty?` | ❌ Not Allowed | Use `.is_empty()` - `?` not allowed in method names per design decision |
| `push()` / `pop()` | ✅ Implemented | Also `push_front()`, `pop_front()` |
| `map()` / `filter()` | ✅ Implemented | |
| `fold()` | ✅ Implemented | Called `reduce()` |
| `sort()` | ⚠️ Basic | Insertion sort only, no algorithm choice |
| `sort_by()` | ❌ Missing | Not implemented |
| `in` operator | ❌ Missing | Use `.contains()` |

**Current List Methods** (`simple/std_lib/src/core/list.spl`):
```simple
impl List<T>:
    fn len() -> usize
    fn capacity() -> usize
    fn push(item: T)
    fn pop() -> Option<T>
    fn push_front(item: T)
    fn pop_front() -> Option<T>
    fn insert(idx: usize, item: T)
    fn remove(idx: usize) -> T
    fn map<U>(fn: (T) -> U) -> List<U>
    fn filter(predicate: (T) -> bool) -> List<T>
    fn reduce<U>(init: U, fn: (U, T) -> U) -> U
    fn find(predicate: (T) -> bool) -> Option<T>
    fn contains(value: T) -> bool where T: Eq
    fn sort() where T: Ord                          # Insertion sort only
    fn reverse()
    fn slice(start: usize, end: usize) -> List<T>
    fn join(sep: text) -> text where T: Display
    fn partition(predicate) -> (List<T>, List<T>)
    fn compact<U>() -> List<U>                      # Remove None values
    fn flatten<U>() -> List<U>
    fn chunks(size: usize) -> List<List<T>>
    fn windows(size: usize) -> List<List<T>>
    fn dedup() where T: Eq
    fn enumerate() -> List<(usize, T)>
```

**Sorting Implementation Gap:**
```simple
# Current (insertion sort only)
list.sort()

# Proposed (not implemented)
list.sort(algorithm=TIMSORT, stable=true, cmp=custom_compare)
list.sort_by(key_fn, algorithm=PDQSORT)

# Missing enum
enum SortAlgorithm { PDQSORT, TIMSORT, INTRO, MERGE, EXTERNAL_MERGE, AUTO }
const DEFAULT_DATASET_ALGORITHM = PDQSORT
```

---

## 5. Range Type

### Proposed Specification
```
Literal: 1..5 (inclusive) / 1...5 (exclusive)
each(fn) - iteration
x in r - containment
step(n) - stepped iteration
```

### Current Implementation: ✅ **COMPLETE**

| Feature | Status | Notes |
|---------|--------|-------|
| Inclusive `1..5` | ✅ Implemented | [1, 2, 3, 4, 5] |
| Exclusive `1..<5` | ✅ Implemented | [1, 2, 3, 4] (note: `..<` not `...`) |
| Stepped `0..10 by 2` | ✅ Implemented | |
| `contains()` | ✅ Implemented | |
| `in` operator | ❌ Missing | Use `.contains()` |
| `to_list()` | ✅ Implemented | |
| Reverse ranges | ✅ Implemented | `5..1` with step -1 |

**Syntax Difference:**
```simple
# Proposed (Ruby-style)
1...5   # exclusive end

# Current (Rust-style)
1..<5   # exclusive end
```

---

## 6. The `in` Operator

### Proposed Specification
Replace all `contains()` calls with `in` operator:
```simple
x in container    # Seq, Set, Map keys, Range, Str
```

### Current Implementation: ❌ **NOT IMPLEMENTED**

The `in` operator does not exist as syntax. All containment checks use method calls:

```simple
# Current approach (works)
arr.contains(value)
range.contains(n)
set.contains(elem)
text.contains(substr)

# Proposed (not implemented)
value in arr
n in range
elem in set
substr in text
```

**Implementation Requirements:**
1. Parser: Add `in` as binary operator
2. Type checker: Require `Collection<T>` trait or equivalent
3. Codegen: Lower to `.contains()` call

---

## 7. Summary Comparison Table

| Feature | Proposed | Current Status | Gap |
|---------|----------|----------------|-----|
| `re{}` block | Yes | ✅ Complete | Tests skipped |
| No regex on String | Yes | ✅ Correct | - |
| `in` operator | Yes | ❌ Missing | Parser change needed |
| `each` on String | Yes | ⚠️ `.iter()` | Naming difference |
| `empty?` predicate | Yes | ❌ Missing | Use `.len() == 0` |
| `Number` supertype | Yes | ❌ Missing | Design decision |
| `Int.times(fn)` | Yes | ❌ Missing | |
| `Int.upto(fn)` | Yes | ❌ Missing | |
| `sort(algorithm)` | Yes | ❌ Missing | Only insertion sort |
| `sort_by(key_fn)` | Yes | ❌ Missing | |
| `SortAlgorithm` enum | Yes | ❌ Missing | |
| Inclusive range `1..5` | Yes | ✅ Implemented | |
| Exclusive range | `1...5` | ⚠️ `1..<5` | Different syntax |

---

## 8. Recommended Implementation Priorities

### High Priority
1. **Enable regex tests** - Implementation exists, just skipped
2. **Add `in` operator** - High-value syntactic sugar
3. **Add `sort_by(key_fn)`** - Common functional pattern

### Medium Priority
4. **Add `empty?` predicate** - Convenience across all collections
5. **Add `SortAlgorithm` configuration** - Performance optimization control
6. **Add `times()`, `upto()`, `downto()`** - Ruby-style iteration

### Low Priority (Design Decisions)
7. **`Number` trait hierarchy** - Current monomorphic design is intentional
8. **Exclusive range syntax `...`** - Would conflict with existing `..<`

---

## 9. Key File Locations

| Component | Path |
|-----------|------|
| Regex lexer | `src/parser/src/lexer/identifiers.rs:225-325` |
| Regex block handler | `src/compiler/src/blocks/regex.rs` |
| Regex stdlib | `simple/std_lib/src/core/regex.spl` |
| Regex tests (skipped) | `simple/std_lib/test/unit/core/regex_spec.spl` |
| Primitives | `simple/std_lib/src/core/primitives.spl` |
| String | `simple/std_lib/src/core/string_core.spl`, `string_ops.spl` |
| List | `simple/std_lib/src/core/list.spl` |
| Array | `simple/std_lib/src/core/array.spl` |
| Collections traits | `simple/std_lib/src/core/collections.spl` |
| Range tests | `simple/std_lib/test/features/data_structures/ranges_spec.spl` |

---

## 10. Appendix: Cross-Language API Comparison

### Integer Methods

| Capability | Ruby | Python | Rust | Simple Current | Simple Proposed |
|------------|------|--------|------|----------------|-----------------|
| Absolute | `i.abs` | `abs(i)` | `i.abs()` | ✅ `i.abs()` | `i.abs()` |
| Even/Odd | `even?`/`odd?` | ❌ | `i % 2 == 0` | ✅ `is_even()`/`is_odd()` | `even?`/`odd?` |
| Repeat | `i.times {}` | ❌ | ❌ | ❌ | `i.times(fn)` |
| Clamp | `clamp(a,b)` | ❌ | `clamp(a,b)` | ✅ `clamp(a,b)` | `clamp(a,b)` |
| Checked math | ❌ | ❌ | `checked_add` | ✅ `checked_add()` | `checked_add()` |

### String Methods

| Capability | Ruby | Python | Rust | Simple Current | Simple Proposed |
|------------|------|--------|------|----------------|-----------------|
| Length | `length` | `len(s)` | `len()` | ✅ `len()` | `len()` |
| Empty | `empty?` | `not s` | `is_empty()` | ❌ | `empty?` |
| Trim | `strip` | `strip()` | `trim()` | ✅ `trim()` | `trim()` |
| Contains | `include?` | `in` | `contains` | ✅ `contains()` | `sub in s` |
| Iterate chars | `each_char` | `for c` | `chars()` | ✅ `chars()`/`.iter()` | `each(fn)` |
| Regex | native | `re` | crate | ❌ (correct) | `re{}` block |

### Collection Methods

| Capability | Ruby | Python | Rust | Simple Current | Simple Proposed |
|------------|------|--------|------|----------------|-----------------|
| Length | `length` | `len(a)` | `len()` | ✅ `len()` | `len()` |
| Push/Pop | `push`/`pop` | `append`/`pop` | `push`/`pop` | ✅ | ✅ |
| Map | `map` | comprehension | `map+collect` | ✅ `map(fn)` | `map(fn)` |
| Filter | `select` | comprehension | `filter` | ✅ `filter(fn)` | `filter(fn)` |
| Fold | `reduce` | `reduce` | `fold` | ✅ `reduce()` | `fold()` |
| Contains | `include?` | `in` | `contains` | ✅ `contains()` | `x in xs` |
| Sort | `sort!` | `sort()` | `sort()` | ✅ (insertion only) | `sort(algorithm)` |
| Sort-by | `sort_by!` | `sort(key=)` | `sort_by_key` | ❌ | `sort_by(key_fn)` |
