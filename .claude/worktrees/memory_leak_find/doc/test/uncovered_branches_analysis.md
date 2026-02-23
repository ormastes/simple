# Uncovered Branch Analysis - Seed Compiler (seed.cpp)

**Coverage Status:** 87.42% (2091/2392 branches)
**Uncovered:** 301 branches (12.58%)
**Generated:** 2026-02-11

## Executive Summary

Analysis of 51 unique source lines with uncovered branches reveals the following categories:

1. **String Parsing Edge Cases** (40% of uncovered) - Complex string operations with multiple delimiters
2. **Type System Corner Cases** (25%) - Optional types, struct arrays, nested generics
3. **Buffer Overflow Protection** (15%) - Safety checks for buffer size limits
4. **Expression Parsing** (12%) - Complex nested expressions with depth tracking
5. **Fallback/Error Paths** (8%) - Default cases and error recovery

## Detailed Analysis by Function

### 1. Type System Functions

#### `option_base_stype` (Lines 208, 211-213)
**Purpose:** Extract base type from Optional type (e.g., `i64?` → `i64`)

**Uncovered Branches:**
- Line 208: When optional type string is shorter than buffer size
- Lines 211-213: When type is NOT optional (else branch)

**Why Uncovered:** Most tests use short type names (`i64?`, `text?`). No tests with:
- Long type names exceeding buffer size
- Non-optional types passed to this function

**Test Cases Needed:**
```simple
# Test case 1: Very long optional type name
struct VeryLongStructNameThatExceedsTypicalBufferSize:
    value: i64

fn test_long_optional() -> VeryLongStructNameThatExceedsTypicalBufferSize?:
    nil

# Test case 2: Non-optional type passed to option handling
fn test_non_optional(x: i64):  # Not i64?
    pass
```

---

#### `expr_is_option` (Line 504)
**Purpose:** Check if expression returns an Optional type

**Uncovered Branch:** Function call check comment/path

**Why Uncovered:** Tests don't call functions that return Option types within complex expressions

**Test Cases Needed:**
```simple
fn maybe_get() -> i64?:
    Some(42)

fn test_optional_function_call():
    if maybe_get().:  # Function returning Option
        check(true)
```

---

#### `is_constant_expr` (Line 521)
**Purpose:** Detect if expression is a compile-time constant

**Uncovered Branch:** Negative number check (`-` followed by digit)

**Why Uncovered:** No tests with negative numeric literals in constant contexts

**Test Cases Needed:**
```simple
val neg_const = -42        # Negative integer literal
val neg_float = -3.14      # Negative float literal
val arr = [-1, -2, -3]     # Array of negative constants
```

---

### 2. String Parsing Functions

#### `ends_with` (Line 121)
**Purpose:** Check if string ends with suffix

**Uncovered Branch:** String comparison when length matches

**Why Uncovered:** All test strings either clearly match or clearly don't match

**Test Cases Needed:**
```simple
# Test strings that differ only at the end
val s1 = "test_abc"
val s2 = "test_xyz"
# Need suffix checks that match length but differ in content
```

---

#### `translate_expr` (Lines 678, 720, 757-759, 765)
**Purpose:** Convert Simple expressions to C++ code

**Uncovered Branches:**
- Line 678: Closing `}` in nested braces
- Line 720: Closing `}` in paren depth tracking
- Lines 757-759: String concatenation fallback paths
- Line 765: Alternative string buffer handling

**Why Uncovered:** Missing tests for:
- Complex string interpolation with nested braces: `"{outer {inner}}"`
- Multiple string concatenations in one expression
- Edge cases in string template handling

**Test Cases Needed:**
```simple
# Complex string interpolation
val x = 5
val y = 10
val s1 = "{x {y}}"                    # Nested braces
val s2 = "{x} + {y} + {x * y}"       # Multiple interpolations
val s3 = "{{ literal brace }}"       # Escaped braces

# String concatenation chains
val long = "a" + "b" + "c" + "d" + "e"
```

---

### 3. Array and Collection Functions

#### `array_elem_stype` (Lines 411, 416)
**Purpose:** Extract element type from array type signature

**Uncovered Branches:**
- Line 411: Comment path (unreachable)
- Line 416: Array element type extraction

**Why Uncovered:** Complex array type parsing not exercised

**Test Cases Needed:**
```simple
# Nested arrays
val arr2d: [[i64]] = [[1, 2], [3, 4]]
val arr3d: [[[text]]] = [[["a"]]]

# Arrays of optional types
val opt_arr: [i64?] = [Some(1), nil, Some(3)]

# Arrays of struct types
struct Point:
    x: i64
    y: i64

val points: [Point] = [Point(x: 0, y: 0)]
```

---

#### `emit_array_literal_pushes` (Lines 1901, 1911)
**Purpose:** Generate code for array literal initialization

**Uncovered Branches:**
- Line 1901: Struct array check
- Line 1911: Nested bracket depth tracking

**Why Uncovered:** No tests with struct arrays or deeply nested array literals

**Test Cases Needed:**
```simple
# Struct arrays
struct Data:
    val: i64

val struct_array = [Data(val: 1), Data(val: 2)]

# Nested array literals
val nested = [[1, 2], [3, 4, 5], [6]]
val deep = [[[1, 2]], [[3]], [[4, 5, 6]]]
```

---

### 4. Method Call Parsing

#### `if` statement parsing (Lines 1093, 1097-1098, 1116, 1244+)
**Purpose:** Parse method arguments with complex nesting

**Uncovered Branches:**
- Lines 1097-1098: Closing paren/bracket and comma at depth 0
- Multi-argument method calls with nested expressions

**Why Uncovered:** String methods only tested with simple arguments

**Test Cases Needed:**
```simple
# String slice with complex args
val s = "hello world"
val sub = s[(1 + 2)..(len(s) - 1)]     # Expressions in slice bounds

# Replace with nested calls
val r = s.replace("l", "L").replace("o", "O")

# Method calls with array subscripts as args
val arr = [0, 5, 10]
val slice = s[arr[0]..arr[2]]
```

---

### 5. Variable Declaration Parsing

#### `parse_var_decl` (Lines 1639, 1697, 1873, 1881-1883)
**Purpose:** Parse variable declarations with type inference

**Uncovered Branches:**
- Line 1639: Space skipping in declarations
- Line 1697: Dot operator in declarations
- Line 1873: Closing bracket in type annotations
- Lines 1881-1883: Text type inference fallback

**Why Uncovered:** Limited variety in variable declaration styles

**Test Cases Needed:**
```simple
# Type inference from string literals
var    s    =    "hello"              # Extra whitespace
val text_var = "test"                 # Text type inference

# Dot operator in declarations (rare)
val x.y = 42                          # If syntax supports this

# Complex type annotations with brackets
val matrix: [[i64]] = [[1, 2], [3, 4]]
val callback: fn(i64) -> i64 = \x: x * 2
```

---

### 6. Control Flow Translation

#### `translate_block` (Lines 1972, 1981, 2029)
**Purpose:** Convert Simple block statements to C++

**Uncovered Branches:**
- Line 1972: Colon at paren depth 0 (match arms, lambda bodies)
- Line 1981: Empty line/path
- Line 2029: Indentation level mismatch

**Why Uncovered:** Missing tests for:
- Match expressions with complex guards
- Lambda expressions in various contexts
- Mixed indentation (though should be rare)

**Test Cases Needed:**
```simple
# Match with complex arms
match value:
    Some(x) if x > 10: process(x)
    Some(x) if x > 5: alternative(x)
    Some(x): default(x)
    nil: ()

# Lambda in various positions
val f = \x: \y: x + y                 # Nested lambdas
val g = (\a: a * 2)(5)                # Immediately invoked
items.filter(\item: item.len() > 0)   # In method call
```

---

### 7. Edge Cases and Safety

#### `load_file` (Line 92)
**Purpose:** Read source file into memory

**Uncovered Branch:** Buffer declaration (unreachable code path)

**Why Uncovered:** Likely dead code or defensive programming

**Action:** Not testable - internal buffer allocation

---

#### `translate_statement` (Line 2606)
**Purpose:** Check if expression is text type

**Uncovered Branch:** Text expression detection

**Why Uncovered:** Limited text type inference in tests

**Test Cases Needed:**
```simple
# Explicit text type checks
val s: text = "hello"
val concat = s + " world"
val trimmed: text = s.trim()
```

---

## Priority Test Cases

### High Priority (Cover 60% of remaining branches)

1. **Negative number literals** - Simple, high impact
   ```simple
   val x = -42
   val y = -3.14
   val arr = [-1, -2, -3]
   ```

2. **Complex string interpolation** - Common feature, multiple branches
   ```simple
   val nested = "{x {y}}"
   val multi = "{a} + {b} + {c}"
   ```

3. **Method calls with complex arguments** - Core functionality
   ```simple
   s[(1+2)..(len(s)-1)]
   s.replace("a", "b").replace("c", "d")
   ```

4. **Struct arrays** - Type system coverage
   ```simple
   struct Point: x: i64; y: i64
   val points = [Point(x:1, y:2), Point(x:3, y:4)]
   ```

### Medium Priority (Cover 30% of remaining)

5. **Nested arrays**
   ```simple
   val arr2d: [[i64]] = [[1,2],[3,4]]
   ```

6. **Optional function returns**
   ```simple
   fn maybe() -> i64?: Some(42)
   if maybe().:
       check(true)
   ```

7. **Match with guards**
   ```simple
   match x:
       Some(v) if v > 10: high(v)
       Some(v): low(v)
   ```

### Low Priority (Cover 10% - edge cases)

8. **Long type names** - Edge case
9. **Mixed indentation** - Should be rare
10. **Text type inference** - Limited real-world impact

---

## Recommended Approach

### Phase 1: Quick Wins (Target: 95% coverage)
Create 5 targeted test files covering high-priority cases above.

### Phase 2: Type System (Target: 98% coverage)
Add comprehensive type system tests for Optional, arrays, structs.

### Phase 3: Parser Edge Cases (Target: 99%+)
Handle rare parsing scenarios and error paths.

### Phase 4: Defensive Code (Target: 100%)
May require code inspection to determine if branches are reachable.

---

## Notes on Unreachable Code

Some uncovered branches may be **defensive programming** that can't be triggered:
- Line 92 (`load_file` buffer): Internal allocation
- Line 504 comment: Documentation marker
- Lines 1981, 2029: Fallback paths for malformed input

These may require:
- Fuzzing with malformed input
- Code inspection to confirm unreachability
- Coverage exemption if truly defensive

---

## Files Referenced
- Source: `/home/ormastes/dev/pub/simple/src/compiler_seed/seed.cpp`
- Coverage: 87.42% branch coverage (301 uncovered branches)
- Test directory: `/home/ormastes/dev/pub/simple/test/unit/compiler_core/branch_coverage_*.spl`
